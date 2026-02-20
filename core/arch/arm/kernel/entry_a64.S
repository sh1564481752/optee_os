/*
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2015-2025, Linaro Limited
 * Copyright (c) 2021-2023, Arm Limited
 */

#include <platform_config.h>

#include <arm.h>
#include <arm64_macros.S>
#include <asm.S>
#include <generated/asm-defines.h>
#include <keep.h>
#include <kernel/asan.h>
#include <kernel/thread.h>
#include <kernel/thread_private.h>
#include <kernel/thread_private_arch.h>
#include <mm/core_mmu.h>
#include <sm/optee_smc.h>
#include <sm/teesmc_opteed.h>
#include <sm/teesmc_opteed_macros.h>

/*
 * 设置SP_EL0和SP_EL1寄存器。SP将被设置为SP_EL0。
 * SP_EL0分配方式：
 *   stack_tmp + (cpu_id + 1) * stack_tmp_stride - STACK_TMP_GUARD
 * SP_EL1分配方式：thread_core_local[cpu_id]
 */
	.macro set_sp
		bl	__get_core_pos
		cmp	x0, #CFG_TEE_CORE_NB_CORE
		/* 不支持的CPU，将其暂停以防止破坏系统 */
		bge	unhandled_cpu
		add	x0, x0, #1
		adr_l	x1, stack_tmp_stride
		ldr	w1, [x1]
		mul	x1, x0, x1

		/* x0 = stack_tmp - STACK_TMP_GUARD */
		adr_l	x2, stack_tmp_rel
		ldr	w0, [x2]
		add	x0, x0, x2

		msr	spsel, #0
		add	sp, x1, x0
		bl	thread_get_core_local
		msr	spsel, #1
		mov	sp, x0
		msr	spsel, #0
	.endm

/*
 * 读取MTE特性寄存器的值并提取相关字段。
 */
	.macro read_feat_mte reg
		mrs	\reg, id_aa64pfr1_el1
		ubfx	\reg, \reg, #ID_AA64PFR1_EL1_MTE_SHIFT, #4
	.endm

/*
 * 读取PAN特性寄存器的值并提取相关字段。
 */
	.macro read_feat_pan reg
		mrs	\reg, id_mmfr3_el1
		ubfx	\reg, \reg, #ID_MMFR3_EL1_PAN_SHIFT, #4
	.endm

/*
 * 设置SCTLR_EL1寄存器的值，启用必要的控制位。
 */
	.macro set_sctlr_el1
		mrs	x0, sctlr_el1
		orr	x0, x0, #SCTLR_I
		orr	x0, x0, #SCTLR_SA
		orr	x0, x0, #SCTLR_SPAN
#if defined(CFG_CORE_RWDATA_NOEXEC)
		orr	x0, x0, #SCTLR_WXN
#endif
#if defined(CFG_SCTLR_ALIGNMENT_CHECK)
		orr	x0, x0, #SCTLR_A
#else
		bic	x0, x0, #SCTLR_A
#endif
#ifdef CFG_MEMTAG
		read_feat_mte x1
		cmp	w1, #1
		b.ls	111f
		orr	x0, x0, #(SCTLR_ATA | SCTLR_ATA0)
		bic	x0, x0, #SCTLR_TCF_MASK
		bic	x0, x0, #SCTLR_TCF0_MASK
111:
#endif
#if defined(CFG_TA_PAUTH) && defined(CFG_TA_BTI)
		orr	x0, x0, #SCTLR_BT0
#endif
#if defined(CFG_CORE_PAUTH) && defined(CFG_CORE_BTI)
		orr	x0, x0, #SCTLR_BT1
#endif
		msr	sctlr_el1, x0
	.endm

/*
 * 初始化每个CPU的内存标签功能。
 */
	.macro init_memtag_per_cpu
		read_feat_mte x0
		cmp	w0, #1
		b.ls	11f

#ifdef CFG_TEE_CORE_DEBUG
		/*
		 * 这与GCR_EL1.RRND = 0一起使用，使得通过irg指令获取的标签是确定性的。
		 */
		mov_imm	x0, 0xcafe00
		msr	rgsr_el1, x0
		/* 避免标签为0x0和0xf */
		mov	x0, #0
#else
		/*
		 * 仍然避免标签为0x0和0xf，因为我们将这些标签用于未明确标记的内容。
		 * 设置GCR_EL1.RRND = 1以允许实现特定的方法生成标签。
		 */
		mov	x0, #GCR_EL1_RRND
#endif
		orr	x0, x0, #1
		orr	x0, x0, #(1 << 15)
		msr	gcr_el1, x0

		/*
		 * 在当前CPU上启用标签检查。
		 *
		 * 依赖于boot_init_memtag()已经清除了TEE核心内存的标签。
		 * 实际上并非如此，带有标签值0b0000的地址将使用未经检查的访问，
		 * 因为TCR_TCMA0。
		 */
		mrs	x0, tcr_el1
		orr	x0, x0, #TCR_TBI0
		orr	x0, x0, #TCR_TCMA0
		msr	tcr_el1, x0

		mrs	x0, sctlr_el1
		orr	x0, x0, #SCTLR_TCF_SYNC
		orr	x0, x0, #SCTLR_TCF0_SYNC
		msr	sctlr_el1, x0

		isb
11:
	.endm

/*
 * 初始化次要CPU的指针认证功能。
 */
	.macro init_pauth_secondary_cpu
		msr	spsel, #1
		ldp	x0, x1, [sp, #THREAD_CORE_LOCAL_KEYS]
		msr	spsel, #0
		write_apiakeyhi x0
		write_apiakeylo x1
		mrs	x0, sctlr_el1
		orr	x0, x0, #SCTLR_ENIA
		msr	sctlr_el1, x0
		isb
	.endm

/*
 * 初始化PAN（特权访问从不）功能。
 */
	.macro init_pan
		read_feat_pan x0
		cmp	x0, #0
		b.eq	1f
		mrs	x0, sctlr_el1
		bic	x0, x0, #SCTLR_SPAN
		msr	sctlr_el1, x0
		write_pan_enable
	1:
	.endm

/*
 * 系统启动入口点。
 * 参数：
 *   x0-x3: 启动参数
 */
FUNC _start , :
	/*
	 * 暂时保存启动参数寄存器，稍后传递给boot_save_args()。
	 */
	mov	x19, x0
	mov	x20, x1
	mov	x21, x2
	mov	x22, x3

	adr	x0, reset_vect_table
	msr	vbar_el1, x0
	isb

#ifdef CFG_PAN
	init_pan
#endif

	set_sctlr_el1
	isb

#ifdef CFG_WITH_PAGER
	/*
	 * 将初始化代码移动到正确的位置，并将哈希值移动到临时安全位置，
	 * 直到堆初始化完成。
	 *
	 * 二进制文件构建如下：
	 * [分页器代码、只读数据和数据]：在正确位置
	 * [初始化代码和只读数据]：应复制到__init_start
	 * [struct boot_embdata + 数据]：应在初始化分页器之前保存，
	 * 第一个uint32_t表示数据长度
	 */
	adr	x0, __init_start	/* 目标地址 */
	adr	x1, __data_end		/* 源地址 */
	adr	x2, __init_end
	sub	x2, x2, x0		/* 初始化长度 */
	ldr	w4, [x1, x2]		/* 哈希等数据的长度 */
	add	x2, x2, x4		/* 初始化和哈希等数据的总长度 */
	/* 向后复制（如memmove），以防重叠 */
	add	x0, x0, x2		/* __init_start + len */
	add	x1, x1, x2		/* __data_end + len */
	adr_l	x3, boot_cached_mem_end
	str	x0, [x3]
	adr	x2, __init_start
copy_init:
	ldp	x3, x4, [x1, #-16]!
	stp	x3, x4, [x0, #-16]!
	cmp	x0, x2
	b.gt	copy_init
#else
	/*
	 * 二进制文件构建如下：
	 * [核心、只读数据和数据]：在正确位置
	 * [struct boot_embdata + 数据]：应移动到__vcore_free_end之前，
	 * 第一个uint32_t表示结构体+数据的长度
	 */
	adr_l	x1, __data_end		/* 源地址 */
	ldr	w2, [x1]		/* struct boot_embdata::total_len */
	/* 目标地址 */
	adr_l	x0, __vcore_free_end
	sub	x0, x0, x2
	/* 向下舍入到页面开始 */
	bic	x0, x0, #(SMALL_PAGE_SIZE - 1)
	adr_l	x3, boot_embdata_ptr
	str	x0, [x3]

	/* 向后复制（如memmove），以防重叠 */
	add	x1, x1, x2
	add	x2, x0, x2
	adr_l	x3, boot_cached_mem_end
	str	x2, [x3]

copy_init:
	ldp	x3, x4, [x1, #-16]!
	stp	x3, x4, [x2, #-16]!
	cmp	x2, x0
	b.gt	copy_init
#endif

	/*
	 * 清除.bss段，此代码显然依赖于链接器保持.bss段起始/结束至少8字节对齐。
	 */
	adr_l	x0, __bss_start
	adr_l	x1, __bss_end
clear_bss:
	str	xzr, [x0], #8
	cmp	x0, x1
	b.lt	clear_bss

#ifdef CFG_NS_VIRTUALIZATION
	/*
	 * 清除.nex_bss段，此代码显然依赖于链接器保持.bss段起始/结束至少8字节对齐。
	 */
	adr_l	x0, __nex_bss_start
	adr_l	x1, __nex_bss_end
clear_nex_bss:
	str	xzr, [x0], #8
	cmp	x0, x1
	b.lt	clear_nex_bss
#endif

#if defined(CFG_CORE_PHYS_RELOCATABLE)
	/*
	 * 保存基础物理地址，此后不会更改。
	 */
	adr_l	x2, core_mmu_tee_load_pa
	adr	x1, _start		/* 加载地址 */
	str	x1, [x2]

	mov_imm	x0, TEE_LOAD_ADDR	/* 编译时加载地址 */
	sub	x0, x1, x0		/* 重定位偏移量 */

	cbz	x0, 1f
	bl	relocate
1:
#endif

#ifdef CFG_CORE_SANITIZE_KADDRESS
	/* 使用无访问权限初始化整个阴影区域 */
	adr_l	x0, __asan_shadow_start	/* 起始地址 */
	adr_l	x1, __asan_shadow_end	/* 限制地址 */
	mov	x2, #ASAN_DATA_RED_ZONE
1:	str	x2, [x0], #8
	cmp	x0, x1
	bls	1b

#if !defined(CFG_DYN_CONFIG)
	/* 标记整个栈区域为OK */
	mov_imm	x2, CFG_ASAN_SHADOW_OFFSET
	adr_l	x0, __nozi_stack_start	/* 起始地址 */
	lsr	x0, x0, #ASAN_BLOCK_SHIFT
	add	x0, x0, x2
	adr_l	x1, __nozi_stack_end	/* 限制地址 */
	lsr	x1, x1, #ASAN_BLOCK_SHIFT
	add	x1, x1, x2
	mov	w2, #0
1:	strb	w2, [x0], #1
	cmp	x0, x1
	bls	1b
#endif
#endif

	/* 设置SP_EL0和SP_EL1，SP将被设置为SP_EL0 */
#if defined(CFG_DYN_CONFIG)
	/*
	 * 将SP_EL0指向映射核心内存末尾的临时栈。
	 * 将SP_EL1指向临时struct thread_core_local，在临时栈之前。
	 */
	adr_l	x0, boot_embdata_ptr
	ldr	x0, [x0]
	sub	x1, x0, #THREAD_BOOT_INIT_TMP_ALLOC

	/* 清除分配的struct thread_core_local */
	add	x2, x1, #THREAD_CORE_LOCAL_SIZE
1:	stp	xzr, xzr, [x2, #-16]!
	cmp	x2, x1
	bgt	1b

	mov	x2, #THREAD_ID_INVALID
	str	x2, [x1, #THREAD_CORE_LOCAL_CURR_THREAD]
	mov	w2, #THREAD_CLF_TMP
	str	w2, [x1, #THREAD_CORE_LOCAL_FLAGS]
	sub	x0, x0, #(__STACK_CANARY_SIZE / 2)
	str	x0, [x1, #THREAD_CORE_LOCAL_TMP_STACK_VA_END]
	sub	x2, x0, #(THREAD_BOOT_INIT_TMP_ALLOC / 2)
	str	x2, [x1, #THREAD_CORE_LOCAL_ABT_STACK_VA_END]
	msr	spsel, #1
	mov	sp, x1
	msr	spsel, #0
	mov	sp, x0
	/*
	 * 记录单个核心，稍后在安全世界启动完成前更改。
	 */
	adr_l	x2, thread_core_local
	str	x1, [x2]
	adr_l	x2, thread_core_count
	mov	x0, #1
	str	x0, [x2]
#else
	set_sp

	/* 为早期启动初始化thread_core_local[current_cpu_id] */
	bl	thread_get_abt_stack
	mov	x1, sp
	msr	spsel, #1
	str	x1, [sp, #THREAD_CORE_LOCAL_TMP_STACK_VA_END]
	str	x0, [sp, #THREAD_CORE_LOCAL_ABT_STACK_VA_END]
	mov	x0, #THREAD_ID_INVALID
	str	x0, [sp, #THREAD_CORE_LOCAL_CURR_THREAD]
	mov	w0, #THREAD_CLF_TMP
	str	w0, [sp, #THREAD_CORE_LOCAL_FLAGS]
	msr	spsel, #0
#endif

	/* 现在可以接收异常，启用中止 */
	msr	daifclr, #DAIFBIT_ABT

	/*
	 * 使缓存在初始化期间使用的所有内存无效，以避免在缓存开启时出现意外情况。
	 * 我们不得使OP-TEE未使用的内存无效，因为我们可能会使ARM可信固件等使用的条目无效。
	 */
	adr_l	x0, __text_start
	adr_l	x1, boot_cached_mem_end
	ldr	x1, [x1]
	sub	x1, x1, x0
	bl	dcache_cleaninv_range

	/* 启用控制台 */
	bl	console_init

	mov	x0, x19
	mov	x1, x20
	mov	x2, x21
	mov	x3, x22
	mov	x4, xzr
	bl	boot_save_args

#ifdef CFG_WITH_PAGER
	adr_l	x0, __init_end	/* 指向boot_embdata */
	ldr	w1, [x0]	/* struct boot_embdata::total_len */
	add	x0, x0, x1
	add	x0, x0, #0xfff	/* 向上舍入 */
	bic	x0, x0, #0xfff  /* 到下一页 */
	mov_imm x1, (TEE_RAM_PH_SIZE + TEE_RAM_START)
	mov	x2, x1
#else
	adr_l	x0, __vcore_free_start
	adr_l	x1, boot_embdata_ptr
	ldr	x1, [x1]
#ifdef CFG_DYN_CONFIG
	sub	x1, x1, #THREAD_BOOT_INIT_TMP_ALLOC
#endif
	adr_l	x2, __vcore_free_end;
#endif
	bl	boot_mem_init

#ifdef CFG_MEMTAG
	/*
	 * 如果FEAT_MTE2可用，则初始化memtag回调。
	 * 然后清除OP-TEE核心内存的标签，使其安全地启用MEMTAG。
	 */
	bl	boot_init_memtag
#endif

#ifdef CFG_CORE_ASLR
	bl	get_aslr_seed
#ifdef CFG_CORE_ASLR_SEED
	mov_imm	x0, CFG_CORE_ASLR_SEED
#endif
#else
	mov	x0, #0
#endif

	adr	x1, boot_mmu_config
	bl	core_init_mmu_map

#ifdef CFG_CORE_ASLR
	/*
	 * 再次处理重定位信息，更新虚拟映射偏移量。
	 * 我们现在这样做是因为MMU尚未启用，某些内存将成为写保护。
	 */
	ldr	x0, boot_mmu_config + CORE_MMU_CONFIG_MAP_OFFSET
	cbz	x0, 1f
	/*
	 * 使用加载偏移量更新boot_cached_mem_end地址，因为它是在重定位之前计算的。
	 */
	adr_l	x5, boot_cached_mem_end
	ldr	x6, [x5]
	add	x6, x6, x0
	str	x6, [x5]
	adr	x1, _start		/* 加载地址 */
	bl	relocate
1:
#endif

	bl	__get_core_pos
	bl	enable_mmu
#ifdef CFG_CORE_ASLR
#if defined(CFG_DYN_CONFIG)
	/*
	 * thread_core_local仅持有一个核心且thread_core_count为1，
	 * 因此SP_EL1指向更新后的thread_core_local指针。
	 */
	msr	spsel, #1
	mov	x1, sp
	msr	spsel, #0
	adr_l	x0, thread_core_local
	str	x1, [x0]
#endif

	/*
	 * 更新记录的end_va。这必须在调用C代码之前完成，
	 * 以确保栈指针与我们在thread_core_local[]中的记录匹配。
	 */
	adr_l	x0, boot_mmu_config
	ldr	x0, [x0, #CORE_MMU_CONFIG_MAP_OFFSET]
	msr	spsel, #1
	ldr	x1, [sp, #THREAD_CORE_LOCAL_TMP_STACK_VA_END]
	add	x1, x1, x0
	str	x1, [sp, #THREAD_CORE_LOCAL_TMP_STACK_VA_END]
	ldr	x1, [sp, #THREAD_CORE_LOCAL_ABT_STACK_VA_END]
	add	x1, x1, x0
	str	x1, [sp, #THREAD_CORE_LOCAL_ABT_STACK_VA_END]
	msr	spsel, #0

	/* 更新通过boot_mem_add_reloc()记录的重定位 */
	adr_l	x0, boot_mmu_config
	ldr	x0, [x0, #CORE_MMU_CONFIG_MAP_OFFSET]
	bl	boot_mem_relocate
	/*
	 * 重新初始化控制台，因为register_serial_console()先前注册了PA，
	 * 而使用ASLR时VA与PA不同。
	 */
	bl	console_init
#endif

#ifdef CFG_MEMTAG
	bl	boot_clear_memtag
#endif

#ifdef CFG_NS_VIRTUALIZATION
	/*
	 * 为每个分区初始化分区表为default_partition，
	 * 该分区现已重定位到不同的VA。
	 */
	bl	core_mmu_set_default_prtn_tbl
#endif

	bl	boot_init_primary_early

#ifdef CFG_MEMTAG
	init_memtag_per_cpu
#endif
	bl	boot_init_primary_late

#if defined(CFG_DYN_CONFIG)
	bl	__get_core_pos

	/*
	 * 切换到新的thread_core_local和thread_core_count，
	 * 并将新thread_core_local的指针保留在x1中。
	 */
	adr_l	x1, __thread_core_count_new
	ldr	x1, [x1]
	adr_l 	x2, thread_core_count;
	str	x1, [x2]
	adr_l	x1, __thread_core_local_new
	ldr	x1, [x1]
	adr_l	x2, thread_core_local
	str	x1, [x2]

	/*
	 * 更新SP_EL0以使用新的tmp栈，并更新SP_EL1以指向新的thread_core_local，
	 * 并清除thread_core_local[0].stackcheck_recursion，因为栈指针与记录的信息匹配。
	 */
	mov	x2, #THREAD_CORE_LOCAL_SIZE
	/* x3 = x2 * x0 + x1 */
	madd	x3, x2, x0, x1
	ldr	x0, [x3, #THREAD_CORE_LOCAL_TMP_STACK_VA_END]
	mov	sp, x0
	msr	spsel, #1
	mov	sp, x3
	msr	spsel, #0
#endif

#ifndef CFG_NS_VIRTUALIZATION
	mov	x23, sp
	adr_l	x0, threads
	ldr	x0, [x0]
	ldr	x0, [x0, #THREAD_CTX_STACK_VA_END]
	mov	sp, x0
	bl	thread_get_core_local
	mov	x24, x0
	str	wzr, [x24, #THREAD_CORE_LOCAL_FLAGS]
#endif
	bl	boot_init_primary_runtime
#ifdef CFG_CORE_PAUTH
	adr_l	x0, threads
	ldr	x0, [x0]
	ldp	x1, x2, [x0, #THREAD_CTX_KEYS]
	write_apiakeyhi x1
	write_apiakeylo x2
	mrs	x0, sctlr_el1
	orr	x0, x0, #SCTLR_ENIA
	msr	sctlr_el1, x0
	isb
#endif
	bl	boot_init_primary_final

#ifndef CFG_NS_VIRTUALIZATION
	mov	x0, #THREAD_CLF_TMP
	str     w0, [x24, #THREAD_CORE_LOCAL_FLAGS]
	mov	sp, x23
#ifdef CFG_CORE_PAUTH
	ldp	x0, x1, [x24, #THREAD_CORE_LOCAL_KEYS]
	write_apiakeyhi x0
	write_apiakeylo x1
	isb
#endif
#endif

#ifdef _CFG_CORE_STACK_PROTECTOR
	/* 更新栈保护值 */
	sub	sp, sp, #0x10
	mov	x0, sp
	mov	x1, #1
	mov	x2, #0x8
	bl	plat_get_random_stack_canaries
	ldr	x0, [sp]
	adr_l	x5, __stack_chk_guard
	str	x0, [x5]
	add	sp, sp, #0x10
#endif

	/*
	 * 如果我们在二级CPU启用其D-cache之前访问了它们将使用的内存，
	 * 则在退出到正常世界之前清理并使D-cache无效。
	 */
	adr_l	x0, __text_start
	adr_l	x1, boot_cached_mem_end
	ldr	x1, [x1]
	sub	x1, x1, x0
	bl	dcache_cleaninv_range

	/*
	 * 现在清除当前线程ID，以便在线程下次进入时可以重用。
	 * 匹配boot.c中的thread_init_boot_thread。
	 */
#ifndef CFG_NS_VIRTUALIZATION
	bl 	thread_clr_boot_thread
#endif

#ifdef CFG_CORE_FFA
	adr	x0, cpu_on_handler
	/*
	 * 补偿虚拟映射偏移量，因为cpu_on_handler()在MMU关闭时被调用。
	 */
	ldr	x1, boot_mmu_config + CORE_MMU_CONFIG_MAP_OFFSET
	sub	x0, x0, x1
	bl	thread_spmc_register_secondary_ep
	b	thread_ffa_msg_wait
#else
	/*
	 * 传递从main_init返回的向量地址。补偿虚拟映射偏移量，
	 * 因为cpu_on_handler()在MMU关闭时被调用。
	 */
	ldr	x0, boot_mmu_config + CORE_MMU_CONFIG_MAP_OFFSET
	adr	x1, thread_vector_table
	sub	x1, x1, x0
	mov	x0, #TEESMC_OPTEED_RETURN_ENTRY_DONE
	smc	#0
	/* SMC不应返回 */
	panic_at_smc_return
#endif
END_FUNC _start
DECLARE_KEEP_INIT _start

#ifndef CFG_WITH_PAGER
	.section .identity_map.data
	.balign	8
LOCAL_DATA boot_embdata_ptr , :
	.skip	8
END_DATA boot_embdata_ptr
#endif

#if defined(CFG_CORE_ASLR) || defined(CFG_CORE_PHYS_RELOCATABLE)
LOCAL_FUNC relocate , :
	/*
	 * x0保存重定位偏移量
	 * x1保存加载地址
	 */
#ifdef CFG_WITH_PAGER
	adr_l	x6, __init_end
#else
	adr_l	x6, boot_embdata_ptr
	ldr	x6, [x6]
#endif
	ldp	w2, w3, [x6, #BOOT_EMBDATA_RELOC_OFFSET]

	add	x2, x2, x6	/* 重定位开始 */
	add	x3, x3, x2	/* 重定位结束 */

	/*
	 * 重定位不是格式化的Rela64，而是由scripts/gen_tee_bin.py中的get_reloc_bin()
	 * 创建的压缩格式。
	 *
	 * 所有R_AARCH64_RELATIVE重定位都被转换为从TEE_LOAD_ADDR开始的32位偏移列表。
	 * 在每个地址处，指向的64位值增加了加载偏移量。
	 */

#ifdef CFG_WITH_PAGER
	/*
	 * 启用分页器时，我们只能重定位分页器和初始化部分，
	 * 其余部分必须在页面填充时完成。
	 */
	sub	x6, x6, x1
#endif

	b	2f
	/* 循环遍历重定位地址并处理所有条目 */
1:	ldr	w4, [x2], #4
#ifdef CFG_WITH_PAGER
	/* 跳过太大的地址 */
	cmp	x4, x6
	b.ge	2f
#endif
	add	x4, x4, x1
	ldr	x5, [x4]
	add	x5, x5, x0
	str	x5, [x4]

2:	cmp	x2, x3
	b.ne	1b

	ret
END_FUNC relocate
#endif

/*
 * void enable_mmu(unsigned long core_pos);
 *
 * 此函数依赖于在身份映射中映射，其中物理地址和虚拟地址相同。
 * 启用MMU后，指令指针将更新为以新偏移量执行。
 * 栈指针和返回地址也会更新。
 */
LOCAL_FUNC enable_mmu , : , .identity_map
	adr	x1, boot_mmu_config
	load_xregs x1, 0, 2, 6
	/*
	 * x0 = core_pos
	 * x2 = tcr_el1
	 * x3 = mair_el1
	 * x4 = ttbr0_el1_base
	 * x5 = ttbr0_core_offset
	 * x6 = load_offset
	 */
	msr	tcr_el1, x2
	msr	mair_el1, x3

	/*
	 * ttbr0_el1 = ttbr0_el1_base + ttbr0_core_offset * core_pos
	 */
	madd	x1, x5, x0, x4
	msr	ttbr0_el1, x1
	msr	ttbr1_el1, xzr
	isb

	/* 使TLB无效 */
	tlbi	vmalle1

	/*
	 * 确保翻译表写入已刷新到内存，并且TLB无效已完成。
	 */
	dsb	sy
	isb

	/* 启用MMU */
	mrs	x1, sctlr_el1
	orr	x1, x1, #SCTLR_M
	msr	sctlr_el1, x1
	isb

	/* 更新vbar */
	mrs	x1, vbar_el1
	add	x1, x1, x6
	msr	vbar_el1, x1
	isb

	/* 使指令缓存和分支预测器无效 */
	ic	iallu
	isb

	/* 启用I和D缓存 */
	mrs	x1, sctlr_el1
	orr	x1, x1, #SCTLR_I
	orr	x1, x1, #SCTLR_C
	msr	sctlr_el1, x1
	isb

	/* 调整栈指针和返回地址 */
	msr	spsel, #1
	add	sp, sp, x6
	msr	spsel, #0
	add	sp, sp, x6
	add	x30, x30, x6

	ret
END_FUNC enable_mmu

	.section .identity_map.data
	.balign	8
DATA boot_mmu_config , : /* struct core_mmu_config */
	.skip	CORE_MMU_CONFIG_SIZE
END_DATA boot_mmu_config

FUNC cpu_on_handler , :
	mov	x19, x0
	mov	x20, x1
	mov	x21, x30

	adr	x0, reset_vect_table
	msr	vbar_el1, x0
	isb

	set_sctlr_el1
	isb

#ifdef CFG_PAN
	init_pan
#endif

	/* 现在可以接收异常，启用中止 */
	msr	daifclr, #DAIFBIT_ABT

	bl	__get_core_pos
	bl	enable_mmu

#if defined(CFG_DYN_CONFIG)
	/*
	 * 更新SP_EL0以使用新的tmp栈，并更新SP_EL1以指向新的thread_core_local。
	 */
	bl	__get_core_pos
	adr_l	x1, thread_core_local
	ldr	x1, [x1]
	mov	x2, #THREAD_CORE_LOCAL_SIZE
	/* x3 = x2 * x0 + x1 */
	madd	x3, x2, x0, x1
	ldr	x0, [x3, #THREAD_CORE_LOCAL_TMP_STACK_VA_END]
	mov	sp, x0
	msr	spsel, #1
	mov	sp, x3
	msr	spsel, #0
#else
	/* 设置SP_EL0和SP_EL1，SP将被设置为SP_EL0 */
	set_sp
#endif

#ifdef CFG_MEMTAG
	init_memtag_per_cpu
#endif
#ifdef CFG_CORE_PAUTH
	init_pauth_secondary_cpu
#endif

	mov	x0, x19
	mov	x1, x20
#ifdef CFG_CORE_FFA
	bl	boot_cpu_on_handler
	b	thread_ffa_msg_wait
#else
	mov	x30, x21
	b	boot_cpu_on_handler
#endif
END_FUNC cpu_on_handler
DECLARE_KEEP_PAGER cpu_on_handler

LOCAL_FUNC unhandled_cpu , :
	wfi
	b	unhandled_cpu
END_FUNC unhandled_cpu

#if !defined(CFG_DYN_CONFIG)
LOCAL_DATA stack_tmp_rel , :
	.word	stack_tmp - stack_tmp_rel - STACK_TMP_GUARD
END_DATA stack_tmp_rel
#endif

	/*
	 * 此宏验证给定向量不超过架构限制的32条指令。
	 * 应立即放置在向量最后一条指令之后。
	 * 它以向量条目作为参数。
	 */
	.macro check_vector_size since
	  .if (. - \since) > (32 * 4)
	    .error "Vector exceeds 32 instructions"
	  .endif
	.endm

	.section .identity_map, "ax", %progbits
	.align	11
LOCAL_FUNC reset_vect_table , :, .identity_map, , nobti
	/* -----------------------------------------------------
	 * 当前EL使用SP0 : 0x0 - 0x180
	 * -----------------------------------------------------
	 */
SynchronousExceptionSP0:
	b	SynchronousExceptionSP0
	check_vector_size SynchronousExceptionSP0

	.align	7
IrqSP0:
	b	IrqSP0
	check_vector_size IrqSP0

	.align	7
FiqSP0:
	b	FiqSP0
	check_vector_size FiqSP0

	.align	7
SErrorSP0:
	b	SErrorSP0
	check_vector_size SErrorSP0

	/* -----------------------------------------------------
	 * 当前EL使用SPx: 0x200 - 0x380
	 * -----------------------------------------------------
	 */
	.align	7
SynchronousExceptionSPx:
	b	SynchronousExceptionSPx
	check_vector_size SynchronousExceptionSPx

	.align	7
IrqSPx:
	b	IrqSPx
	check_vector_size IrqSPx

	.align	7
FiqSPx:
	b	FiqSPx
	check_vector_size FiqSPx

	.align	7
SErrorSPx:
	b	SErrorSPx
	check_vector_size SErrorSPx

	/* -----------------------------------------------------
	 * 下层EL使用AArch64 : 0x400 - 0x580
	 * -----------------------------------------------------
	 */
	.align	7
SynchronousExceptionA64:
	b	SynchronousExceptionA64
	check_vector_size SynchronousExceptionA64

	.align	7
IrqA64:
	b	IrqA64
	check_vector_size IrqA64

	.align	7
FiqA64:
	b	FiqA64
	check_vector_size FiqA64

	.align	7
SErrorA64:
	b   	SErrorA64
	check_vector_size SErrorA64

	/* -----------------------------------------------------
	 * 下层EL使用AArch32 : 0x0 - 0x180
	 * -----------------------------------------------------
	 */
	.align	7
SynchronousExceptionA32:
	b	SynchronousExceptionA32
	check_vector_size SynchronousExceptionA32

	.align	7
IrqA32:
	b	IrqA32
	check_vector_size IrqA32

	.align	7
FiqA32:
	b	FiqA32
	check_vector_size FiqA32

	.align	7
SErrorA32:
	b	SErrorA32
	check_vector_size SErrorA32

END_FUNC reset_vect_table

BTI(emit_aarch64_feature_1_and     GNU_PROPERTY_AARCH64_FEATURE_1_BTI)