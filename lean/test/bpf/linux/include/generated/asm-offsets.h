#ifndef __ASM_OFFSETS_H__
#define __ASM_OFFSETS_H__
/*
 * DO NOT MODIFY.
 *
 * This file was generated by Kbuild
 */

#define TASK_THREAD_RA 1424 /* offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_SP 1428 /* offsetof(struct task_struct, thread.sp) */
#define TASK_THREAD_S0 1432 /* offsetof(struct task_struct, thread.s[0]) */
#define TASK_THREAD_S1 1436 /* offsetof(struct task_struct, thread.s[1]) */
#define TASK_THREAD_S2 1440 /* offsetof(struct task_struct, thread.s[2]) */
#define TASK_THREAD_S3 1444 /* offsetof(struct task_struct, thread.s[3]) */
#define TASK_THREAD_S4 1448 /* offsetof(struct task_struct, thread.s[4]) */
#define TASK_THREAD_S5 1452 /* offsetof(struct task_struct, thread.s[5]) */
#define TASK_THREAD_S6 1456 /* offsetof(struct task_struct, thread.s[6]) */
#define TASK_THREAD_S7 1460 /* offsetof(struct task_struct, thread.s[7]) */
#define TASK_THREAD_S8 1464 /* offsetof(struct task_struct, thread.s[8]) */
#define TASK_THREAD_S9 1468 /* offsetof(struct task_struct, thread.s[9]) */
#define TASK_THREAD_S10 1472 /* offsetof(struct task_struct, thread.s[10]) */
#define TASK_THREAD_S11 1476 /* offsetof(struct task_struct, thread.s[11]) */
#define TASK_TI_FLAGS 0 /* offsetof(struct task_struct, thread_info.flags) */
#define TASK_TI_PREEMPT_COUNT 4 /* offsetof(struct task_struct, thread_info.preempt_count) */
#define TASK_TI_KERNEL_SP 8 /* offsetof(struct task_struct, thread_info.kernel_sp) */
#define TASK_TI_USER_SP 12 /* offsetof(struct task_struct, thread_info.user_sp) */
#define TASK_TI_CPU 16 /* offsetof(struct task_struct, thread_info.cpu) */
#define TASK_THREAD_F0 1480 /* offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F1 1488 /* offsetof(struct task_struct, thread.fstate.f[1]) */
#define TASK_THREAD_F2 1496 /* offsetof(struct task_struct, thread.fstate.f[2]) */
#define TASK_THREAD_F3 1504 /* offsetof(struct task_struct, thread.fstate.f[3]) */
#define TASK_THREAD_F4 1512 /* offsetof(struct task_struct, thread.fstate.f[4]) */
#define TASK_THREAD_F5 1520 /* offsetof(struct task_struct, thread.fstate.f[5]) */
#define TASK_THREAD_F6 1528 /* offsetof(struct task_struct, thread.fstate.f[6]) */
#define TASK_THREAD_F7 1536 /* offsetof(struct task_struct, thread.fstate.f[7]) */
#define TASK_THREAD_F8 1544 /* offsetof(struct task_struct, thread.fstate.f[8]) */
#define TASK_THREAD_F9 1552 /* offsetof(struct task_struct, thread.fstate.f[9]) */
#define TASK_THREAD_F10 1560 /* offsetof(struct task_struct, thread.fstate.f[10]) */
#define TASK_THREAD_F11 1568 /* offsetof(struct task_struct, thread.fstate.f[11]) */
#define TASK_THREAD_F12 1576 /* offsetof(struct task_struct, thread.fstate.f[12]) */
#define TASK_THREAD_F13 1584 /* offsetof(struct task_struct, thread.fstate.f[13]) */
#define TASK_THREAD_F14 1592 /* offsetof(struct task_struct, thread.fstate.f[14]) */
#define TASK_THREAD_F15 1600 /* offsetof(struct task_struct, thread.fstate.f[15]) */
#define TASK_THREAD_F16 1608 /* offsetof(struct task_struct, thread.fstate.f[16]) */
#define TASK_THREAD_F17 1616 /* offsetof(struct task_struct, thread.fstate.f[17]) */
#define TASK_THREAD_F18 1624 /* offsetof(struct task_struct, thread.fstate.f[18]) */
#define TASK_THREAD_F19 1632 /* offsetof(struct task_struct, thread.fstate.f[19]) */
#define TASK_THREAD_F20 1640 /* offsetof(struct task_struct, thread.fstate.f[20]) */
#define TASK_THREAD_F21 1648 /* offsetof(struct task_struct, thread.fstate.f[21]) */
#define TASK_THREAD_F22 1656 /* offsetof(struct task_struct, thread.fstate.f[22]) */
#define TASK_THREAD_F23 1664 /* offsetof(struct task_struct, thread.fstate.f[23]) */
#define TASK_THREAD_F24 1672 /* offsetof(struct task_struct, thread.fstate.f[24]) */
#define TASK_THREAD_F25 1680 /* offsetof(struct task_struct, thread.fstate.f[25]) */
#define TASK_THREAD_F26 1688 /* offsetof(struct task_struct, thread.fstate.f[26]) */
#define TASK_THREAD_F27 1696 /* offsetof(struct task_struct, thread.fstate.f[27]) */
#define TASK_THREAD_F28 1704 /* offsetof(struct task_struct, thread.fstate.f[28]) */
#define TASK_THREAD_F29 1712 /* offsetof(struct task_struct, thread.fstate.f[29]) */
#define TASK_THREAD_F30 1720 /* offsetof(struct task_struct, thread.fstate.f[30]) */
#define TASK_THREAD_F31 1728 /* offsetof(struct task_struct, thread.fstate.f[31]) */
#define TASK_THREAD_FCSR 1736 /* offsetof(struct task_struct, thread.fstate.fcsr) */
#define TSK_STACK_CANARY 760 /* offsetof(struct task_struct, stack_canary) */
#define PT_SIZE 144 /* sizeof(struct pt_regs) */
#define PT_EPC 0 /* offsetof(struct pt_regs, epc) */
#define PT_RA 4 /* offsetof(struct pt_regs, ra) */
#define PT_FP 32 /* offsetof(struct pt_regs, s0) */
#define PT_S0 32 /* offsetof(struct pt_regs, s0) */
#define PT_S1 36 /* offsetof(struct pt_regs, s1) */
#define PT_S2 72 /* offsetof(struct pt_regs, s2) */
#define PT_S3 76 /* offsetof(struct pt_regs, s3) */
#define PT_S4 80 /* offsetof(struct pt_regs, s4) */
#define PT_S5 84 /* offsetof(struct pt_regs, s5) */
#define PT_S6 88 /* offsetof(struct pt_regs, s6) */
#define PT_S7 92 /* offsetof(struct pt_regs, s7) */
#define PT_S8 96 /* offsetof(struct pt_regs, s8) */
#define PT_S9 100 /* offsetof(struct pt_regs, s9) */
#define PT_S10 104 /* offsetof(struct pt_regs, s10) */
#define PT_S11 108 /* offsetof(struct pt_regs, s11) */
#define PT_SP 8 /* offsetof(struct pt_regs, sp) */
#define PT_TP 16 /* offsetof(struct pt_regs, tp) */
#define PT_A0 40 /* offsetof(struct pt_regs, a0) */
#define PT_A1 44 /* offsetof(struct pt_regs, a1) */
#define PT_A2 48 /* offsetof(struct pt_regs, a2) */
#define PT_A3 52 /* offsetof(struct pt_regs, a3) */
#define PT_A4 56 /* offsetof(struct pt_regs, a4) */
#define PT_A5 60 /* offsetof(struct pt_regs, a5) */
#define PT_A6 64 /* offsetof(struct pt_regs, a6) */
#define PT_A7 68 /* offsetof(struct pt_regs, a7) */
#define PT_T0 20 /* offsetof(struct pt_regs, t0) */
#define PT_T1 24 /* offsetof(struct pt_regs, t1) */
#define PT_T2 28 /* offsetof(struct pt_regs, t2) */
#define PT_T3 112 /* offsetof(struct pt_regs, t3) */
#define PT_T4 116 /* offsetof(struct pt_regs, t4) */
#define PT_T5 120 /* offsetof(struct pt_regs, t5) */
#define PT_T6 124 /* offsetof(struct pt_regs, t6) */
#define PT_GP 12 /* offsetof(struct pt_regs, gp) */
#define PT_ORIG_A0 140 /* offsetof(struct pt_regs, orig_a0) */
#define PT_STATUS 128 /* offsetof(struct pt_regs, status) */
#define PT_BADADDR 132 /* offsetof(struct pt_regs, badaddr) */
#define PT_CAUSE 136 /* offsetof(struct pt_regs, cause) */
#define TASK_THREAD_RA_RA 0 /* offsetof(struct task_struct, thread.ra) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_SP_RA 4 /* offsetof(struct task_struct, thread.sp) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S0_RA 8 /* offsetof(struct task_struct, thread.s[0]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S1_RA 12 /* offsetof(struct task_struct, thread.s[1]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S2_RA 16 /* offsetof(struct task_struct, thread.s[2]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S3_RA 20 /* offsetof(struct task_struct, thread.s[3]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S4_RA 24 /* offsetof(struct task_struct, thread.s[4]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S5_RA 28 /* offsetof(struct task_struct, thread.s[5]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S6_RA 32 /* offsetof(struct task_struct, thread.s[6]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S7_RA 36 /* offsetof(struct task_struct, thread.s[7]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S8_RA 40 /* offsetof(struct task_struct, thread.s[8]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S9_RA 44 /* offsetof(struct task_struct, thread.s[9]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S10_RA 48 /* offsetof(struct task_struct, thread.s[10]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_S11_RA 52 /* offsetof(struct task_struct, thread.s[11]) - offsetof(struct task_struct, thread.ra) */
#define TASK_THREAD_F0_F0 0 /* offsetof(struct task_struct, thread.fstate.f[0]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F1_F0 8 /* offsetof(struct task_struct, thread.fstate.f[1]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F2_F0 16 /* offsetof(struct task_struct, thread.fstate.f[2]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F3_F0 24 /* offsetof(struct task_struct, thread.fstate.f[3]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F4_F0 32 /* offsetof(struct task_struct, thread.fstate.f[4]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F5_F0 40 /* offsetof(struct task_struct, thread.fstate.f[5]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F6_F0 48 /* offsetof(struct task_struct, thread.fstate.f[6]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F7_F0 56 /* offsetof(struct task_struct, thread.fstate.f[7]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F8_F0 64 /* offsetof(struct task_struct, thread.fstate.f[8]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F9_F0 72 /* offsetof(struct task_struct, thread.fstate.f[9]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F10_F0 80 /* offsetof(struct task_struct, thread.fstate.f[10]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F11_F0 88 /* offsetof(struct task_struct, thread.fstate.f[11]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F12_F0 96 /* offsetof(struct task_struct, thread.fstate.f[12]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F13_F0 104 /* offsetof(struct task_struct, thread.fstate.f[13]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F14_F0 112 /* offsetof(struct task_struct, thread.fstate.f[14]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F15_F0 120 /* offsetof(struct task_struct, thread.fstate.f[15]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F16_F0 128 /* offsetof(struct task_struct, thread.fstate.f[16]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F17_F0 136 /* offsetof(struct task_struct, thread.fstate.f[17]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F18_F0 144 /* offsetof(struct task_struct, thread.fstate.f[18]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F19_F0 152 /* offsetof(struct task_struct, thread.fstate.f[19]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F20_F0 160 /* offsetof(struct task_struct, thread.fstate.f[20]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F21_F0 168 /* offsetof(struct task_struct, thread.fstate.f[21]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F22_F0 176 /* offsetof(struct task_struct, thread.fstate.f[22]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F23_F0 184 /* offsetof(struct task_struct, thread.fstate.f[23]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F24_F0 192 /* offsetof(struct task_struct, thread.fstate.f[24]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F25_F0 200 /* offsetof(struct task_struct, thread.fstate.f[25]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F26_F0 208 /* offsetof(struct task_struct, thread.fstate.f[26]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F27_F0 216 /* offsetof(struct task_struct, thread.fstate.f[27]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F28_F0 224 /* offsetof(struct task_struct, thread.fstate.f[28]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F29_F0 232 /* offsetof(struct task_struct, thread.fstate.f[29]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F30_F0 240 /* offsetof(struct task_struct, thread.fstate.f[30]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_F31_F0 248 /* offsetof(struct task_struct, thread.fstate.f[31]) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define TASK_THREAD_FCSR_F0 256 /* offsetof(struct task_struct, thread.fstate.fcsr) - offsetof(struct task_struct, thread.fstate.f[0]) */
#define PT_SIZE_ON_STACK 144 /* ALIGN(sizeof(struct pt_regs), STACK_ALIGN) */

#endif
