/* SPDX-License-Identifier: NoAssertionLicense */
        .option norvc
        .option norelax
        .section        .data
.tl_fmt:
        .asciz  "%lu\n"
        .text
        .globl  main
main:
        addi    sp, sp, -16
        addi    a0, sp, 0
        addi    a1, zero, 8
        addi    a2, zero, 0
        lui     ra, %hi(getrandom)
        jalr    ra, ra, %lo(getrandom)
        addi    t0, zero, 8
        beq     a0, t0, . + 12
        lui     t0, %hi(main + 116)
        jalr    zero, t0, %lo(main + 116)
        lw      a0, 0(sp)
        andi    a0, a0, 31
        addi    s1, a0, 0
        lui     ra, %hi(tl_fib)
        jalr    ra, ra, %lo(tl_fib)
        addi    s2, a0, 0
        addi    a1, s1, 0
        lui     a0, %hi(.tl_fmt)
        addi    a0, a0, %lo(.tl_fmt)
        lui     ra, %hi(printf)
        jalr    ra, ra, %lo(printf)
        addi    a1, s2, 0
        lui     a0, %hi(.tl_fmt)
        addi    a0, a0, %lo(.tl_fmt)
        lui     ra, %hi(printf)
        jalr    ra, ra, %lo(printf)
        addi    a0, zero, 0
        lui     ra, %hi(exit)
        jalr    ra, ra, %lo(exit)
        addi    a0, zero, 1
        lui     ra, %hi(exit)
        jalr    ra, ra, %lo(exit)
