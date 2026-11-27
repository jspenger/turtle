/* SPDX-License-Identifier: NoAssertionLicense */
        .option norvc
        .option norelax
        .section        .data
.tl_fmt:
        .asciz  "%lu\n"
        .text
        .globl  main
main:
        addi    s1, zero, 2
        addi    s2, zero, 4
        add     s1, s1, s1
        addi    a1, s1, 0
        lui     a0, %hi(.tl_fmt)
        addi    a0, a0, %lo(.tl_fmt)
        lui     ra, %hi(printf)
        jalr    ra, ra, %lo(printf)
        addi    s2, s2, -1
        beq     s2, zero, . + 12
        lui     t0, %hi(main + 8)
        jalr    zero, t0, %lo(main + 8)
        addi    a0, zero, 0
        lui     ra, %hi(exit)
        jalr    ra, ra, %lo(exit)
