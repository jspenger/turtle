/* SPDX-License-Identifier: NoAssertionLicense */
        .option norvc
        .option norelax
        .section        .data
.tl_fmt:
        .asciz  "%lu\n"
        .text
        .globl  main
main:
        addi    a1, zero, 32
        lui     a0, %hi(.tl_fmt)
        addi    a0, a0, %lo(.tl_fmt)
        lui     ra, %hi(printf)
        jalr    ra, ra, %lo(printf)
        addi    a0, zero, 0
        lui     ra, %hi(exit)
        jalr    ra, ra, %lo(exit)
