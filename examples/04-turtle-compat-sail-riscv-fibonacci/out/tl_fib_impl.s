/* SPDX-License-Identifier: NoAssertionLicense */
        .option norvc
        .option norelax
        .text
        .globl  tl_fib
tl_fib:
        addi    a1, zero, 0
        addi    a2, zero, 1
        addi    a3, a0, 0
        beq     a3, zero, . + 8
        jal     zero, . + 12
        addi    a0, a1, 0
        jalr    zero, ra, 0
        add     a4, a1, a2
        addi    a1, a2, 0
        addi    a2, a4, 0
        addi    a3, a3, -1
        beq     a3, zero, . + 8
        jal     zero, . - 20
        addi    a0, a1, 0
        jalr    zero, ra, 0
