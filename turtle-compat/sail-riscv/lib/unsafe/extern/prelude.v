(* SPDX-License-Identifier: NoAssertionLicense *)

Require turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require turtle.compat.sail.riscv.lib.unsafe.extern.extern.
Require turtle.compat.sail.riscv.lib.unsafe.extern.glu.

Notation abi_ra :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_ra
        (only parsing).

Notation abi_sp :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_sp
        (only parsing).

Notation abi_a0 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a0
        (only parsing).

Notation abi_a1 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a1
        (only parsing).

Notation abi_a2 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a2
        (only parsing).

Notation abi_a3 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a3
        (only parsing).

Notation abi_a4 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a4
        (only parsing).

Notation abi_a5 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a5
        (only parsing).

Notation abi_a6 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a6
        (only parsing).

Notation abi_a7 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_a7
        (only parsing).

Notation abi_signed_a0 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a0
        (only parsing).

Notation abi_signed_a1 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a1
        (only parsing).

Notation abi_signed_a2 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a2
        (only parsing).

Notation abi_signed_a3 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a3
        (only parsing).

Notation abi_signed_a4 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a4
        (only parsing).

Notation abi_signed_a5 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a5
        (only parsing).

Notation abi_signed_a6 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a6
        (only parsing).

Notation abi_signed_a7 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_a7
        (only parsing).

Notation abi_arg0 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg0
        (only parsing).

Notation abi_arg1 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg1
        (only parsing).

Notation abi_arg2 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg2
        (only parsing).

Notation abi_arg3 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg3
        (only parsing).

Notation abi_arg4 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg4
        (only parsing).

Notation abi_arg5 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg5
        (only parsing).

Notation abi_arg6 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg6
        (only parsing).

Notation abi_arg7 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_arg7
        (only parsing).

Notation abi_signed_arg0 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg0
        (only parsing).

Notation abi_signed_arg1 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg1
        (only parsing).

Notation abi_signed_arg2 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg2
        (only parsing).

Notation abi_signed_arg3 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg3
        (only parsing).

Notation abi_signed_arg4 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg4
        (only parsing).

Notation abi_signed_arg5 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg5
        (only parsing).

Notation abi_signed_arg6 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg6
        (only parsing).

Notation abi_signed_arg7 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_arg7
        (only parsing).

Notation abi_res0 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_res0
        (only parsing).

Notation abi_res1 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_res1
        (only parsing).

Notation abi_signed_res0 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_res0
        (only parsing).

Notation abi_signed_res1 :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_signed_res1
        (only parsing).

Notation abi_precond :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_precond
        (only parsing).

Notation abi_stepcond_preserve_regs :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_stepcond_preserve_regs
        (only parsing).

Notation abi_stepcond_preserve_conf :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_stepcond_preserve_conf
        (only parsing).

Notation abi_stepcond :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_stepcond
        (only parsing).

Notation abi_opt_stepcond_preserve_mem :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_opt_stepcond_preserve_mem
        (only parsing).

Notation abi_opt_stepcond_return :=
        turtle.compat.sail.riscv.lib.unsafe.extern.abi.abi_opt_stepcond_return
        (only parsing).

Notation unsafe_extern :=
        turtle.compat.sail.riscv.lib.unsafe.extern.extern.unsafe_extern
        (only parsing).
