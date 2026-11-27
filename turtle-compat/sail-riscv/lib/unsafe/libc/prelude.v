(* SPDX-License-Identifier: NoAssertionLicense *)

Require turtle.compat.sail.riscv.lib.unsafe.libc.libc.
Require turtle.compat.sail.riscv.lib.unsafe.libc.stdio.
Require turtle.compat.sail.riscv.lib.unsafe.libc.stdlib.
Require turtle.compat.sail.riscv.lib.unsafe.libc.sys_random.

Notation unsafe_libc :=
        turtle.compat.sail.riscv.lib.unsafe.libc.libc.unsafe_libc
        (only parsing).

Notation unsafe_libc_stdio :=
        turtle.compat.sail.riscv.lib.unsafe.libc.stdio.unsafe_libc_stdio
        (only parsing).

Notation unsafe_libc_stdlib :=
        turtle.compat.sail.riscv.lib.unsafe.libc.stdlib.unsafe_libc_stdlib
        (only parsing).

Notation unsafe_libc_sys_random :=
        turtle.compat.sail.riscv.lib.unsafe.libc.sys_random.unsafe_libc_sys_random
        (only parsing).
