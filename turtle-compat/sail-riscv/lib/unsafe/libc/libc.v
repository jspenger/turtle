(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.stdio.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.stdlib.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.sys_random.

#[local] Open Scope tla_scope.

Definition unsafe_libc (e : env) : property state :=
        unsafe_libc_stdio e
                \land unsafe_libc_stdlib e
                \land unsafe_libc_sys_random e.
