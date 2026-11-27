(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.conf_default.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Definition stack_ok : property state :=
        \lift1 (fun s =>
                conf_stack_addr <= abi_sp s
                        /\ abi_sp s <= conf_stack_addr + conf_stack_size).

Theorem thm_6_stack_ok :
        valid (impl_linked
                \impl [] stack_ok).
Proof.
(* TODO *) Admitted.
