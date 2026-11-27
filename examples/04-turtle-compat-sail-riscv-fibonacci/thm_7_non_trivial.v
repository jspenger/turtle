(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4.

#[local] Open Scope string_scope.
#[local] Open Scope tla_scope.

Definition non_trivial (F : property state) : Prop :=
        (exists beh, F beh)
                /\ (exists beh, ~ F beh).

Theorem thm_7_non_trivial :
        non_trivial impl_linked.
Proof.
(* TODO *) Admitted.

Theorem thm_7_non_trivial_2 :
        non_trivial spec_linked.
Proof.
(* TODO *) Admitted.

Definition pc_at_exit (s : state) : Prop :=
        _pc_addr s = e_static "exit".

Theorem thm_7_termination :
        valid (impl_linked
                \impl <>[] \lift1 pc_at_exit).
Proof.
(* TODO *) Admitted.

Theorem thm_7_termination_2 :
        valid (spec_linked
                \impl <>[] \lift1 pc_at_exit).
Proof.
(* TODO *) Admitted.
