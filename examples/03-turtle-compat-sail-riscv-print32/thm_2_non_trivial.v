(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.compat.sail.riscv.examples.print32.main_1.
Require Import turtle.compat.sail.riscv.examples.print32.main_2.
Require Import turtle.compat.sail.riscv.examples.print32.thm.

#[local] Open Scope string_scope.
#[local] Open Scope tla_scope.

Definition non_trivial (F : property state) : Prop :=
        (exists beh, F beh)
                /\ (exists beh, ~ F beh).

Definition pc_at_exit (s : state) : Prop :=
        _pc_addr s = e_static "exit".

Theorem thm_2_non_trivial_1 :
        non_trivial (exec_static main_1_s \land unsafe_libc e_static).
Proof.
(* TODO *) Admitted.

Theorem thm_2_non_trivial_2 :
        non_trivial (exec_static main_2_s \land unsafe_libc e_static).
Proof.
(* TODO *) Admitted.

Theorem thm_2_termination_1 :
        valid (exec_static main_1_s \land unsafe_libc e_static
                \impl <>[] \lift1 pc_at_exit).
Proof.
(* TODO *) Admitted.

Theorem thm_2_termination_2 :
        valid (exec_static main_2_s \land unsafe_libc e_static
                \impl <>[] \lift1 pc_at_exit).
Proof.
(* TODO *) Admitted.
