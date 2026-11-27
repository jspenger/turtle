(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.Lists.List.

Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.thm_5_source_ok.

(* The checks of tl_fib: a closed computation. *)
Lemma tl_fib_source_ok :
        _source_ok tl_fib_impl_s = true.
Proof.
        vm_compute. reflexivity.
Qed.

Theorem thm_5_source_ok :
        _sources_ok (tl_fib_impl_s :: nil).
Proof.
        apply Forall_cons; [exact tl_fib_source_ok |].
        apply Forall_nil.
Qed.

(* The statement of thm_5_source_ok.v. *)
Definition thm_5_source_ok_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_5_source_ok.thm_5_source_ok in exact t) :=
        thm_5_source_ok.

Print Assumptions thm_5_source_ok.
