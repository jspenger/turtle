(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.main.
Require Import turtle.compat.sail.riscv.examples.fib.spec.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.
Require turtle.compat.sail.riscv.examples.fib.thm_1_proof_x.
Require turtle.compat.sail.riscv.examples.fib.thm_2_proof_x.
Require turtle.compat.sail.riscv.examples.fib.thm_3.

#[local] Open Scope tla_scope.

Theorem thm_3 :
        valid ((\rmap (rm e_static)
                        (E e_static
                        \land exec_static tl_fib_impl_s
                        \land unsafe_libc e_static
                        \land exec_static main_s))
                \impl (\rmap (rm e_static)
                                (tl_fib_spec e_static
                                \land unsafe_libc e_static
                                \land exec_static main_s))).
Proof.
        intros tau (sigma & Hs & HE & Himpl & Hlibc & Hmain).
        (* thm_1: a behaviour of the spec with the same image *)
        assert (H1 : (\rmap (rm e_static) (E e_static \land exec_static tl_fib_impl_s)) tau).
        { exists sigma. split; [exact Hs |]. exact (conj HE Himpl). }
        destruct (turtle.compat.sail.riscv.examples.fib.thm_1_proof_x.thm_1 tau H1)
                as (sigma' & Hs' & Hspec).
        exists sigma'. split; [exact Hs' |].
        split; [exact Hspec |]. split.
        - (* thm_2_1: the libc holds of it *)
          assert (H2 : (\rmap (rm e_static) (E e_static \land unsafe_libc e_static)) tau).
          { exists sigma. split; [exact Hs |]. exact (conj HE Hlibc). }
          exact (turtle.compat.sail.riscv.examples.fib.thm_2_proof_x.thm_2_1 tau H2 sigma' Hs').
        - (* thm_2_2: main holds of it *)
          assert (H2 : (\rmap (rm e_static) (E e_static \land exec_static main_s)) tau).
          { exists sigma. split; [exact Hs |]. exact (conj HE Hmain). }
          exact (turtle.compat.sail.riscv.examples.fib.thm_2_proof_x.thm_2_2 tau H2 sigma' Hs').
Qed.

(* The statement of thm_3.v. *)
Definition thm_3_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_3.thm_3 in exact t) :=
        thm_3.

Print Assumptions thm_3.
