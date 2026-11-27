(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.

Require Riscv.rv64d_types.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.gen.reg.
Require Import turtle.compat.sail.riscv.examples.fib.conf_default.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1_proof_x.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4_proof_x.
Require Import turtle.compat.sail.riscv.examples.fib.thm_6_stack_ok.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Module T := rv64d_types.

(* The stack pointer of a stage of main: that of the first state, or 16
        below it. *)
Lemma m_regs_sp k s :
        (k < 36)%nat ->
        m_regs k s ->
                reg T.x2 0x4000000000 s
                \/ reg T.x2 0x3ffffffff0 s.
Proof.
        intros Hk Hx.
        destruct k as [| k]; [left; exact Hx |].
        do 35 (destruct k as [| k];
                [right; cbn [m_regs] in Hx; first [exact Hx | exact (proj1 Hx)] |]).
        lia.
Qed.

(* The stack pointer of a state of the linked code. *)
Lemma G_sp s :
        G s ->
                reg T.x2 0x4000000000 s
                \/ reg T.x2 0x3ffffffff0 s.
Proof.
        intros [(k & Hk & _ & _ & Hx) | (N & p & _ & _ & _ & _ & X2 & _)].
        - exact (m_regs_sp k s Hk Hx).
        - right. exact X2.
Qed.

Theorem thm_6_stack_ok :
        valid (impl_linked
                \impl [] stack_ok).
Proof.
        intros sigma (Hfib & Hlibc & Hmain) k.
        unfold stack_ok, Lift1, util_suffix. rewrite Nat.add_0_r.
        change (conf_stack_addr + conf_stack_size) with 0x4000000000.
        change conf_stack_addr with 0x3ffffff000. unfold abi_sp.
        destruct (G_sp _ (linked_G sigma Hfib Hlibc Hmain k)) as [H | H];
                rewrite (reg_abi _ _ _ H ltac:(lia)); lia.
Qed.

(* The statement of thm_6_stack_ok.v. *)
Definition thm_6_stack_ok_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_6_stack_ok.thm_6_stack_ok in exact t) :=
        thm_6_stack_ok.

Print Assumptions thm_6_stack_ok.
