(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* reg.v                                                                      *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.

Require stdpp.bitvector.definitions.
Require Riscv.rv64d_types.

Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.

#[local] Open Scope Z_scope.

Module T := rv64d_types.

(* ========================================================================== *)
(* Registers                                                                  *)
(* ========================================================================== *)

(* The value `v` in the register `r`. *)
Definition reg (r : T.register_bitvector_64) (v : Z) (s : state) : Prop :=
        T.register_lookup (T.R_bitvector_64 r) (st_regs s) = definitions.Z_to_bv 64 v.

Lemma reg_only l r v s s' :
        only l s s' ->
        reg r v s ->
        reg_in l (T.R_bitvector_64 r) = false ->
                reg r v s'.
Proof.
        intros (_ & Ho) Hv Hr. unfold reg in *. rewrite (Ho _ Hr). exact Hv.
Qed.

Lemma reg_pc v s :
        reg T.PC v s ->
        0 <= v < 2 ^ 64 ->
                _pc_addr s = v.
Proof.
        intros Hpc Hv. unfold _pc_addr, st_regs_read, _regs_read. unfold reg in Hpc. rewrite Hpc.
        apply definitions.Z_to_bv_small. unfold definitions.bv_modulus. exact Hv.
Qed.

Lemma pc_reg v s :
        _pc_addr s = v ->
                reg T.PC v s.
Proof.
        intros <-. unfold reg, _pc_addr, st_regs_read, _regs_read. symmetry.
        apply definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma reg_abi r v s :
        reg r v s ->
        0 <= v < 2 ^ 64 ->
                _state_regs_to_z s r = v.
Proof.
        intros Hr Hv. unfold _state_regs_to_z, st_regs_read, _regs_read. unfold reg in Hr. rewrite Hr.
        apply definitions.Z_to_bv_small. unfold definitions.bv_modulus. exact Hv.
Qed.

Lemma abi_reg r s :
        reg r (_state_regs_to_z s r) s.
Proof.
        unfold reg, _state_regs_to_z, st_regs_read, _regs_read. symmetry.
        apply definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma abi_range r s :
        0 <= _state_regs_to_z s r < 2 ^ 64.
Proof.
        unfold _state_regs_to_z.
        pose proof (definitions.bv_unsigned_in_range _
                (st_regs_read s (T.R_bitvector_64 r))) as H.
        unfold definitions.bv_modulus in H. exact H.
Qed.

(* A register that a step did not write. *)
Lemma abi_only l r s s' :
        only l s s' ->
        reg_in l (T.R_bitvector_64 r) = false ->
                _state_regs_to_z s' r = _state_regs_to_z s r.
Proof.
        intros (_ & Ho) Hr. unfold _state_regs_to_z, st_regs_read, _regs_read.
        rewrite (Ho _ Hr). reflexivity.
Qed.

(* The registers that a call preserves. *)
Definition preserved (r : T.register_bitvector_64) : bool :=
        match r with
                | T.x2
                | T.x3
                | T.x4
                | T.x8
                | T.x9
                | T.x18
                | T.x19
                | T.x20
                | T.x21
                | T.x22
                | T.x23
                | T.x24
                | T.x25
                | T.x26
                | T.x27 => true
                | _     => false
                end.

(* A register that a call preserves. *)
Lemma reg_preserved r v s s' :
        abi_stepcond_preserve_regs s s' ->
        preserved r = true ->
        reg r v s ->
                reg r v s'.
Proof.
        intros Hp Hr Hx. unfold reg in *.
        unfold abi_stepcond_preserve_regs, _state_regs_to_bv, st_regs_read, _regs_read in Hp.
        destruct Hp as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
        destruct r; try discriminate Hr; rewrite <- Hx; symmetry; assumption.
Qed.

(* The registers of a goal, after the step `Hl : only l s s'`: those that the
        step wrote are hypotheses, the others are kept. *)
Ltac regs_after Hl :=
        repeat match goal with
                | |- _ /\ _ => split
                end;
        first
                [ exact I
                | assumption
                | (unfold reg; assumption)
                | (eapply reg_only; [ exact Hl | assumption | reflexivity ])
                | lia ].

(* ========================================================================== *)
(* The return from a call                                                     *)
(* ========================================================================== *)

(* The PC at `a`, nothing else changed. *)
Definition ret_to (a : Z) (s : state) : state :=
        set_reg (T.R_bitvector_64 T.PC) (definitions.Z_to_bv 64 a) s.

Lemma ret_to_only a s :
        only (T.R_bitvector_64 T.PC :: nil) s (ret_to a s).
Proof.
        unfold ret_to. apply only_set_reg; [reflexivity | apply only_refl].
Qed.

Lemma ret_to_pc a s :
        reg T.PC a (ret_to a s).
Proof.
        unfold reg, ret_to. apply lookup_set_same.
Qed.

Lemma ret_to_ne a s :
        0 <= a < 2 ^ 64 ->
        _pc_addr s <> a ->
                s <> ret_to a s.
Proof.
        intros Ha Hs He. apply Hs. rewrite He at 1. exact (reg_pc a _ (ret_to_pc a s) Ha).
Qed.

(* A return to `ra`: the step of a call. *)
Lemma ret_to_abi a s :
        0 <= a < 2 ^ 64 ->
        abi_ra s = a ->
                abi_stepcond s (ret_to a s)
                /\ abi_opt_stepcond_preserve_mem s (ret_to a s)
                /\ abi_opt_stepcond_return s (ret_to a s).
Proof.
        intros Ha Hra. split; [split | split].
        - unfold abi_stepcond_preserve_regs, _state_regs_to_bv, st_regs_read, _regs_read, ret_to.
          repeat split; rewrite lookup_set_other; reflexivity.
        - exact (preserve_conf_only (T.R_bitvector_64 T.PC :: nil) _ _ eq_refl (ret_to_only a s)).
        - unfold abi_opt_stepcond_preserve_mem, ret_to. symmetry. apply mem_set_reg.
        - unfold abi_opt_stepcond_return. rewrite Hra. exact (reg_pc a _ (ret_to_pc a s) Ha).
Qed.
