(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* step.v                                                                     *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.
Require Import turtle.gen.ev.

#[local] Open Scope Z_scope.

Module T := rv64d_types.

(* ========================================================================== *)
(* One step of an instruction                                                 *)
(* ========================================================================== *)

(* The registers that a step may write, besides the register `x` of its
        instruction. *)
Definition step_regs (x : T.register) : list T.register :=
        T.R_bitvector_64 T.mip ::
        T.R_bool T.minstret_increment ::
        T.R_bitvector_64 T.nextPC ::
        T.R_bitvector_64 T.PC ::
        T.R_bitvector_64 T.minstret ::
        x ::
        nil.

(* The registers that a jump may write besides: the landing pad. *)
Definition step_regs_elp (x : T.register) : list T.register :=
        T.R_bitvector_1 T.elp :: step_regs x.

(* The value of a register after the step: the last write to it, in each
        branch of a condition. *)
Ltac step_value :=
        rewrite ?lookup_if;
        repeat first
                [ rewrite lookup_set_same
                | rewrite lookup_set_other by reflexivity ];
        rewrite ?if_same;
        repeat match goal with
                | |- context [if ?c then _ else _] => destruct c
                end;
        first
                [ reflexivity
                | assumption
                | apply definitions.bv_eq; vm_compute; reflexivity ].

(* A step of an instruction: `ev` runs `try_step`. The goal is
        `exists s', outcome (try_step n b) s (res_val false s') /\ only l s s' /\ facts`. *)
Ltac step_tac :=
        intros;
        conf_intro;
        repeat match goal with
                | H : mem_word _ _ _ |- _ => unfold mem_word in H
                end;
        lazymatch goal with
                | |- exists _, outcome _ ?s _ /\ _ => ev_base s
                end;
        eexists; split;
        [ eapply outcome_conv; [ ev | reflexivity ]
        | split; [ only_tac | repeat split; step_value ] ].

(* A step of `try_step` that ends in `s'`. *)
Lemma step_1_of s s' :
        outcome (rv64d.try_step 0 true) s (res_val false s') ->
                exec_eval_step_1 s s'.
Proof.
        intros Ho. unfold exec_eval_step_1. rewrite (outcome_eval_step _ _ _ Ho). reflexivity.
Qed.

(* What a step of `try_step` with one result gives in TLA. *)
Lemma step_tla (s : state) (P : state -> Prop) :
        (forall n b, exists s', outcome (rv64d.try_step n b) s (res_val false s') /\ P s') ->
                (forall s', exec_eval_step_1 s s' -> P s')
                /\ (exists s', exec_eval_step_1 s s' /\ P s').
Proof.
        intros H. destruct (H 0%Z true) as (s1 & Ho & Hp). split.
        - intros s'. unfold exec_eval_step_1. rewrite (outcome_eval_step _ _ _ Ho).
          intros ->. exact Hp.
        - exists s1. split; [exact (step_1_of s s1 Ho) | exact Hp].
Qed.

(* ========================================================================== *)
(* The clock                                                                  *)
(* ========================================================================== *)

Lemma tick s :
        exists s',
        outcome (rv64d.tick_clock tt) s (res_val tt s')
        /\ only (T.R_bitvector_64 T.mcycle :: T.R_bitvector_64 T.mtime :: nil) s s'.
Proof.
        ev_base s.
        eexists. split.
        - eapply outcome_conv; [ ev | reflexivity ].
        - only_tac.
Qed.

(* A tick changes only the clock. *)
Lemma tick_tla s s' :
        exec_eval_step_2 s s' ->
                only (T.R_bitvector_64 T.mcycle :: T.R_bitvector_64 T.mtime :: nil) s s'.
Proof.
        destruct (tick s) as (s1 & H1 & Hl).
        unfold exec_eval_step_2. rewrite (outcome_eval_step _ _ _ H1).
        intros ->. exact Hl.
Qed.
