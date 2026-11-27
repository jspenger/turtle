(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* tla.v                                                                      *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Wf_nat.

Require Import turtle.tla.TLA.
Require Import turtle.gen.base.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* Steps and fairness, at an index                                            *)
(* ========================================================================== *)

Lemma next_at {St : Type} (sigma : behavior St) (N : St -> St -> Prop) :
        ([][\lift2 N]_ (fun s => s)) sigma ->
                forall i,
                N (sigma i) (sigma (S i))
                \/ sigma i = sigma (S i).
Proof.
        intros H i. specialize (H i).
        unfold Stutter, Or, Unchanged in H. unfold Lift2, util_suffix in H.
        rewrite Nat.add_0_r, Nat.add_1_r in H. exact H.
Qed.

Lemma next_intro (sigma : behavior state) (N : state -> state -> Prop) :
        (forall i,
                N (sigma i) (sigma (S i))
                \/ sigma i = sigma (S i)) ->
                ([][\lift2 N]_ exec_vars) sigma.
Proof.
        intros H i.
        unfold Stutter, Or, Unchanged. unfold Lift2, util_suffix, exec_vars.
        rewrite Nat.add_0_r, Nat.add_1_r. exact (H i).
Qed.

Lemma wf_at {St : Type} (sigma : behavior St) (A : St -> St -> Prop) :
        (\wf (\lift2 A) \sub (fun s => s)) sigma ->
                forall i,
                (forall j, exists s', A (sigma (i + j)%nat) s' /\ sigma (i + j)%nat <> s') ->
                        exists m,
                        A (sigma (i + m)%nat) (sigma (S (i + m))).
Proof.
        intros H i Hen. specialize (H i).
        unfold Implication in H.
        destruct H as (m & Hm & _).
        - intros j. destruct (Hen j) as (s' & Ha & Hne).
          exists (fun n => match n with O => sigma (i + j)%nat | S _ => s' end).
          unfold NonStutter, And, Not, Unchanged. unfold Lift2, util_suffix.
          rewrite Nat.add_0_r. split; [reflexivity |]. split; assumption.
        - exists m.
          unfold Lift2, util_suffix in Hm.
          rewrite Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r in Hm. exact Hm.
Qed.

(* ========================================================================== *)
(* The next stage of a section                                                *)
(* ========================================================================== *)

(* The PC is in the section at `addr`. *)
Definition at_pc (sec : source_section) (addr : Z) (s : state) : Prop :=
        addr - 1 < _pc_addr s < addr + _section_size sec.

(* From a state of `P`, in the section at `addr`, a state of `Q` is reached:
        the step of a state of `P` is enabled and ends in `Q`, a tick keeps
        `P`, and the section is fair. *)
Lemma leads (sigma : behavior state) (sec : source_section) (addr : Z) (P Q : state -> Prop) :
        (forall i,
                exec_next_src_1 sec addr (sigma i) (sigma (S i))
                \/ sigma i = sigma (S i)) ->
        (forall i,
                (forall j, exists s',
                        exec_fair_src_1 sec addr (sigma (i + j)%nat) s'
                        /\ sigma (i + j)%nat <> s') ->
                        exists m,
                        exec_fair_src_1 sec addr (sigma (i + m)%nat) (sigma (S (i + m)))) ->
        (forall s, P s -> at_pc sec addr s) ->
        (forall s s', P s -> exec_eval_step_1 s s' -> Q s') ->
        (forall s, P s -> exists s', exec_eval_step_1 s s' /\ s <> s') ->
        (forall s s', P s -> exec_eval_step_2 s s' -> P s') ->
        forall i,
        P (sigma i) ->
                exists j,
                Q (sigma j).
Proof.
        intros Hnext Hwf Hat Hok Hen Htick i Hi.
        destruct (excluded_middle (exists j, Q (sigma j))) as [H | Hno]; [exact H |].
        assert (Hall : forall d, P (sigma (i + d)%nat)).
        { induction d as [| d IH].
          - rewrite Nat.add_0_r. exact Hi.
          - rewrite Nat.add_succ_r.
            destruct (Hnext (i + d)%nat) as [Hn | Heq].
            + destruct (Hn (Hat _ IH)) as [Ho | Ht].
              * exfalso. apply Hno. eexists. exact (Hok _ _ IH Ho).
              * exact (Htick _ _ IH Ht).
            + rewrite <- Heq. exact IH. }
        destruct (Hwf i) as (m & _ & Ho).
        - intros j. destruct (Hen _ (Hall j)) as (s' & Ho & Hne).
          exists s'. split; [| exact Hne].
          split; [exact (Hat _ (Hall j)) | exact Ho].
        - eexists. exact (Hok _ _ (Hall m) Ho).
Qed.

(* ========================================================================== *)
(* Weak fairness                                                              *)
(* ========================================================================== *)

(* A behaviour that stays at a state where the action can only stutter. *)
Lemma wf_end (sigma : behavior state) (A : state -> state -> Prop) (N : nat) :
        (forall n, (N <= n)%nat -> sigma n = sigma N) ->
        (forall s', A (sigma N) s' -> s' = sigma N) ->
                (\wf (\lift2 A) \sub exec_vars) sigma.
Proof.
        intros Hend Hno k Hen. exfalso.
        specialize (Hen N). destruct Hen as (beh & H0 & HA & Hne).
        unfold util_suffix in H0. rewrite Nat.add_0_r in H0.
        rewrite (Hend (k + N)%nat) in H0 by lia.
        unfold Lift2 in HA. rewrite H0 in HA.
        apply Hne. unfold Unchanged, Lift2, exec_vars.
        rewrite H0. symmetry. exact (Hno _ HA).
Qed.

(* From a state of `P`, a state of `Q` is reached: a step from `P` stays in
        `P` or ends in `Q`, the action `A` is enabled in `P` and ends in `Q`,
        and `A` is weakly fair. *)
Lemma leads_wf {St : Type} (sigma : behavior St) (A : St -> St -> Prop) (P Q : St -> Prop) :
        (\wf (\lift2 A) \sub (fun s => s)) sigma ->
        (forall i, P (sigma i) -> P (sigma (S i)) \/ Q (sigma (S i))) ->
        (forall s, P s -> exists s', A s s' /\ s <> s') ->
        (forall s s', P s -> A s s' -> Q s') ->
        forall i,
        P (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ Q (sigma j).
Proof.
        intros Hwf Hstep Hen HA i Hi.
        destruct (excluded_middle (exists j, (i <= j)%nat /\ Q (sigma j))) as [H | Hno]; [exact H |].
        assert (Hall : forall d, P (sigma (i + d)%nat)).
        { induction d as [| d IH].
          - rewrite Nat.add_0_r. exact Hi.
          - rewrite Nat.add_succ_r. destruct (Hstep _ IH) as [H | H]; [exact H |].
            exfalso. apply Hno. exists (S (i + d)). split; [lia | exact H]. }
        destruct (wf_at sigma A Hwf i) as (m & Hm).
        - intros j. exact (Hen _ (Hall j)).
        - exists (S (i + m)). split; [lia |]. exact (HA _ _ (Hall m) Hm).
Qed.

(* ========================================================================== *)
(* Indices                                                                    *)
(* ========================================================================== *)

(* The least index of a property that holds at some index. *)
Lemma least (P : nat -> Prop) :
        (exists n, P n) ->
                exists n,
                P n
                /\ forall m, (m < n)%nat -> ~ P m.
Proof.
        intros (n & Hn). revert Hn. induction n as [n IH] using lt_wf_ind. intros Hn.
        destruct (excluded_middle (exists m, (m < n)%nat /\ P m)) as [(m & Hm & Pm) | Hno].
        - exact (IH m Hm Pm).
        - exists n. split; [exact Hn |]. intros m Hm Pm. apply Hno. exists m. split; assumption.
Qed.
