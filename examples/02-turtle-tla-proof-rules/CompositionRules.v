(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import turtle.tla.TLA.
Require Import turtle.tla.TLA_2.
Require Import turtle.gen.closed.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* > Leslie Lamport. 2026. A Science of Concurrent Programs. Cambridge        *)
(* > University Press.                                                        *)
(* > https://doi.org/10.1017/9781009719841                                    *)
(*                                                                            *)
(* Other references:                                                          *)
(* > Martin Abadi and Leslie Lamport. 1995. Conjoining Specifications. ACM    *)
(* > Trans. Program. Lang. Syst. 17, 3 (May 1995), 507-535.                   *)
(* > https://doi.org/10.1145/203095.201069                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Utility lemmas                                                             *)
(* ========================================================================== *)

Lemma property_implies_closure {State : Type} (F : property State) :
    valid (F \impl util_closure F).
Proof.
    exact (closed.property_implies_closure F).
Qed.

Lemma machine_closed_def_iff {State : Type} (F L : property State) :
    util_machine_closed F L <->
        (* Ref: SCP Section 4.2.2 *)
        (* "In general, a pair <S, L>, where S is a safety property and L a
           liveness property, is defined to be machine closed iff every finite
           behavior satisfying S can be completed to a behavior satisfying
           S /\ L." *)
        util_prop_is_safety F
        /\ (forall (beh : behavior State) (n: nat),
                (* The definition of `util_tts` states that some behavior
                   with prefix `beh` up to state `n` satisfies `F` *)
                (util_tts F beh n) ->
                    (util_tts (F \land L) beh n)).
Proof.
    split.
    - intros Hmc.
        assert (Hmono : forall (beh : behavior State) (n : nat),
                    util_tts F beh n -> util_tts (F \land L) beh n).
        { intros beh n. apply (util_tts_mono F (F \land L) beh n).
            intros c HF. exact (proj2 (Hmc c) HF). }
        split; [| exact Hmono].
        intros beh HC. apply (proj1 (Hmc beh)).
        intros n. exact (Hmono beh n (HC n)).
    - intros [Hsafe Hcompl] beh. split.
        + intros HC. apply (Hsafe beh). intros n.
            exact (util_tts_mono (F \land L) F beh n
                       (fun c HFL => property_implies_closure F c (proj1 HFL))
                       (HC n)).
        + intros HF n.
            exact (Hcompl beh n (property_implies_closure F beh HF n)).
Qed.

(* ========================================================================== *)
(* Composition                                                                *)
(* ========================================================================== *)

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* Not from refs *)
(* Acyclic form of the `Decomposition` theorem with strengthening of hypothesis 
   (1.) by replacing `util_closure (M j)` with `M j` *)
Theorem Decomposition0 (E Ml M : nat -> prop) :
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st ((\lift0 (j < i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i) \impl (\A i \st M i)).
Proof.
    intros Hyp1 Hyp2 beh HMl i.
    induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hyp2 i beh (conj (Hyp1 i beh IH) (conj (HMl i) IH))).
Qed.

(* Acyclic composition of `M0` and `M1` where `M1` depends on the specification 
   of `M0` (and not the implementation `Ml0` of `M0`). *)
(* Not from refs *)
#[local] Example ex_01 (Ml0 M0 Ml1 M1 : prop) :
    valid (Ml0  \impl  M0)  ->
        valid ((M0 \land Ml1)  \impl  M1)  ->
            valid ((Ml0 \land Ml1)  \impl  (M0 \land M1)).
Proof.
    intros H0 H1 beh [HMl0 HMl1].
    assert (HM0 : M0 beh) by exact (H0 beh HMl0).
    split; [exact HM0 | exact (H1 beh (conj HM0 HMl1))].
Qed.

(* Not from refs *)
(* Acyclic form of the `Decomposition` theorem with structure defined over
   `dep`endency relation (`dep i j` reads "j depends on i" or "i before j")
   (cf. Decomposition0). *)
Corollary Decomposition1 (dep : nat -> nat -> Prop) (E Ml M : nat -> prop) :
    well_founded dep -> (* The `dep` relation is acyclic and well-founded *)
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st ((\lift0 (dep j i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (dep j i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i) \impl (\A i \st M i)).
Proof.
    intros Hwf Hyp1 Hyp2 beh HMl i.
    induction (Hwf i) as [i _ IH].
    exact (Hyp2 i beh (conj (Hyp1 i beh IH) (conj (HMl i) IH))).
Qed.

(* Not from refs *)
(* Refinement form of the `Decomposition` theorem (cf.
   Decomposition1). *)
Corollary Decomposition2 {State2 : Type} (r : State -> State2 -> Prop) (E : nat -> property State2) (Ml : nat -> property State) (M : nat -> property State2) :
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st ((\lift0 (j < i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((\rrel r (Ml i)) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\rrel r (\A i \st Ml i)) \impl (\A i \st M i)).
Proof.
    intros Hyp1 Hyp2 beh [c [Hsc HMl]] i.
    induction (Nat.lt_wf_0 i) as [i _ IH].
    apply (Hyp2 i beh). split; [exact (Hyp1 i beh IH) |].
    split; [exists c; split; [exact Hsc | exact (HMl i)] | exact IH].
Qed.

(* Not from refs *)
(* Acyclic form of the `Composition` theorem with strengthening of hypothesis
   (1.) by replacing `util_closure E` with `E` and `util_closure (M_ j)` with
   `M_ j` *)
Theorem Composition0 (E M : prop) (E_ M_ : nat -> prop) :
    (* If... *)
    (* 1. *)
    valid (\A i \st ((E \land (\A j \st ((\lift0 (j < i)) \impl (M_ j))))
        \impl (E_ i))) ->
    (* 2. (b) *)
    valid ((E \land (\A j \st M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j \st ((E_ j) \impl (M_ j)))
        \impl (E \impl M)).
Proof.
    intros Hyp1 Hyp2 beh Hspec HE.
    apply (Hyp2 beh). split; [exact HE |].
    intros i. induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hspec i (Hyp1 beh i (conj HE IH))).
Qed.

(* Not from refs *)
(* Acyclic form of the `GeneralDecomposition` theorem with strengthening of
   hypothesis (1) by replacing `util_closure E` with `E` and
   `util_closure (M j)` with `M j` *)
Theorem GeneralDecomposition0 (E : prop) (E_ Ml_ M_ : nat -> prop) :
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid ((E \land (\A j \st ((\lift0 (j < i)) \impl (M_ j))))
                \impl (E_ i))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (b) *)
    valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
    intros Hyp1 Hyp2b beh [HE HMl] i.
    induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hyp2b i beh (conj (Hyp1 i beh (conj HE IH)) (conj (HMl i) IH))).
Qed.

(* Not from refs *)
(* Acyclic form of the `GeneralDecomposition` theorem with structure defined
   over `dep`endency relation (`dep i j` reads "j depends on i" or
   "i before j") (cf. GeneralDecomposition0). *)
Corollary GeneralDecomposition1 (dep : nat -> nat -> Prop) (E : prop) (E_ Ml_ M_ : nat -> prop) :
    well_founded dep -> (* The `dep` relation is acyclic and well-founded *)
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid ((E \land (\A j \st ((\lift0 (dep j i)) \impl (M_ j))))
                \impl (E_ i))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (dep j i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (b) *)
    valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
    intros Hwf Hyp1 Hyp2b beh [HE HMl] i.
    induction (Hwf i) as [i _ IH].
    exact (Hyp2b i beh (conj (Hyp1 i beh (conj HE IH)) (conj (HMl i) IH))).
Qed.

(* Not from refs *)
(* TODO: Generalize similarly to the Decomposition theorem(s). *)
Theorem LocalDecomposition {State2 : Type} (f : State -> State2) (E1 : prop) (E2 : property State2) (F G H : prop) :
    (* If... *)
    valid ((E2 \land (\rmap f (F \land E1)))
                \impl (\rmap f G)) ->
    valid ((E2 \land (\rmap f H))
                \impl (\univ_rmap f H)) ->
    valid (H
                \impl E1) ->
    valid ((\rmap f H)
                \impl E2) ->
    (* ...then *)
    valid ((\rmap f (F \land H))
                \impl (\rmap f (G \land H))).
Proof.
    intros HFG HH HE1 HE2 beh2 (beh1 & Hs & HF & HH1).
    assert (Hw : (\rmap f H) beh2) by (exists beh1; split; assumption).
    destruct (HFG beh2 (conj (HE2 beh2 Hw) (ex_intro _ beh1 (conj Hs (conj HF (HE1 beh1 HH1)))))) as (beh1' & Hs' & HG).
    exists beh1'. split; [exact Hs' |]. split; [exact HG |].
    exact (HH beh2 (conj (HE2 beh2 Hw) Hw) beh1' Hs').
Qed.

(* Not from refs *)
(* TODO: Generalize similarly to the Decomposition theorem(s). *)
Theorem LocalDecomposition0 {State2 : Type} (r : State -> State2 -> Prop) (E1 : prop) (E2 : property State2) (F G H : prop) :
    (* If... *)
    valid ((E2 \land (\rrel r (F \land E1)))
                \impl (\rrel r G)) ->
    valid ((E2 \land (\rrel r H))
                \impl (\univ_rrel r H)) ->
    valid (H
                \impl E1) ->
    valid ((\rrel r H)
                \impl E2) ->
    (* ...then *)
    valid ((\rrel r (F \land H))
                \impl (\rrel r (G \land H))).
Proof.
    intros HFG HH HE1 HE2 beh2 (beh1 & Hs & HF & HH1).
    assert (Hw : (\rrel r H) beh2) by (exists beh1; split; assumption).
    destruct (HFG beh2 (conj (HE2 beh2 Hw) (ex_intro _ beh1 (conj Hs (conj HF (HE1 beh1 HH1)))))) as (beh1' & Hs' & HG).
    exists beh1'. split; [exact Hs' |]. split; [exact HG |].
    exact (HH beh2 (conj (HE2 beh2 Hw) Hw) beh1' Hs').
Qed.

(* Not from refs *)
#[local] Example ex_02 {State2 : Type} (f : State -> State2) (F G H : prop) :
    valid ((\rmap f F)
                \impl (\rmap f G)) ->
    valid ((\rmap f H)
                \impl (\univ_rmap f H)) ->
    valid ((\rmap f (F \land H))
                \impl (\rmap f (G \land H))).
Proof.
    intros HFG HH. apply (LocalDecomposition f (\lift0 True) (\lift0 True) F G H).
    - intros beh2 [_ (beh1 & Hs & HF & _)]. apply HFG. exists beh1. split; assumption.
    - intros beh2 [_ Hw]. exact (HH beh2 Hw).
    - intros beh1 _. exact I.
    - intros beh2 _. exact I.
Qed.

End rules.
