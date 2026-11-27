(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

Require Import turtle.tla.TLA.
Require Import turtle.tla.TLA_2.
Require Import turtle.gen.closed.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* [1]                                                                        *)
(* > Leslie Lamport. 2026. A Science of Concurrent Programs. Cambridge        *)
(* > University Press.                                                        *)
(* > https://doi.org/10.1017/9781009719841                                    *)
(*                                                                            *)
(* Other references:                                                          *)
(* [2]                                                                        *)
(* > Martin Abadi and Leslie Lamport. 1995. Conjoining Specifications. ACM    *)
(* > Trans. Program. Lang. Syst. 17, 3 (May 1995), 507-535.                   *)
(* > https://doi.org/10.1145/203095.201069                                    *)
(*                                                                            *)
(* The file is named after AL95 [2] which was the (first, to my knowledge)    *)
(* presentation of the decomposition and composition theorems. I don't        *)
(* remember for certain if there was a difference between [1] and [2].        *)
(* However, I seem to have favored some of the writing / definitions from     *)
(* [1] as evident in my comments.                                             *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Composition                                                                *)
(* ========================================================================== *)

Section al95.

Context {State : Type}.
#[local] Notation prop := (property State).

(* Ref: SCP Theorem 8.7 (Decomposition Theorem) *)
Theorem Decomposition {V : Type} (v : State -> V) (E Ml M : nat -> prop) :
    (forall i : nat,
            util_stuttering_closed (Ml i))  ->
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st (util_closure (M j)))
                \impl (E i))) ->
    (* 2. (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E i)) v) \land (util_closure (Ml i)))
                \impl (util_closure (M i)))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i)
        \impl (\A i \st M i)).
Proof.
    intros Hstut Hyp1 Hyp2a Hyp2b beh HMl.
    assert (HCMl : forall j : nat, util_closure (Ml j) beh)
        by (intros j; exact (property_implies_closure (Ml j) beh (HMl j))).
    assert (HE : forall n i : nat, util_tts (E i) beh n).
    { intros n i.
        refine (util_prefix_induction (\lift0 True) E M beh _ _ _ n
                    (property_implies_closure (\lift0 True) beh I n) i).
        - intros b c _ Hb. exact Hb.
        - intros k b [_ HC]. exact (Hyp1 k b HC).
        - intros m k HEk. apply (Hyp2a k (util_trunc beh m)).
            split; [exact (util_trunc_plus (E k) v beh m HEk) |].
            exact (util_tts_freeze (Ml k) beh m (Hstut k) (HCMl k (S m))). }
    assert (HC : forall j : nat, util_closure (M j) beh).
    { intros j. apply (Hyp2a j beh). split; [| exact (HCMl j)].
        left. intros n. exact (HE n j). }
    intros i. induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hyp2b i beh (conj (Hyp1 i beh HC) (conj (HMl i) IH))).
Qed.

(* Ref: SCP Theorem 8.8 (Composition Theorem) *)
Theorem Composition {V : Type} (v : State -> V) (E M : prop) (E_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall j : nat,
            util_stuttering_closed (M_ j))  ->
    (* If... *)
    (* 1. *)
    valid (\A i \st (((util_closure E) \land (\A j \st (util_closure (M_ j))))
        \impl (E_ i))) ->
    (* 2. (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j \st (util_closure (M_ j))))
        \impl (util_closure M)) ->
    (* 2. (b) *)
    valid ((E \land (\A j \st M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j \st (util_plus_arrow (E_ j) (M_ j)))
        \impl (util_plus_arrow E M)).
Proof.
    intros HscE HscM Hyp1 Hyp2a Hyp2b beh Hspec.
    assert (HQ : forall m : nat,
                util_tts E beh m -> forall j : nat, util_tts (E_ j) beh m).
    { apply (util_prefix_induction E E_ M_ beh HscE (fun i c => Hyp1 c i)).
        intros m k HEk.
        exact (util_tts_freeze (M_ k) beh m (HscM k) (proj2 (Hspec k) m HEk)). }
    split.
    - intros HE.
        assert (HCE : util_closure E beh)
            by exact (property_implies_closure E beh HE).
        assert (HCall : forall j : nat, util_closure (M_ j) beh).
        { intros j p. destruct p as [| p]; [left; reflexivity |].
            exact (proj2 (Hspec j) p (HQ p (HCE p) j)). }
        apply (Hyp2b beh). split; [exact HE |].
        intros j. exact (proj1 (Hspec j) (Hyp1 beh j (conj HCE HCall))).
    - intros n HEn.
        assert (HCM : util_closure M (util_trunc beh n)).
        { apply (Hyp2a (util_trunc beh n)).
            split; [exact (util_trunc_plus E v beh n HEn) |].
            intros k. apply (util_tts_freeze (M_ k) beh n (HscM k)).
            exact (proj2 (Hspec k) n (HQ n HEn k)). }
        apply (util_tts_agree M (util_trunc beh n) beh (S n));
            [| exact (HCM (S n))].
        intros i Hi. apply util_trunc_agree. exact Hi.
Qed.

(* Ref: "Conjoining Specifications" Corollary 1 *)
Corollary CompositionCor1 {V : Type} (v : State -> V) (E Ml M : prop) :
    util_stuttering_closed E ->
    util_stuttering_closed Ml ->
    (* If... *)
    valid ((util_closure E)
        \impl E)  ->
    (* (a) *)
    valid (((util_plus_operator E v) \land (util_closure Ml))
        \impl (util_closure M)) ->
    (* (b) *)
    valid ((E \land Ml)
        \impl M) ->
    (* ...then *)
    valid ((util_plus_arrow E Ml)
        \impl (util_plus_arrow E M)).
Proof.
    intros HscE HscMl Hsafe Hyp_a Hyp_b beh Hspec.
    pose (E_ := fun j : nat => match j with 0 => E | _ => \lift0 True end).
    pose (M_ := fun j : nat => match j with 0 => Ml | _ => \lift0 True end).
    refine (Composition v E M E_ M_ HscE _ _ _ _ beh _).
    - intros [| j]; [exact HscMl | intros b c _ Hb; exact Hb].
    - intros b [| j] [HCE HCall]; [exact (Hsafe b HCE) | exact I].
    - intros b [Hplus HCall]. apply (Hyp_a b). split; [| exact (HCall 0)].
        destruct Hplus as [HCE | [k [Hfrz HEk]]].
        + left. exact (Hsafe b HCE).
        + right. exists k.
            split; [exact Hfrz | exact (proj1 (util_tts_closure E b k) HEk)].
    - intros b [HE Hall]. exact (Hyp_b b (conj HE (Hall 0))).
    - intros [| j]; [exact Hspec |].
        split; [intros _; exact I |].
        intros n _. right. exists beh.
        split; [exact I | intros i _; reflexivity].
Qed.

(* Ref: "Conjoining Specifications" Theorem 2 (General Decomposition Theorem) *)
(* The hypothesis "v is a tuple of variables including all the free variables of
   Mi" ("Conjoining Specifications", Theorem 2) is omitted. Instead, as
   suggested in SCP, "The theorem does not [need to] make any assumption about
   v". *)
(* The definition adds `(\A j \st ((\lift0 (j < i)) \impl (M_ j)))` to hypothesis
   (2) b as is done in `Decomposition` (SCP, Theorem 8.7) but missing from
   Theorem 2. *)
Theorem GeneralDecomposition {V : Type} (v : State -> V) (E : prop) (E_ Ml_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall i : nat,
            util_stuttering_closed (Ml_ i))  ->
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid (((util_closure E) \land (\A j \st (util_closure (M_ j))))
                \impl (E_ i))) ->
    (* (2) (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E_ i)) v) \land (util_closure (Ml_ i)))
                \impl (util_closure (M_ i)))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j \st (util_closure (Ml_ j))))
        \impl (\A j \st (util_closure (M_ j))))
    (* (b) *)
    /\ valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
    intros HscE HscMl Hyp1 Hyp2a Hyp2b.
    assert (HQ : forall b : behavior State,
                (forall j : nat, util_closure (Ml_ j) b) ->
                    forall m : nat, util_tts E b m ->
                        forall j : nat, util_tts (E_ j) b m).
    { intros b HMl. apply (util_prefix_induction E E_ M_ b HscE Hyp1).
        intros m k HEk. apply (Hyp2a k (util_trunc b m)).
        split; [exact (util_trunc_plus (E_ k) v b m HEk) |].
        exact (util_tts_freeze (Ml_ k) b m (HscMl k) (HMl k (S m))). }
    split.
    - intros b [Hplus HMl] j.
        apply (Hyp2a j b). split; [| exact (HMl j)].
        destruct Hplus as [HCE | [k [Hfrz HEk]]].
        + left. intros m. exact (HQ b HMl m (HCE m) j).
        + right. exists k. split; [exact Hfrz |].
            apply (proj2 (util_tts_closure (E_ j) b k)).
            exact (HQ b HMl k (proj1 (util_tts_closure E b k) HEk) j).
    - intros b [HE HMl].
        assert (HCMl : forall j : nat, util_closure (Ml_ j) b)
            by (intros j; exact (property_implies_closure (Ml_ j) b (HMl j))).
        assert (HCE : util_closure E b)
            by exact (property_implies_closure E b HE).
        assert (HCall : forall j : nat, util_closure (M_ j) b).
        { intros j. apply (Hyp2a j b). split; [| exact (HCMl j)].
            left. intros m. exact (HQ b HCMl m (HCE m) j). }
        intros j. induction (Nat.lt_wf_0 j) as [j _ IH].
        exact (Hyp2b j b (conj (Hyp1 j b (conj HCE HCall)) (conj (HMl j) IH))).
Qed.

End al95.
