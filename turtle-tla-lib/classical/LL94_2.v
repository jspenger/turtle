(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

Require Import Classical.
Require Import turtle.tla.TLA.
Require Import turtle.tla.lib.LL94_2.
Require Import turtle.gen.base.

#[local] Open Scope tla_scope.

Section ll94_2.

Context {State : Type}.
#[local] Notation prop := (property State).

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated `Not from ref`):         *)
(* [1]                                                                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Additional Rules                                                           *)
(* ========================================================================== *)

(* These rules are presumably only provable using `Classical` *)

Lemma WF1 {V : Type} (P Q N A : prop) (f : State -> V) :
    valid (
        P \land [N]_f \impl (P ' \lor Q ')
    )
    /\ valid(
        P \land <<(N \land A)>>_f \impl Q '
    )
    /\ valid(
        P \impl \enabled <<A>>_f
    )
    -> valid(
        (([]([N]_f)) \land (\wf A \sub f))
        \impl
        (P \leadsto Q)
    ).
Proof.
    intros [Hp1 [Hp2 Hp3]] beh [HN HWF] k.
    apply (always_suffix _ _ k) in HN, HWF.
    set (b := util_suffix beh k) in *. intro HPk.
    apply NNPP. intro Hno.
    assert (HnoQ : Always (Not Q) b).
    { intros m HQ. apply Hno. exists m. exact HQ. }
    pose proof (always_p _ _ _ _ _ Hp1 HN HnoQ HPk) as HP.
    assert (HEn : Always (Enabled (NonStutter A f)) b).
    { intro j. exact (Hp3 (util_suffix b j) (HP j)). }
    destruct (always_now _ _ HWF HEn) as [m HA].
    exact (HnoQ _ (q_of_step _ _ _ _ _ _ _ Hp2 HN HP HA)).
Qed.

Lemma WF2 {Vf Vg : Type} (N M A B P F : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        <<(N \land B)>>_f \impl <<M>>_g
    )
    /\ valid (
        P \land (P ') \land <<(N \land A)>>_f \land \enabled <<M>>_g \impl B
    )
    /\ valid (
        P \land \enabled <<M>>_g \impl \enabled <<A>>_f
    )
    /\ valid (
        ([]([(N \land (\lnot B))]_f)) \land (\wf A \sub f) \land ([]F) \land (<>([](\enabled <<M>>_g))) \impl (<>([]P))
    )
    -> valid (
        (([]([N]_f)) \land (\wf A \sub f) \land ([]F)) \impl (\wf M \sub g)
    ).
Proof.
    intros [Hp1 [Hp2 [Hp3 Hp4]]] beh [HN [HWF HF]] k.
    apply (always_suffix _ _ k) in HN, HWF, HF.
    set (b := util_suffix beh k) in *. intro HEnM.
    apply NNPP. intro Hno.
    assert (HnoM : Always (Not (NonStutter M g)) b).
    { intros m HM. apply Hno. exists m. exact HM. }
    pose proof (stutter_of_no_m _ _ _ _ _ _ Hp1 HN HnoM) as HNB.
    assert (HEnMk : Eventually (Always (Enabled (NonStutter M g))) b).
    { exists 0. exact HEnM. }
    destruct (Hp4 b (conj HNB (conj HWF (conj HF HEnMk)))) as [d HPd].
    apply (always_suffix _ _ d) in HN, HWF, HEnM, HnoM.
    set (c := util_suffix b d) in *.
    assert (HEnA : Always (Enabled (NonStutter A f)) c).
    { intro j. exact (Hp3 (util_suffix c j) (conj (HPd j) (HEnM j))). }
    destruct (always_now _ _ HWF HEnA) as [m [HA Hch]].
    destruct (HN m) as [HNm | Hunch]; [| destruct (Hch Hunch)].
    apply (HnoM m). apply (Hp1 (util_suffix c m)).
    split; [split; [exact HNm |] | exact Hch].
    apply (Hp2 (util_suffix c m)). split; [exact (HPd m) |].
    split; [rewrite prime_suffix; exact (HPd (S m)) |].
    exact (conj (conj (conj HNm HA) Hch) (HEnM m)).
Qed.

Lemma SF1 {V : Type} (P Q N A F : prop) (f : State -> V) :
    valid(
        (P \land ([N]_f)) \impl ((P ') \lor (Q '))
    )
    /\ valid(
        (P \land (<<(N \land A)>>_f)) \impl (Q ')
    )
    /\ valid(
        (([]P) \land ([]([N]_f)) \land ([]F)) \impl (<>(\enabled (<<A>>_f)))
    )
    -> valid(
        (([]([N]_f)) \land (\sf A \sub f) \land ([]F)) \impl (P \leadsto Q)
    ).
Proof.
    intros [Hp1 [Hp2 Hp3]] beh [HN [HSF HF]] k.
    apply (always_suffix _ _ k) in HN, HSF, HF.
    set (b := util_suffix beh k) in *. intro HPk.
    apply NNPP. intro Hno.
    assert (HnoQ : Always (Not Q) b).
    { intros m HQ. apply Hno. exists m. exact HQ. }
    pose proof (always_p _ _ _ _ _ Hp1 HN HnoQ HPk) as HP.
    assert (HEn : Always (Eventually (Enabled (NonStutter A f))) b).
    { intro j. apply (Hp3 (util_suffix b j)).
        split; [exact (always_suffix _ _ j HP) |].
        split; [exact (always_suffix _ _ j HN) |].
        exact (always_suffix _ _ j HF). }
    destruct (always_now _ _ HSF HEn) as [m HA].
    exact (HnoQ _ (q_of_step _ _ _ _ _ _ _ Hp2 HN HP HA)).
Qed.

Lemma SF2 {Vf Vg : Type} (N M A B P F : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        (<<(N \land B)>>_f) \impl (<<M>>_g) 
    )
    /\ valid (
        P \land (P ') \land (<<(N \land A)>>_f) \impl B
    )
    /\ valid (
        P \land (\enabled (<<M>>_g)) \impl (\enabled (<<A>>_f))
    )
    /\ valid (
        (([]([(N \land (\lnot B))]_f)) \land (\sf A \sub f) \land ([]F) \land ([]<>(\enabled (<<M>>_g)))) \impl (<>([]P))
    )
    -> valid (
        (([]([N]_f)) \land (\sf A \sub f) \land ([]F)) \impl (\sf M \sub g)
    ).
Proof.
    intros [Hp1 [Hp2 [Hp3 Hp4]]] beh [HN [HSF HF]] k.
    apply (always_suffix _ _ k) in HN, HSF, HF.
    set (b := util_suffix beh k) in *. intro HEnM.
    apply NNPP. intro Hno.
    assert (HnoM : Always (Not (NonStutter M g)) b).
    { intros m HM. apply Hno. exists m. exact HM. }
    pose proof (stutter_of_no_m _ _ _ _ _ _ Hp1 HN HnoM) as HNB.
    destruct (Hp4 b (conj HNB (conj HSF (conj HF HEnM)))) as [d HPd].
    apply (always_suffix _ _ d) in HN, HSF, HEnM, HnoM.
    set (c := util_suffix b d) in *.
    assert (HEnA : Always (Eventually (Enabled (NonStutter A f))) c).
    { intro j. destruct (HEnM j) as [i HEi]. exists i.
        apply (Hp3 (util_suffix (util_suffix c j) i)).
        split; [exact (always_suffix _ _ j HPd i) | exact HEi]. }
    destruct (always_now _ _ HSF HEnA) as [m [HA Hch]].
    destruct (HN m) as [HNm | Hunch]; [| destruct (Hch Hunch)].
    apply (HnoM m). apply (Hp1 (util_suffix c m)).
    split; [split; [exact HNm |] | exact Hch].
    apply (Hp2 (util_suffix c m)). split; [exact (HPd m) |].
    split; [rewrite prime_suffix; exact (HPd (S m)) |].
    exact (conj (conj HNm HA) Hch).
Qed.

End ll94_2.

(* ========================================================================== *)
(* Temporal Quantification                                                    *)
(* ========================================================================== *)

(* See `State` def in turtle.tla.lib.LL94_2 *)
#[local] Definition State (Id Var : Type) : Type := Id -> Var.

(* Not from refs *)
Lemma FF4 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid (F \impl \AA x \st F) -> (* x not free in F *)
        valid ((\AA x \st (F \lor G))
            \equiv (F \lor (\AA x \st G))).
Proof.
    intros Hfree beh. split.
    - intros HA. apply NNPP. intros Hn. apply Hn. right. intros beh1 Hse.
        destruct (HA beh1 Hse) as [HF | HG].
        + exfalso. apply Hn. left. apply (Hfree beh1 HF).
            apply stuttering_equivalent0_sym; [| exact Hse].
            intros s t Hst y Hy. exact (eq_sym (Hst y Hy)).
        + exact HG.
    - intros [HF | HG] beh1 Hse.
        + left. exact (Hfree beh HF beh1 Hse).
        + right. exact (HG beh1 Hse).
Qed.
