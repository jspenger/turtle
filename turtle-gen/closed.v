(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* closed.v                                                                   *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Export turtle.gen.stutter.
Require Import turtle.tla.TLA_2.

Definition util_reads {State : Type} (l : nat) (P : property State) : Prop :=
    forall b c : behavior State, (forall i : nat, i < l -> b i = c i) -> P b -> P c.

#[local] Lemma util_reads_flip {State : Type} (l : nat) (F : property State) :
    util_reads l F ->
        forall b c : behavior State, (forall i : nat, i < l -> b i = c i) -> F c -> F b.
Proof.
    intros HF b c Hbc. apply (HF c b). intros i Hi. symmetry. exact (Hbc i Hi).
Qed.

#[local] Lemma util_closed_flip {State : Type} (F : property State) :
    util_stuttering_closed F ->
        forall b c : behavior State, util_stuttering_equivalent b c -> F c -> F b.
Proof.
    intros HF b c Hbc. exact (HF c b (stuttering_equivalent_sym b c Hbc)).
Qed.

Lemma reads_weaken {State : Type} (l l' : nat) (P : property State) :
    l <= l' -> util_reads l P -> util_reads l' P.
Proof.
    intros Hl HP b c Hbc. apply (HP b c). intros i Hi. apply Hbc. lia.
Qed.

Lemma reads_stuttering_closed {State : Type} (l : nat) (P : property State) :
    l <= 1 -> util_reads l P -> util_stuttering_closed P.
Proof.
    intros Hl HP b c Hbc H. apply (HP b c); [| exact H].
    intros i Hi. replace i with 0 by lia. exact (stuttering_equivalent_head b c Hbc).
Qed.

Lemma lift0_reads {State : Type} (p : Prop) :
    util_reads 0 (@Lift0 State p).
Proof.
    intros b c _ H. exact H.
Qed.

Lemma lift1_reads {State : Type} (p : State -> Prop) :
    util_reads 1 (Lift1 p).
Proof.
    intros b c Hbc H. unfold Lift1 in *. rewrite <- (Hbc 0 (Nat.lt_0_succ 0)). exact H.
Qed.

Lemma lift2_reads {State : Type} (a : State -> State -> Prop) :
    util_reads 2 (Lift2 a).
Proof.
    intros b c Hbc H. unfold Lift2 in *.
    rewrite <- (Hbc 0 (Nat.lt_0_succ 1)), <- (Hbc 1 (Nat.lt_succ_diag_r 1)). exact H.
Qed.

Lemma unchanged_reads {State V : Type} (e : State -> V) :
    util_reads 2 (Unchanged e).
Proof.
    exact (lift2_reads (fun s s' => e s = e s')).
Qed.

Lemma prime_reads {State : Type} (l : nat) (F : property State) :
    util_reads l F -> util_reads (S l) (Prime F).
Proof.
    intros HF b c Hbc H. unfold Prime.
    apply (HF (util_suffix b 1) (util_suffix c 1)); [| exact H].
    intros i Hi. unfold util_suffix. apply Hbc. lia.
Qed.

Lemma not_reads {State : Type} (l : nat) (F : property State) :
    util_reads l F -> util_reads l (Not F).
Proof.
    intros HF b c Hbc HnF HFc. exact (HnF (util_reads_flip l F HF b c Hbc HFc)).
Qed.

Lemma and_reads {State : Type} (l : nat) (F G : property State) :
    util_reads l F -> util_reads l G -> util_reads l (And F G).
Proof.
    intros HF HG b c Hbc [HFb HGb]. split.
    - exact (HF b c Hbc HFb).
    - exact (HG b c Hbc HGb).
Qed.

Lemma or_reads {State : Type} (l : nat) (F G : property State) :
    util_reads l F -> util_reads l G -> util_reads l (Or F G).
Proof.
    intros HF HG b c Hbc [HFb | HGb].
    - left. exact (HF b c Hbc HFb).
    - right. exact (HG b c Hbc HGb).
Qed.

Lemma implication_reads {State : Type} (l : nat) (F G : property State) :
    util_reads l F -> util_reads l G -> util_reads l (Implication F G).
Proof.
    intros HF HG b c Hbc HFG HFc.
    exact (HG b c Hbc (HFG (util_reads_flip l F HF b c Hbc HFc))).
Qed.

Lemma iff_reads {State : Type} (l : nat) (F G : property State) :
    util_reads l F -> util_reads l G -> util_reads l (Iff F G).
Proof.
    intros HF HG b c Hbc [HFG HGF]. split.
    - intros HFc. exact (HG b c Hbc (HFG (util_reads_flip l F HF b c Hbc HFc))).
    - intros HGc. exact (HF b c Hbc (HGF (util_reads_flip l G HG b c Hbc HGc))).
Qed.

Lemma exists_reads {State T : Type} (l : nat) (F : T -> property State) :
    (forall x : T, util_reads l (F x)) -> util_reads l (Exists F).
Proof.
    intros HF b c Hbc [x Hx]. exists x. exact (HF x b c Hbc Hx).
Qed.

Lemma forall_reads {State T : Type} (l : nat) (F : T -> property State) :
    (forall x : T, util_reads l (F x)) -> util_reads l (Forall F).
Proof.
    intros HF b c Hbc H x. exact (HF x b c Hbc (H x)).
Qed.

Lemma stutter_reads {State V : Type} (A : property State) (e : State -> V) :
    util_reads 2 A -> util_reads 2 (Stutter A e).
Proof.
    intros HA. exact (or_reads 2 A (Unchanged e) HA (unchanged_reads e)).
Qed.

Lemma nonstutter_reads {State V : Type} (A : property State) (e : State -> V) :
    util_reads 2 A -> util_reads 2 (NonStutter A e).
Proof.
    intros HA.
    exact (and_reads 2 A (Not (Unchanged e)) HA (not_reads 2 (Unchanged e) (unchanged_reads e))).
Qed.

Lemma enabled_reads {State : Type} (F : property State) :
    util_reads 1 (Enabled F).
Proof.
    intros b c Hbc [beh' [Hb HF]]. exists beh'. split.
    - rewrite Hb. exact (Hbc 0 (Nat.lt_0_succ 0)).
    - exact HF.
Qed.

Lemma lift1_stuttering_closed {State : Type} (p : State -> Prop) :
    util_stuttering_closed (Lift1 p).
Proof.
    exact (reads_stuttering_closed 1 (Lift1 p) (Nat.le_refl 1) (lift1_reads p)).
Qed.

Lemma enabled_stuttering_closed {State : Type} (F : property State) :
    util_stuttering_closed (Enabled F).
Proof.
    exact (reads_stuttering_closed 1 (Enabled F) (Nat.le_refl 1) (enabled_reads F)).
Qed.

Lemma always_stuttering_closed {State : Type} (F : property State) :
    util_stuttering_closed F -> util_stuttering_closed (Always F).
Proof.
    intros HF b c Hbc H k.
    destruct (stuttering_equivalent_suffix b c Hbc k) as [j Hjk].
    exact (HF _ _ Hjk (H j)).
Qed.

Lemma eventually_stuttering_closed {State : Type} (F : property State) :
    util_stuttering_closed F -> util_stuttering_closed (Eventually F).
Proof.
    intros HF b c Hbc [j Hj].
    destruct (stuttering_equivalent_suffix c b (stuttering_equivalent_sym b c Hbc) j)
        as [k Hkj].
    exists k. exact (util_closed_flip F HF _ _ Hkj Hj).
Qed.

#[local] Lemma util_suffix_agree2 {State : Type} (b c : behavior State) (j k : nat) :
    b j = c k -> b (S j) = c (S k) ->
        forall i : nat, i < 2 -> util_suffix b j i = util_suffix c k i.
Proof.
    intros H0 H1 i Hi. unfold util_suffix. destruct i as [| [| i]].
    - rewrite !Nat.add_0_r. exact H0.
    - rewrite !Nat.add_1_r. exact H1.
    - exfalso. lia.
Qed.

Lemma always_stutter_stuttering_closed {State V : Type} (A : property State) (e : State -> V) :
    util_reads 2 A -> util_stuttering_closed (Always (Stutter A e)).
Proof.
    intros HA b c Hbc H k.
    destruct (stuttering_equivalent_step b c Hbc k) as [E | [j [E0 E1]]].
    - right. unfold Unchanged, Lift2, util_suffix.
      rewrite Nat.add_0_r, Nat.add_1_r, E. reflexivity.
    - exact (stutter_reads A e HA (util_suffix b j) (util_suffix c k)
        (util_suffix_agree2 b c j k E0 E1) (H j)).
Qed.

Lemma eventually_nonstutter_stuttering_closed {State V : Type} (A : property State) (e : State -> V) :
    util_reads 2 A -> util_stuttering_closed (Eventually (NonStutter A e)).
Proof.
    intros HA b c Hbc [j Hj].
    destruct (stuttering_equivalent_step c b (stuttering_equivalent_sym b c Hbc) j)
        as [E | [k [E0 E1]]].
    - exfalso. destruct Hj as [_ HU]. apply HU. unfold Unchanged, Lift2, util_suffix.
      rewrite Nat.add_0_r, Nat.add_1_r, E. reflexivity.
    - exists k. exact (nonstutter_reads A e HA (util_suffix b j) (util_suffix c k)
        (util_suffix_agree2 b c j k (eq_sym E0) (eq_sym E1)) Hj).
Qed.

Lemma not_stuttering_closed {State : Type} (F : property State) :
    util_stuttering_closed F -> util_stuttering_closed (Not F).
Proof.
    intros HF b c Hbc HnF HFc. exact (HnF (util_closed_flip F HF b c Hbc HFc)).
Qed.

Lemma and_stuttering_closed {State : Type} (F G : property State) :
    util_stuttering_closed F -> util_stuttering_closed G -> util_stuttering_closed (And F G).
Proof.
    intros HF HG b c Hbc [HFb HGb]. split.
    - exact (HF b c Hbc HFb).
    - exact (HG b c Hbc HGb).
Qed.

Lemma or_stuttering_closed {State : Type} (F G : property State) :
    util_stuttering_closed F -> util_stuttering_closed G -> util_stuttering_closed (Or F G).
Proof.
    intros HF HG b c Hbc [HFb | HGb].
    - left. exact (HF b c Hbc HFb).
    - right. exact (HG b c Hbc HGb).
Qed.

Lemma implication_stuttering_closed {State : Type} (F G : property State) :
    util_stuttering_closed F -> util_stuttering_closed G ->
        util_stuttering_closed (Implication F G).
Proof.
    intros HF HG b c Hbc HFG HFc.
    exact (HG b c Hbc (HFG (util_closed_flip F HF b c Hbc HFc))).
Qed.

Lemma iff_stuttering_closed {State : Type} (F G : property State) :
    util_stuttering_closed F -> util_stuttering_closed G -> util_stuttering_closed (Iff F G).
Proof.
    intros HF HG b c Hbc [HFG HGF]. split.
    - intros HFc. exact (HG b c Hbc (HFG (util_closed_flip F HF b c Hbc HFc))).
    - intros HGc. exact (HF b c Hbc (HGF (util_closed_flip G HG b c Hbc HGc))).
Qed.

Lemma exists_stuttering_closed {State T : Type} (F : T -> property State) :
    (forall x : T, util_stuttering_closed (F x)) -> util_stuttering_closed (Exists F).
Proof.
    intros HF b c Hbc [x Hx]. exists x. exact (HF x b c Hbc Hx).
Qed.

Lemma forall_stuttering_closed {State T : Type} (F : T -> property State) :
    (forall x : T, util_stuttering_closed (F x)) -> util_stuttering_closed (Forall F).
Proof.
    intros HF b c Hbc H x. exact (HF x b c Hbc (H x)).
Qed.

Lemma ifthenelse_stuttering_closed {State : Type} (A F G : property State) :
    util_stuttering_closed A -> util_stuttering_closed F -> util_stuttering_closed G ->
        util_stuttering_closed (IfThenElse A F G).
Proof.
    intros HA HF HG.
    exact (and_stuttering_closed _ _ (implication_stuttering_closed A F HA HF)
        (implication_stuttering_closed (Not A) G (not_stuttering_closed A HA) HG)).
Qed.

Lemma leadsto_eventually_stuttering_closed {State : Type} (F G : property State) :
    util_stuttering_closed F -> util_stuttering_closed (Eventually G) ->
        util_stuttering_closed (LeadsTo F G).
Proof.
    intros HF HG. unfold LeadsTo. apply always_stuttering_closed.
    exact (implication_stuttering_closed F (Eventually G) HF HG).
Qed.

Lemma leadsto_stuttering_closed {State : Type} (F G : property State) :
    util_stuttering_closed F -> util_stuttering_closed G -> util_stuttering_closed (LeadsTo F G).
Proof.
    intros HF HG.
    exact (leadsto_eventually_stuttering_closed F G HF (eventually_stuttering_closed G HG)).
Qed.

Lemma weak_fairness_stuttering_closed {State V : Type} (e : State -> V) (A : property State) :
    util_reads 2 A -> util_stuttering_closed (WeakFairness e A).
Proof.
    intros HA. unfold WeakFairness. apply leadsto_eventually_stuttering_closed.
    - apply always_stuttering_closed. exact (enabled_stuttering_closed (NonStutter A e)).
    - exact (eventually_nonstutter_stuttering_closed A e HA).
Qed.

Lemma strong_fairness_stuttering_closed {State V : Type} (e : State -> V) (A : property State) :
    util_reads 2 A -> util_stuttering_closed (StrongFairness e A).
Proof.
    intros HA. unfold StrongFairness. apply leadsto_eventually_stuttering_closed.
    - apply always_stuttering_closed. apply eventually_stuttering_closed.
      exact (enabled_stuttering_closed (NonStutter A e)).
    - exact (eventually_nonstutter_stuttering_closed A e HA).
Qed.

Lemma refinement_mapping_stuttering_closed {State1 State2 : Type} (r : State1 -> State2) (F : property State1) :
    util_stuttering_closed (ExistentialRefinementMapping r F).
Proof.
    intros b c Hbc [beh1 [Hb HF]]. exists beh1. split.
    - exact (stuttering_equivalent_trans _ _ _ Hb Hbc).
    - exact HF.
Qed.

Lemma corefinement_mapping_stuttering_closed {State1 State2 : Type} (r : State1 -> State2) (F : property State1) :
    util_stuttering_closed (UniversalRefinementMapping r F).
Proof.
    intros b c Hbc H beh1 Hc.
    exact (H beh1 (stuttering_equivalent_trans _ _ _ Hc (stuttering_equivalent_sym _ _ Hbc))).
Qed.

Lemma refinement_mapping0_stuttering_closed {State1 State2 : Type} (R : State1 -> State2 -> Prop) (F : property State1) :
    util_stuttering_closed (ExistentialRefinementRelation R F).
Proof.
    intros b c Hbc [beh1 [Hb HF]]. exists beh1. split.
    - exact (stuttering_equivalent0_trans R beh1 b c Hb Hbc).
    - exact HF.
Qed.

Lemma corefinement_mapping0_stuttering_closed {State1 State2 : Type} (R : State1 -> State2 -> Prop) (F : property State1) :
    util_stuttering_closed (UniversalRefinementRelation R F).
Proof.
    intros b c Hbc H beh1 Hc.
    exact (H beh1 (stuttering_equivalent0_trans R beh1 c b Hc (stuttering_equivalent_sym _ _ Hbc))).
Qed.

#[local] Open Scope tla_scope.

Lemma property_implies_closure {State : Type} (F : property State) :
    valid (F \impl util_closure F).
Proof.
    intros beh HF n. right. exists beh.
    split; [exact HF | intros i _; reflexivity].
Qed.

Lemma util_tts_agree {State : Type} (P : property State)
        (beh c : behavior State) (n : nat) :
    (forall i : nat, i < n -> beh i = c i) ->
        util_tts P beh n -> util_tts P c n.
Proof.
    intros Hbc [Hn | [d [HP Hag]]]; [left; exact Hn |].
    right. exists d. split; [exact HP |].
    intros i Hi. rewrite (Hag i Hi). exact (Hbc i Hi).
Qed.

Lemma util_tts_mono {State : Type} (P Q : property State)
        (beh : behavior State) (n : nat) :
    (forall c : behavior State, P c -> util_closure Q c) ->
        util_tts P beh n -> util_tts Q beh n.
Proof.
    intros HPQ [Hn | [c [HP Hag]]]; [left; exact Hn |].
    exact (util_tts_agree Q c beh n Hag (HPQ c HP n)).
Qed.

Lemma util_tts_closure {State : Type} (F : property State)
        (beh : behavior State) (n : nat) :
    util_tts (util_closure F) beh n <-> util_tts F beh n.
Proof.
    split.
    - apply (util_tts_mono (util_closure F) F beh n). intros c HC. exact HC.
    - apply (util_tts_mono F (util_closure F) beh n). intros c HF.
        exact (property_implies_closure (util_closure F) c
                   (property_implies_closure F c HF)).
Qed.

Lemma util_tts_downward {State : Type} (F : property State)
        (beh : behavior State) (m n : nat) :
    m <= n -> util_tts F beh n -> util_tts F beh m.
Proof.
    intros Hmn [Hn | [c [HF Hag]]]; [left; lia | right].
    exists c. split; [exact HF | intros i Hi; apply Hag; lia].
Qed.

Definition util_trunc {State : Type} (beh : behavior State)
        (m : nat) : behavior State :=
    fun i => beh (Nat.min i m).

Lemma util_trunc_agree {State : Type} (beh : behavior State)
        (m i : nat) :
    i < S m -> util_trunc beh m i = beh i.
Proof.
    intros Hi. unfold util_trunc. rewrite (Nat.min_l i m); [reflexivity | lia].
Qed.

Lemma util_trunc_plus {State V : Type} (F : property State)
        (v : State -> V) (beh : behavior State) (m : nat) :
    util_tts F beh m ->
        util_plus_operator (util_closure F) v (util_trunc beh m).
Proof.
    intros HF. right. exists m. split.
    - intros k Hk. unfold util_trunc.
        rewrite (Nat.min_r k m Hk), (Nat.min_r (S k) m) by lia. reflexivity.
    - apply (proj2 (util_tts_closure F (util_trunc beh m) m)).
        apply (util_tts_agree F beh (util_trunc beh m) m); [| exact HF].
        intros i Hi. symmetry. apply util_trunc_agree. lia.
Qed.

Lemma util_tts_freeze {State : Type} (F : property State)
        (beh : behavior State) (m : nat) :
    util_stuttering_closed F ->
        util_tts F beh (S m) -> util_closure F (util_trunc beh m).
Proof.
    intros Hsc [Habs | [d [HF Hag]]]; [discriminate Habs |].
    intros p. right. exists (util_stutter_at d m p). split.
    - exact (Hsc d _ (stuttering_equivalent_stutter_at d m p) HF).
    - intros i Hi. unfold util_stutter_at, util_trunc.
        destruct (Nat.leb_spec i m) as [Him | Him].
        + rewrite (Nat.min_l i m Him). exact (Hag i (le_n_S i m Him)).
        + rewrite (Nat.min_r i m (Nat.lt_le_incl m i Him)).
            destruct (Nat.leb_spec i (m + p)); [| lia].
            exact (Hag m (Nat.lt_succ_diag_r m)).
Qed.

Lemma util_prefix_induction {State : Type} (E : property State)
        (E_ M_ : nat -> property State) (b : behavior State) :
    util_stuttering_closed E ->
    (forall (i : nat) (c : behavior State),
        util_closure E c /\ (forall j : nat, util_closure (M_ j) c) ->
            E_ i c) ->
    (forall m k : nat,
        util_tts (E_ k) b m -> util_closure (M_ k) (util_trunc b m)) ->
    forall m : nat, util_tts E b m -> forall j : nat, util_tts (E_ j) b m.
Proof.
    intros HscE Hyp1 Hstep m.
    induction m as [| m IH]; intros HEm j; [left; reflexivity |].
    right. exists (util_trunc b m). split.
    - apply (Hyp1 j (util_trunc b m)).
        split; [exact (util_tts_freeze E b m HscE HEm) |].
        intros k. apply (Hstep m k).
        exact (IH (util_tts_downward E b m (S m) (Nat.le_succ_diag_r m) HEm) k).
    - intros i Hi. apply util_trunc_agree. exact Hi.
Qed.

Definition util_level {State : Type} (l : nat) (P : property State) : Prop :=
    match l with
    | 0 | 1 | 2 => util_reads l P
    | _ => util_stuttering_closed P
    end.

Lemma level_reads {State : Type} (l : nat) (F : property State) :
    l <= 1 -> util_level l F -> util_reads l F.
Proof.
    intros Hl H. destruct l as [| [| l]]; [exact H | exact H | lia].
Qed.

Lemma with0_adjunction {S1 S2 : Type} (R : S1 -> S2 -> Prop)
        (F : property S1) (G : property S2) :
    valid ((\rrel R F) \impl G) <->
        valid (F \impl (\univ_rrel (fun t s => R s t) G)).
Proof.
    split.
    - intros H c HF h Hh. apply H. exists c. split; [| exact HF].
      exact (stuttering_equivalent0_flip _ h c Hh).
    - intros H h [c [Hse HF]].
      exact (H c HF h (stuttering_equivalent0_flip R c h Hse)).
Qed.
