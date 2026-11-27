(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Logic.Classical.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.gen.tla.
Require Import turtle.gen.base.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.main.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.
Require turtle.compat.sail.riscv.examples.fib.thm_2.

(* A step of the one that changes is a step of the other, both equivalent to
        a third. *)
Lemma stutter_step {State : Type} (b c o : behavior State) :
        util_stuttering_equivalent b o -> util_stuttering_equivalent c o ->
        forall n, c (S n) <> c n -> exists j, c n = b j /\ c (S n) = b (S j).
Proof.
        intros (f & g & Hfm & Hgm & Hfs & Hgs & Hb) (f' & g' & Hfm' & Hgm' & Hfs' & Hgs' & Hc) n Hne.
        destruct (util_monotone_surjective_cross f' Hfm' Hfs' n) as [k [Hk Hk1]].
        assert (Hg : g' (S k) = S (g' k)).
        { destruct (util_monotone_surjective_step g' Hgm' Hgs' k) as [H | H]; [| exact H].
          exfalso. apply Hne. rewrite <- Hk1, <- Hk, Hc, Hc, H. reflexivity. }
        destruct (util_monotone_surjective_cross g Hgm Hgs (g' k)) as [i [Hi Hi1]].
        assert (Hf : f (S i) = S (f i)).
        { destruct (util_monotone_surjective_step f Hfm Hfs i) as [H | H]; [| exact H].
          exfalso. apply Hne. rewrite <- Hk1, <- Hk, Hc, Hc, Hg, <- Hi1, <- Hi, <- Hb, <- Hb, H. reflexivity. }
        exists (f i). split.
        - rewrite Hb, Hi, <- Hc, Hk. reflexivity.
        - rewrite <- Hf, Hb, Hi1, <- Hg, <- Hc, Hk1. reflexivity.
Qed.

(* From any point of the one, a point of the other: the states of the other
        from there are states of the one from here, and a step of the other
        from there that changes is a step of the one from here. *)
Lemma stutter_tail {State : Type} (b c o : behavior State) :
        util_stuttering_equivalent b o -> util_stuttering_equivalent c o ->
        forall k, exists k',
                (forall i, exists j, b (k' + i) = c (k + j))
                /\ (forall m, k' <= m -> b (S m) <> b m ->
                        exists j, k <= j /\ c j = b m /\ c (S j) = b (S m)).
Proof.
        intros (f & g & Hfm & Hgm & Hfs & Hgs & Hb) (f' & g' & Hfm' & Hgm' & Hfs' & Hgs' & Hc) k.
        destruct (Hfs' k) as [n0 Hn0].
        destruct (util_monotone_surjective_cross g Hgm Hgs (g' n0)) as [n1 [Hn1 Hn1']].
        exists (f n1). split.
        - intros i. destruct (Hfs (f n1 + i)) as [n Hn].
          destruct (Nat.le_gt_cases n1 n) as [Hle | Hgt].
          + destruct (Hgs' (g n)) as [n' Hn'].
            destruct (Nat.le_gt_cases n0 n') as [Hle' | Hgt'].
            * exists (f' n' - k).
              replace (k + (f' n' - k)) with (f' n') by (pose proof (util_monotone_le f' Hfm' n0 n' Hle'); lia).
              rewrite <- Hn, Hb, Hc, Hn'. reflexivity.
            * exists 0. rewrite Nat.add_0_r.
              assert (E : g n = g n1).
              { pose proof (util_monotone_le g' Hgm' n' n0 ltac:(lia)). pose proof (util_monotone_le g Hgm n1 n Hle). lia. }
              rewrite <- Hn, Hb, E, Hn1, <- Hc, Hn0. reflexivity.
          + exists 0. rewrite Nat.add_0_r.
            assert (E : f n1 + i = f n1) by (pose proof (util_monotone_le f Hfm n n1 ltac:(lia)); lia).
            rewrite E, Hb, Hn1, <- Hc, Hn0. reflexivity.
        - intros m Hm Hne.
          destruct (util_monotone_surjective_cross f Hfm Hfs m) as [i [Hi Hi']].
          assert (Hgi : g (S i) = S (g i)).
          { destruct (util_monotone_surjective_step g Hgm Hgs i) as [E | E]; [| exact E].
            exfalso. apply Hne. rewrite <- Hi', <- Hi, Hb, Hb, E. reflexivity. }
          assert (Hin1 : n1 <= i).
          { destruct (Nat.le_gt_cases n1 i) as [H | H]; [exact H |].
            exfalso. pose proof (util_monotone_le f Hfm (S i) n1 H). lia. }
          destruct (util_monotone_surjective_cross g' Hgm' Hgs' (g i)) as [n2 [Hn2 Hn2']].
          assert (Hfn2 : f' (S n2) = S (f' n2)).
          { destruct (util_monotone_surjective_step f' Hfm' Hfs' n2) as [E | E]; [| exact E].
            exfalso. apply Hne.
            rewrite <- Hi', <- Hi, Hb, Hb, Hgi, <- Hn2', <- Hn2, <- Hc, <- Hc, E. reflexivity. }
          assert (Hn02 : n0 <= n2).
          { destruct (Nat.le_gt_cases n0 n2) as [H | H]; [exact H |].
            exfalso. pose proof (util_monotone_le g' Hgm' (S n2) n0 H). pose proof (util_monotone_le g Hgm n1 i Hin1). lia. }
          exists (f' n2). split; [| split].
          + rewrite <- Hn0. exact (util_monotone_le f' Hfm' n0 n2 Hn02).
          + rewrite Hc, Hn2, <- Hi, Hb. reflexivity.
          + rewrite <- Hfn2, Hc, Hn2', <- Hgi, <- Hi', Hb. reflexivity.
Qed.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* What `rm` shows                                                            *)
(* ========================================================================== *)

Lemma pc_internal_range s :
        pc_internal e_static s = true <-> 0x11000 < _pc_addr s < 0x1103c.
Proof.
        unfold pc_internal.
        change (_section_size (tl_fib_impl_sec e_static)) with 60.
        change (e_static "tl_fib"%string) with 0x11000.
        rewrite andb_true_iff, !Z.ltb_lt. lia.
Qed.

Lemma rm_some s x :
        rm e_static s = Some x ->
                x = s.
Proof.
        unfold rm. destruct (pc_internal e_static s); intros H; [discriminate H | congruence].
Qed.

Lemma rm_shown s :
        pc_internal e_static s = false ->
                rm e_static s = Some s.
Proof.
        intros H. unfold rm. rewrite H. reflexivity.
Qed.

(* The states of `D` are shown, and are not at the label of tl_fib. *)
Definition shown (D : state -> Prop) : Prop :=
        forall s, D s ->
                pc_internal e_static s = false
                /\ _pc_addr s <> e_static "tl_fib"%string.

(* A goal `shown D`, the PC of `D` in a closed range. *)
Ltac shown_tac :=
        let s := fresh "s" in
        let Hs := fresh "Hs" in
        let E := fresh "E" in
        intros s Hs;
        split;
        [ destruct (pc_internal e_static s) eqn:E;
                [ apply pc_internal_range in E; lia | reflexivity ]
        | change (e_static "tl_fib"%string) with 0x11000; lia ].

(* ========================================================================== *)
(* Weak fairness, at an index                                                 *)
(* ========================================================================== *)

Lemma wf_elim {St V : Type} (b : behavior St) (A : St -> St -> Prop) (v : St -> V) :
        (\wf (\lift2 A) \sub v) b ->
        forall k,
        (forall j, exists s', A (b (k + j)%nat) s' /\ v (b (k + j)%nat) <> v s') ->
                exists m,
                A (b (k + m)%nat) (b (S (k + m)))
                /\ v (b (k + m)%nat) <> v (b (S (k + m))).
Proof.
        intros H k Hen. specialize (H k). unfold Implication in H.
        destruct H as (m & HA & Hne).
        - intros j. destruct (Hen j) as (s' & Ha & Hv).
          exists (fun n => match n with O => b (k + j)%nat | S _ => s' end).
          unfold NonStutter, And, Not, Unchanged, Lift2, util_suffix.
          rewrite Nat.add_0_r. split; [reflexivity |]. split; assumption.
        - exists m. unfold Lift2, util_suffix in HA.
          unfold Not, Unchanged, Lift2, util_suffix in Hne.
          rewrite Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r in HA, Hne.
          exact (conj HA Hne).
Qed.

Lemma wf_intro {St V : Type} (b : behavior St) (A : St -> St -> Prop) (v : St -> V) :
        (forall k,
                (forall j, exists s', A (b (k + j)%nat) s' /\ v (b (k + j)%nat) <> v s') ->
                        exists m,
                        A (b (k + m)%nat) (b (S (k + m)))
                        /\ v (b (k + m)%nat) <> v (b (S (k + m)))) ->
                (\wf (\lift2 A) \sub v) b.
Proof.
        intros H k Hen.
        destruct (H k) as (m & HA & Hne).
        - intros j. destruct (Hen j) as (beh' & H0 & (HA & Hne)).
          exists (beh' 1%nat).
          unfold Lift2 in HA. unfold Not, Unchanged, Lift2 in Hne.
          rewrite H0 in HA, Hne. unfold util_suffix in HA, Hne.
          rewrite Nat.add_0_r in HA, Hne. exact (conj HA Hne).
        - exists m. split.
          + unfold Lift2, util_suffix.
            rewrite Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r. exact HA.
          + unfold Not, Unchanged, Lift2, util_suffix.
            rewrite Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r. exact Hne.
Qed.

(* ========================================================================== *)
(* Two behaviours with the same image                                         *)
(* ========================================================================== *)

Section robust.

Variables sigma sigma' : behavior state.
Variable tau : behavior (option state).
Hypothesis HE : E e_static sigma.
Hypothesis Hs : util_stuttering_equivalent (fun n => rm e_static (sigma n)) tau.
Hypothesis Hs' : util_stuttering_equivalent (fun n => rm e_static (sigma' n)) tau.

(* A step of `sigma` from a state of `D` ends in a state that is shown. *)
Lemma shown_next (D : state -> Prop) j :
        shown D ->
        D (sigma j) ->
                pc_internal e_static (sigma (S j)) = false.
Proof.
        intros HD Hd. destruct (HD _ Hd) as (Hv & Hl).
        destruct (pc_internal e_static (sigma (S j))) eqn:Ei; [| reflexivity].
        exfalso. apply Hl.
        pose proof (HE j) as H. unfold Lift2, util_suffix in H.
        rewrite Nat.add_0_r, Nat.add_1_r in H. destruct H as (Ha & _).
        apply Ha.
        - rewrite (rm_shown _ Hv). discriminate.
        - unfold rm. rewrite Ei. reflexivity.
Qed.

(* An action that speaks only of steps from `D` holds along `sigma'`. *)
Lemma next_robust (N : state -> state -> Prop) (D : state -> Prop) :
        shown D ->
        (forall s s', ~ D s -> N s s') ->
        ([][\lift2 N]_ exec_vars) sigma ->
                ([][\lift2 N]_ exec_vars) sigma'.
Proof.
        intros HD HN Hn. apply next_intro. intros i.
        destruct (excluded_middle (D (sigma' i))) as [Hd | Hd]; [| left; exact (HN _ _ Hd)].
        destruct (HD _ Hd) as (Hv & Hl).
        destruct (excluded_middle (rm e_static (sigma' (S i)) = rm e_static (sigma' i))) as [Heq | Hne].
        - right. rewrite (rm_shown _ Hv) in Heq. exact (rm_some _ _ Heq).
        - destruct (stutter_step _ _ _ Hs Hs' i Hne) as (j & Hj & Hj').
          cbv beta in Hj, Hj'.
          rewrite (rm_shown _ Hv) in Hj. symmetry in Hj. apply rm_some in Hj.
          assert (Hd' : D (sigma j)) by (rewrite <- Hj; exact Hd).
          pose proof (shown_next D j HD Hd') as Hv'.
          rewrite (rm_shown _ Hv') in Hj'. apply rm_some in Hj'.
          rewrite Hj, <- Hj'. exact (next_at sigma N Hn j).
Qed.

(* A fair action whose steps are from `D` is fair along `sigma'`. *)
Lemma wf_robust (A : state -> state -> Prop) (D : state -> Prop) :
        shown D ->
        (forall s s', A s s' -> D s) ->
        (\wf (\lift2 A) \sub exec_vars) sigma ->
                (\wf (\lift2 A) \sub exec_vars) sigma'.
Proof.
        intros HD HA Hwf. apply wf_intro. intros k Hen.
        assert (HDk : forall j, D (sigma' (k + j)%nat)).
        { intros j. destruct (Hen j) as (s' & Ha & _). exact (HA _ _ Ha). }
        destruct (stutter_tail _ _ _ Hs Hs' k) as (k' & Ht1 & Ht2).
        (* the states of `sigma` from `k'` are states of `sigma'` from `k` *)
        assert (Hst : forall i, exists j, sigma (k' + i)%nat = sigma' (k + j)%nat).
        { intros i. destruct (Ht1 i) as (j & Hj). exists j. cbv beta in Hj.
          rewrite (rm_shown _ (proj1 (HD _ (HDk j)))) in Hj.
          symmetry. exact (rm_some _ _ Hj). }
        destruct (wf_elim sigma A exec_vars Hwf k') as (m & Ham & Hne).
        { intros i. destruct (Hst i) as (j & Hj). rewrite Hj. exact (Hen j). }
        unfold exec_vars in Hne.
        destruct (Hst m) as (j0 & Hj0).
        assert (Hdm : D (sigma (k' + m)%nat)) by (rewrite Hj0; exact (HDk j0)).
        pose proof (proj1 (HD _ Hdm)) as Hv.
        pose proof (shown_next D _ HD Hdm) as Hv'.
        assert (Hb : rm e_static (sigma (S (k' + m))) <> rm e_static (sigma (k' + m)%nat)).
        { rewrite (rm_shown _ Hv), (rm_shown _ Hv'). intros Heq. apply Hne.
          injection Heq as Heq. symmetry. exact Heq. }
        destruct (Ht2 (k' + m)%nat ltac:(lia) Hb) as (j & Hkj & Hj & Hj').
        cbv beta in Hj, Hj'.
        rewrite (rm_shown _ Hv) in Hj. apply rm_some in Hj.
        rewrite (rm_shown _ Hv') in Hj'. apply rm_some in Hj'.
        exists (j - k)%nat. replace (k + (j - k))%nat with j by lia.
        rewrite <- Hj, <- Hj'. unfold exec_vars. exact (conj Ham Hne).
Qed.

End robust.

(* ========================================================================== *)
(* thm_2_1                                                                    *)
(* ========================================================================== *)

Theorem thm_2_1 :
        valid ((\rmap (rm e_static) (E e_static \land unsafe_libc e_static))
                        \impl (\univ_rmap (rm e_static) (unsafe_libc e_static))).
Proof.
        intros tau (sigma & Hs & HE & Hlibc) sigma' Hs'.
        destruct Hlibc as ((Hp & Hpw) & He & (Hg & Hgw)).
        assert (Dp : shown (fun s => _pc_addr s = e_static "printf"%string)).
        { change (e_static "printf"%string) with 0x14000. shown_tac. }
        assert (De : shown (fun s => _pc_addr s = e_static "exit"%string)).
        { change (e_static "exit"%string) with 0x14100. shown_tac. }
        assert (Dg : shown (fun s => _pc_addr s = e_static "getrandom"%string)).
        { change (e_static "getrandom"%string) with 0x14200. shown_tac. }
        split; [split | split; [| split]].
        - apply (next_robust sigma sigma' tau HE Hs Hs' _ _ Dp); [| exact Hp].
          intros s s' Hd Hpc. exfalso. exact (Hd Hpc).
        - apply (wf_robust sigma sigma' tau HE Hs Hs' _ _ Dp); [| exact Hpw].
          intros s s' (Hpc & _). exact Hpc.
        - apply (next_robust sigma sigma' tau HE Hs Hs' _ _ De); [| exact He].
          intros s s' Hd Hpc. exfalso. exact (Hd Hpc).
        - apply (next_robust sigma sigma' tau HE Hs Hs' _ _ Dg); [| exact Hg].
          intros s s' Hd Hpc. exfalso. exact (Hd Hpc).
        - apply (wf_robust sigma sigma' tau HE Hs Hs' _ _ Dg); [| exact Hgw].
          intros s s' (Hpc & _). exact Hpc.
Qed.

(* The statement of thm_2.v. *)
Definition thm_2_1_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_2.thm_2_1 in exact t) :=
        thm_2_1.

Print Assumptions thm_2_1.

(* ========================================================================== *)
(* thm_2_2                                                                    *)
(* ========================================================================== *)

Theorem thm_2_2 :
        valid ((\rmap (rm e_static) (E e_static \land exec_static main_s))
                        \impl (\univ_rmap (rm e_static) (exec_static main_s))).
Proof.
        intros tau (sigma & Hs & HE & Hex) sigma' Hs'.
        destruct Hex as (I1 & I2 & I4 & Is & Hn & Hw).
        destruct Is as ((_ & Ism) & Isf).
        destruct Hn as ((_ & Hnm) & Hnf).
        destruct Hw as ((_ & Hwm) & Hwf).
        (* the first states are the same *)
        assert (H0 : sigma' 0%nat = sigma 0%nat).
        { pose proof (stuttering_equivalent_head _ _ Hs) as E1. pose proof (stuttering_equivalent_head _ _ Hs') as E2.
          cbv beta in E1, E2. rewrite <- E1 in E2.
          assert (Hv : pc_internal e_static (sigma 0%nat) = false).
          { destruct (pc_internal e_static (sigma 0%nat)) eqn:E; [| reflexivity].
            apply pc_internal_range in E.
            assert (Hpc : _pc_addr (sigma 0%nat) = 0x10000) by exact I2.
            lia. }
          rewrite (rm_shown _ Hv) in E2. symmetry. exact (rm_some _ _ E2). }
        assert (Dm : shown (at_pc (main_sec e_static) (e_static "main"%string))).
        { unfold at_pc.
          change (_section_size (main_sec e_static)) with 128.
          change (e_static "main"%string) with 0x10000. shown_tac. }
        assert (Df : shown (at_pc _tl_fmt_sec (e_static ".tl_fmt"%string))).
        { unfold at_pc.
          change (_section_size _tl_fmt_sec) with 5.
          change (e_static ".tl_fmt"%string) with 0x100000. shown_tac. }
        split; [unfold Lift1; rewrite H0; exact I1 |].
        split; [unfold exec_init_pc, Lift1; rewrite H0; exact I2 |].
        split; [unfold exec_init_sp, Lift1; rewrite H0; exact I4 |].
        split; [| split].
        - split; [split; [exact I |] |].
          + unfold Lift1. rewrite H0. exact Ism.
          + unfold Lift1. rewrite H0. exact Isf.
        - split; [split; [exact I |] |].
          + apply (next_robust sigma sigma' tau HE Hs Hs' _ _ Dm); [| exact Hnm].
            intros s s' Hd Hat. exfalso. exact (Hd Hat).
          + apply (next_robust sigma sigma' tau HE Hs Hs' _ _ Df); [| exact Hnf].
            intros s s' Hd Hat. exfalso. exact (Hd Hat).
        - split; [split; [exact I |] |].
          + apply (wf_robust sigma sigma' tau HE Hs Hs' _ _ Dm); [| exact Hwm].
            intros s s' (Hat & _). exact Hat.
          + apply (wf_robust sigma sigma' tau HE Hs Hs' _ _ Df); [| exact Hwf].
            intros s s' (Hat & _). exact Hat.
Qed.

(* The statement of thm_2.v. *)
Definition thm_2_2_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_2.thm_2_2 in exact t) :=
        thm_2_2.

Print Assumptions thm_2_2.
