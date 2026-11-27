(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* bits.v                                                                     *)
(* -------------------------------------------------------------------------- *)
(* Sail's operations on machine words, as integers.                           *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require SailStdpp.TypeCasts.
Require SailStdpp.MachineWord.
Require SailStdpp.Operators_mwords.
Require Riscv.rv64d.

#[local] Open Scope Z_scope.

Module B := stdpp.bitvector.definitions.
Module O := SailStdpp.Operators_mwords.
Module W := SailStdpp.MachineWord.MachineWord.

(* ========================================================================== *)
(* Words                                                                      *)
(* ========================================================================== *)

Lemma mword_eq {n : Z} (x y : Values.mword n) :
        B.bv_unsigned x = B.bv_unsigned y ->
                x = y.
Proof.
        apply B.bv_eq.
Qed.

Lemma mword_range {n : Z} (x : Values.mword n) :
        0 <= n ->
                0 <= B.bv_unsigned x < 2 ^ n.
Proof.
        intros Hn. pose proof (B.bv_unsigned_in_range _ x) as H.
        unfold B.bv_modulus in H. unfold W.Z_idx in H.
        rewrite Z2N.id in H by exact Hn. exact H.
Qed.

(* ========================================================================== *)
(* Casts                                                                      *)
(* ========================================================================== *)

Lemma cast_Z_unsigned (m n : Z) (E : m = n) (x : Values.mword m) :
        B.bv_unsigned (TypeCasts.cast_Z x E) = B.bv_unsigned x.
Proof.
        subst n. rewrite TypeCasts.cast_Z_refl. reflexivity.
Qed.

Lemma autocast_unsigned (m n : Z) H (x : Values.mword m) :
        m = n ->
                B.bv_unsigned (@TypeCasts.autocast Values.mword m n H x) = B.bv_unsigned x.
Proof.
        intros E. rewrite (TypeCasts.autocast_eq x E). apply cast_Z_unsigned.
Qed.

Lemma to_word_idx_unsigned (n : N) (w : W.word n) :
        B.bv_unsigned (Values.to_word_idx w) = B.bv_unsigned w.
Proof.
        change (Values.to_word_idx w) with (TypeCasts.cast_N w (W.Z_idx_Z n)).
        generalize (W.Z_idx_Z n). generalize (W.Z_idx (W.idx_Z n)).
        intros k e. subst k. rewrite TypeCasts.cast_N_refl. reflexivity.
Qed.

(* ========================================================================== *)
(* Operations                                                                 *)
(* ========================================================================== *)

Lemma uint_unsigned {n : Z} (x : Values.mword n) :
        O.uint x = B.bv_unsigned x.
Proof.
        change (O.uint x) with (Z.of_N (Z.to_N (B.bv_unsigned x))).
        pose proof (B.bv_unsigned_in_range _ x). lia.
Qed.

Lemma subrange_unsigned {n : Z} (v : Values.mword n) (m o : Z) :
        0 <= o ->
        o <= m ->
                B.bv_unsigned (O.subrange_vec_dec v m o)
                        = (B.bv_unsigned v / 2 ^ o) mod 2 ^ (m - o + 1).
Proof.
        intros Ho Hm. unfold O.subrange_vec_dec.
        rewrite autocast_unsigned.
        - rewrite to_word_idx_unsigned. unfold W.slice.
          rewrite B.bv_extract_unsigned. unfold B.bv_wrap, B.bv_modulus, W.Z_idx.
          rewrite !Z2N.id by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
        - unfold W.idx_Z, W.Z_idx. lia.
Qed.

Lemma concat_unsigned {a b : Z} (w : Values.mword a) (v : Values.mword b) :
        0 <= a ->
        0 <= b ->
                B.bv_unsigned (O.concat_vec w v)
                        = B.bv_unsigned w * 2 ^ b + B.bv_unsigned v.
Proof.
        intros Ha Hb. unfold O.concat_vec.
        rewrite autocast_unsigned.
        - rewrite to_word_idx_unsigned.
          change (B.bv_unsigned (B.bv_concat (W.idx_add (W.Z_idx a) (W.Z_idx b)) w v)
                  = B.bv_unsigned w * 2 ^ b + B.bv_unsigned v).
          rewrite B.bv_concat_unsigned by reflexivity.
          replace (Z.of_N (W.Z_idx b)) with b by (unfold W.Z_idx; lia).
          pose proof (mword_range v Hb) as Hv.
          rewrite Z.shiftl_mul_pow2 by lia.
          assert (Hl : Z.land (B.bv_unsigned w * 2 ^ b) (B.bv_unsigned v) = 0).
          { apply Z.bits_inj'. intros k Hk.
            rewrite Z.land_spec, Z.bits_0.
            destruct (Z.lt_ge_cases k b) as [Hlt | Hge].
            - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
            - destruct (Z.eq_dec (B.bv_unsigned v) 0) as [E0 | Hne].
              { rewrite E0, Z.bits_0. apply Bool.andb_false_r. }
              rewrite (Z.bits_above_log2 (B.bv_unsigned v) k).
              + apply Bool.andb_false_r.
              + lia.
              + apply Z.log2_lt_pow2; [lia |].
                apply Z.lt_le_trans with (2 ^ b); [lia |].
                apply Z.pow_le_mono_r; lia. }
          rewrite <- (Z.lxor_lor _ _ Hl), <- (Z.add_nocarry_lxor _ _ Hl). reflexivity.
        - unfold W.idx_Z, W.Z_idx, W.idx_add. lia.
Qed.

Lemma eq_vec_unsigned {n : Z} (x y : Values.mword n) :
        O.eq_vec x y = (B.bv_unsigned x =? B.bv_unsigned y).
Proof.
        destruct (B.bv_unsigned x =? B.bv_unsigned y) eqn:E.
        - apply O.eq_vec_true_iff. apply mword_eq. apply Z.eqb_eq. exact E.
        - apply O.eq_vec_false_iff. intros H. subst y.
          rewrite Z.eqb_refl in E. discriminate E.
Qed.

Lemma zero_extend_unsigned {a : Z} (n : Z) (v : Values.mword a) :
        0 <= a ->
        a <= n ->
                B.bv_unsigned (O.zero_extend v n) = B.bv_unsigned v.
Proof.
        intros Ha Hn. unfold O.zero_extend, O.extz_vec, W.zero_extend.
        apply B.bv_zero_extend_unsigned. unfold W.Z_idx. lia.
Qed.

(* ========================================================================== *)
(* Tactics                                                                    *)
(* ========================================================================== *)

(* Rewrite the integer of one operation. The equation is stated on the very
        term of the goal: `rewrite` with the lemmas above misses when the size
        of a word is written in another way (32 against 20 + (5 + 7)). *)
Ltac u_step :=
        match goal with
                | |- context [@B.bv_unsigned ?k (@O.subrange_vec_dec ?n ?v ?m ?o)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@O.subrange_vec_dec n v m o)
                                = (B.bv_unsigned v / 2 ^ o) mod 2 ^ (m - o + 1))
                                by (refine (@subrange_unsigned n v m o _ _); lia);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@O.concat_vec ?a ?b ?w ?v)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@O.concat_vec a b w v)
                                = B.bv_unsigned w * 2 ^ b + B.bv_unsigned v)
                                by (refine (@concat_unsigned a b w v _ _); lia);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@O.zero_extend ?a ?v ?n)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@O.zero_extend a v n)
                                = B.bv_unsigned v)
                                by (refine (@zero_extend_unsigned a n v _ _); lia);
                        rewrite H; clear H
                | |- context [@O.eq_vec ?n ?x ?y] =>
                        rewrite (@eq_vec_unsigned n x y)
                | |- context [@O.uint ?n ?x] =>
                        rewrite (@uint_unsigned n x)
                end.

(* ========================================================================== *)
(* Fields                                                                     *)
(* ========================================================================== *)

(* Replacing bit 3 of senvcfg (SSE) keeps bits 33 and 32 (PMM). *)
Lemma senvcfg_pmm_update_sse (v : Values.mword 64) (x : Values.mword 1) :
        rv64d._get_SEnvcfg_PMM (rv64d._update_SEnvcfg_SSE v x) = rv64d._get_SEnvcfg_PMM v.
Proof.
        apply mword_eq. unfold rv64d._get_SEnvcfg_PMM, rv64d._update_SEnvcfg_SSE.
        do 2 u_step.
        unfold O.update_subrange_vec_dec.
        rewrite autocast_unsigned by (unfold W.idx_Z, W.Z_idx; lia).
        rewrite to_word_idx_unsigned. unfold W.update_slice, W.slice.
        rewrite !B.bv_concat_unsigned', !B.bv_extract_unsigned.
        pose proof (mword_range v ltac:(lia)) as Hv.
        set (A := B.bv_unsigned v) in *.
        unfold B.bv_wrap, B.bv_modulus.
        repeat match goal with
                | |- context [Z.of_N ?e] =>
                        let n := eval vm_compute in (Z.of_N e) in
                        change (Z.of_N e) with n
                end.
        rewrite <- !Z.shiftr_div_pow2 by lia.
        change (2 ^ (33 - 32 + 1)) with (2 ^ 2).
        rewrite <- !Z.land_ones by lia.
        apply Z.bits_inj'. intros k Hk.
        rewrite !Z.land_spec, !Z.shiftr_spec by lia.
        destruct (Z.lt_ge_cases k 2) as [Hk2 | Hk2];
                [ | rewrite !Z.ones_spec_high by lia; rewrite !Bool.andb_false_r; reflexivity ].
        rewrite Z.ones_spec_low by lia. rewrite !Bool.andb_true_r.
        rewrite Z.land_spec, (Z.ones_spec_low 64) by lia. rewrite Bool.andb_true_r.
        rewrite Z.lor_spec, Z.shiftl_spec by lia.
        rewrite Z.land_spec, (Z.ones_spec_low 60) by lia. rewrite Bool.andb_true_r.
        rewrite Z.shiftr_spec by lia.
        replace (k + 32 - 4 + 4) with (k + 32) by lia.
        rewrite Z.land_spec, (Z.ones_spec_high 4) by lia.
        rewrite Bool.andb_false_r, Bool.orb_false_r.
        reflexivity.
Qed.
