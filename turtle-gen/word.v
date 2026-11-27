(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* word.v                                                                     *)
(* -------------------------------------------------------------------------- *)
(* The results of Sail's operations on unknown words, as integers.            *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require SailStdpp.TypeCasts.
Require SailStdpp.MachineWord.
Require SailStdpp.Operators_mwords.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.
Require Import turtle.gen.ev.
Require turtle.gen.bits.

#[local] Open Scope Z_scope.

Module B := stdpp.bitvector.definitions.
Module O := SailStdpp.Operators_mwords.
Module W := SailStdpp.MachineWord.MachineWord.
Module U := turtle.gen.bits.

(* ========================================================================== *)
(* Operations                                                                 *)
(* ========================================================================== *)

Lemma Z_to_bv_mod (n : N) (z : Z) :
        B.bv_unsigned (B.Z_to_bv n z) = z mod 2 ^ Z.of_N n.
Proof.
        reflexivity.
Qed.

Lemma add_vec_mod {n : Z} (x y : Values.mword n) :
        B.bv_unsigned (O.add_vec x y)
                = (B.bv_unsigned x + B.bv_unsigned y) mod 2 ^ Z.of_N (W.Z_idx n).
Proof.
        reflexivity.
Qed.

Lemma and_vec_land {n : Z} (x y : Values.mword n) :
        B.bv_unsigned (O.and_vec x y)
                = Z.land (B.bv_unsigned x) (B.bv_unsigned y).
Proof.
        reflexivity.
Qed.

Lemma sign_extend_mod {n : Z} (m : Z) (v : Values.mword n) :
        B.bv_unsigned (rv64d.sign_extend' m v)
                = B.bv_swrap (W.Z_idx n) (B.bv_unsigned v) mod 2 ^ Z.of_N (W.Z_idx m).
Proof.
        reflexivity.
Qed.

Lemma zero_extend_mod {n : Z} (m : Z) (v : Values.mword n) :
        B.bv_unsigned (rv64d_types.zero_extend' m v)
                = B.bv_unsigned v mod 2 ^ Z.of_N (W.Z_idx m).
Proof.
        reflexivity.
Qed.

(* All the bits of a word replaced. *)
Lemma update_subrange_all {n : Z} (v : Values.mword n) (m : Z) (w : Values.mword (m - (0 - 1))) :
        0 <= m ->
        n = m + 1 ->
                B.bv_unsigned (O.update_subrange_vec_dec v m 0 w) = B.bv_unsigned w.
Proof.
        intros Hm Hn. subst n.
        unfold O.update_subrange_vec_dec.
        rewrite U.autocast_unsigned by (unfold W.idx_Z, W.Z_idx; lia).
        rewrite U.to_word_idx_unsigned.
        change (B.bv_unsigned (W.update_slice v (W.Z_idx 0) w) = B.bv_unsigned w).
        unfold W.update_slice, W.slice.
        rewrite !B.bv_concat_unsigned', !B.bv_extract_unsigned.
        pose proof (U.mword_range w ltac:(lia)) as Hw.
        unfold B.bv_wrap, B.bv_modulus.
        replace (Z.of_N (W.Z_idx (m + 1) - W.Z_idx (m - (0 - 1)) - W.Z_idx 0)) with 0
                by (unfold W.Z_idx; lia).
        replace (Z.of_N (W.Z_idx 0)) with 0 by reflexivity.
        replace (Z.of_N (W.Z_idx (m + 1))) with (m + 1) by (unfold W.Z_idx; lia).
        replace (Z.of_N (W.Z_idx 0 + W.Z_idx (m - (0 - 1)))) with (m + 1) by (unfold W.Z_idx; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r, Z.shiftl_0_l, Z.lor_0_l, Z.shiftl_0_r, Z.lor_0_r.
        assert (Hw' : 0 <= B.bv_unsigned w < 2 ^ (m + 1))
                by (replace (m + 1) with (m - (0 - 1)) by lia; exact Hw).
        rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma cast_N_unsigned (m n : N) (E : m = n) (x : B.bv m) :
        B.bv_unsigned (TypeCasts.cast_N (T := B.bv) x E) = B.bv_unsigned x.
Proof.
        subst n. rewrite TypeCasts.cast_N_refl. reflexivity.
Qed.

(* ========================================================================== *)
(* Tactics                                                                    *)
(* ========================================================================== *)

(* `c` has no unknown in it. *)
Ltac word_is_closed c :=
        let T := type of c in
        assert_succeeds (
                let H := fresh in
                assert (H : T)
                        by (repeat match goal with X : _ |- _ => clear X end; exact c)).

(* An integer literal. *)
Ltac word_is_literal v :=
        lazymatch v with
                | Z0     => idtac
                | Zpos _ => idtac
                | Zneg _ => idtac
                end.

(* The closed parts of a result: immediates, constant words. *)
Ltac word_closed :=
        repeat match goal with
                | |- context [rv64d.sign_extend' ?m ?t] =>
                        word_is_closed t;
                        let v := eval vm_compute in (rv64d.sign_extend' m t) in
                        change (rv64d.sign_extend' m t) with v
                | |- context [rv64d.zeros' ?n] =>
                        let v := eval vm_compute in (rv64d.zeros' n) in
                        change (rv64d.zeros' n) with v
                | |- context [@O.update_subrange_vec_dec ?n ?v ?m ?o ?w] =>
                        word_is_closed m; word_is_closed o;
                        let m' := eval vm_compute in m in
                        let o' := eval vm_compute in o in
                        word_is_literal m'; word_is_literal o';
                        assert_fails (constr_eq m m'; constr_eq o o');
                        change (@O.update_subrange_vec_dec n v m o w) with (@O.update_subrange_vec_dec n v m' o' w)
                end.

(* A goal `w = Z_to_bv n e`, with `w` a result of Sail's operations. *)
Ltac word_value :=
        unfold rv64d.regval_into_reg, rv64d.regval_from_reg, rv64d.extend_value in *;
        apply B.bv_eq;
        unfold B.bv_signed;
        repeat match goal with
                | |- context [@B.bv_unsigned ?k (@O.add_vec ?n ?x ?y)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@O.add_vec n x y)
                                = (B.bv_unsigned x + B.bv_unsigned y) mod 2 ^ Z.of_N (W.Z_idx n))
                                by exact (add_vec_mod (n := n) x y);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@O.and_vec ?n ?x ?y)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@O.and_vec n x y)
                                = Z.land (B.bv_unsigned x) (B.bv_unsigned y))
                                by exact (and_vec_land (n := n) x y);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@rv64d.sign_extend' ?n ?m ?v)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@rv64d.sign_extend' n m v)
                                = B.bv_swrap (W.Z_idx n) (B.bv_unsigned v) mod 2 ^ Z.of_N (W.Z_idx m))
                                by exact (sign_extend_mod (n := n) m v);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@rv64d_types.zero_extend' ?n ?m ?v)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@rv64d_types.zero_extend' n m v)
                                = B.bv_unsigned v mod 2 ^ Z.of_N (W.Z_idx m))
                                by exact (zero_extend_mod (n := n) m v);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@O.update_subrange_vec_dec ?n ?v ?m 0 ?w)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@O.update_subrange_vec_dec n v m 0 w)
                                = B.bv_unsigned w)
                                by (apply update_subrange_all; vm_compute; congruence);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@TypeCasts.autocast Values.mword ?m ?n ?h ?x)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@TypeCasts.autocast Values.mword m n h x)
                                = B.bv_unsigned x)
                                by (apply U.autocast_unsigned; vm_compute; reflexivity);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@TypeCasts.cast_N ?T ?m ?n ?x ?e)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@TypeCasts.cast_N T m n x e) = B.bv_unsigned x)
                                by exact (cast_N_unsigned m n e x);
                        rewrite H; clear H
                | |- context [@B.bv_unsigned ?k (@B.Z_to_bv ?n ?z)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@B.Z_to_bv n z) = z mod 2 ^ Z.of_N n)
                                by exact (Z_to_bv_mod n z);
                        rewrite H; clear H
                end;
        repeat match goal with
                | |- context [B.bv_unsigned ?x] =>
                        word_is_closed x;
                        let v := eval vm_compute in (B.bv_unsigned x) in
                        word_is_literal v;
                        change (B.bv_unsigned x) with v
                | |- context [Z.of_N ?e] =>
                        word_is_closed e;
                        let v := eval vm_compute in (Z.of_N e) in
                        word_is_literal v;
                        change (Z.of_N e) with v
                | |- context [W.Z_idx ?n] =>
                        word_is_closed n;
                        let v := eval vm_compute in (W.Z_idx n) in
                        lazymatch v with N0 => idtac | Npos _ => idtac end;
                        change (W.Z_idx n) with v
                end.

(* ========================================================================== *)
(* Arithmetic                                                                 *)
(* ========================================================================== *)

Lemma mod_eq_by_diff (a b m k : Z) :
        a = b + k * m ->
                a mod m = b mod m.
Proof.
        intros ->. apply Z_mod_plus_full.
Qed.

(* `andi rd, rs1, 31` *)
Lemma land_31_mod (v : Z) :
        Z.land (v mod 2 ^ 64) 31 = Z.land v 31 mod 2 ^ 64.
Proof.
        change 31 with (Z.ones 5).
        rewrite !Z.land_ones by lia.
        rewrite (Z.mod_small (v mod 2 ^ 5) (2 ^ 64)) by (pose proof (Z.mod_pos_bound v (2 ^ 5)); lia).
        apply Z.mod_mod_divide. exists (2 ^ 59). reflexivity.
Qed.

(* A goal `a mod m = b mod m` of integers. *)
Ltac word_arith :=
        rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r;
        first
                [ lazymatch goal with |- ?a = ?a => reflexivity end
                | apply land_31_mod
                | (apply (mod_eq_by_diff _ _ _ 0); lia)
                | (apply (mod_eq_by_diff _ _ _ 1); lia)
                | (apply (mod_eq_by_diff _ _ _ (-1)); lia) ].

(* ========================================================================== *)
(* Conditions                                                                 *)
(* ========================================================================== *)

(* A condition on unknowns, from a hypothesis `a <> b`. *)
Ltac word_cond :=
        repeat match goal with
                | |- context [@O.eq_vec ?n ?x ?y] =>
                        rewrite (@U.eq_vec_unsigned n x y)
                end;
        repeat match goal with
                | |- context [@B.bv_unsigned ?k (@B.Z_to_bv ?n ?z)] =>
                        let H := fresh "H" in
                        assert (H : @B.bv_unsigned k (@B.Z_to_bv n z) = z mod 2 ^ Z.of_N n)
                                by exact (Z_to_bv_mod n z);
                        rewrite H; clear H
                end;
        repeat match goal with
                | |- context [B.bv_unsigned ?x] =>
                        word_is_closed x;
                        let v := eval vm_compute in (B.bv_unsigned x) in
                        word_is_literal v;
                        change (B.bv_unsigned x) with v
                | |- context [Z.of_N ?e] =>
                        word_is_closed e;
                        let v := eval vm_compute in (Z.of_N e) in
                        word_is_literal v;
                        change (Z.of_N e) with v
                end;
        repeat match goal with
                | H : ?a <> ?b |- context [Z.eqb ?a ?b] =>
                        rewrite (proj2 (Z.eqb_neq a b) H)
                end;
        cbn [negb andb orb].

(* ========================================================================== *)
(* A step on unknown values                                                   *)
(* ========================================================================== *)

(* The value of a register after the step, as `step_value`; an unknown value
        by `word_value` and `word_arith`. *)
Ltac step_value_sym :=
        rewrite ?lookup_if;
        repeat first
                [ rewrite lookup_set_same
                | rewrite lookup_set_other by reflexivity ];
        rewrite ?if_same;
        try word_cond;
        first
                [ lazymatch goal with |- ?a = ?a => reflexivity end
                | assumption
                | (lazymatch goal with |- ?a = ?b => word_is_closed a; word_is_closed b end;
                   apply definitions.bv_eq; vm_compute; reflexivity)
                | (word_closed; word_value; word_arith) ].

(* `step_tac`, for unknown values: conjunctions only are split, and no
        evaluation of a goal with an unknown. *)
Ltac step_tac_sym :=
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
        | split;
                [ only_tac
                | repeat match goal with |- _ /\ _ => split end; step_value_sym ] ].

(* ========================================================================== *)
(* Branches on an unknown register                                            *)
(* ========================================================================== *)

(* `bne rs1, zero, _` with `rs1` not 0: taken. *)
Lemma neq_zero_reg (c : Z) :
        c mod 2 ^ 64 <> 0 ->
                O.neq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 c)) (rv64d.regval_from_reg rv64d.zero_reg) = true.
Proof.
        intros H. unfold O.neq_vec, rv64d.regval_from_reg.
        rewrite U.eq_vec_unsigned.
        replace (B.bv_unsigned rv64d.zero_reg) with 0 by (vm_compute; reflexivity).
        match goal with
                | |- context [Z.eqb ?a 0] =>
                        destruct (Z.eqb_spec a 0) as [E | E]; [exfalso; apply H; exact E | reflexivity]
                end.
Qed.

(* `ev_extra` of ev.v, and a branch on an unknown register not 0, decided by
        a hypothesis. *)
Ltac ev_extra ::=
        first
                [ match goal with
                        | H : ?c mod 2 ^ 64 <> 0
                          |- context [O.neq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 ?c))
                                        (rv64d.regval_from_reg rv64d.zero_reg)] =>
                                ev_replace (neq_zero_reg c H)
                        end
                | progress (try unfold rv64d.is_aligned_paddr; try unfold rv64d.is_aligned_vaddr);
                  cbv beta iota ].
