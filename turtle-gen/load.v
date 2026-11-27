(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* load.v                                                                     *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.

Require stdpp.bitvector.definitions.

Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.gen.frame.

#[local] Open Scope Z_scope.

(* ========================================================================== *)
(* Instructions                                                               *)
(* ========================================================================== *)

(* An instruction in memory is the word of `_instr_to_bv`. *)
Lemma instr_mem_word ins addr s :
        st_mem_read s (definitions.Z_to_bv 64 addr) 4 = _instr_to_bv ins ->
                mem_word addr (definitions.bv_unsigned (_instr_to_bv ins)) s.
Proof.
        intros H. unfold mem_word. unfold st_mem_read in H. rewrite H.
        symmetry. apply definitions.Z_to_bv_bv_unsigned.
Qed.

(* `H : st_mem_read s a 4 = _instr_to_bv ins` becomes the word of `ins`. *)
Ltac instr_word H :=
        lazymatch type of H with
                | st_mem_read ?s (definitions.Z_to_bv 64 ?addr) 4 = _instr_to_bv ?ins =>
                        apply instr_mem_word in H;
                        lazymatch type of H with
                                | mem_word ?a ?w _ =>
                                        let a' := eval vm_compute in a in
                                        let w' := eval vm_compute in w in
                                        change (mem_word a' w' s) in H
                                end
                end.

(* A goal `st_mem_read s a 4 = _instr_to_bv ins` whose memory is closed. *)
Ltac instr_intro :=
        lazymatch goal with
                | |- st_mem_read _ _ 4 = _instr_to_bv _ =>
                        vm_compute;
                        reflexivity
                end.

(* ========================================================================== *)
(* Memory outside a range                                                     *)
(* ========================================================================== *)

(* The memory is kept outside `lo` to `hi`. *)
Definition mem_kept (lo hi : Z) (s s' : state) : Prop :=
        forall a,
                ~ (lo <= definitions.bv_unsigned a < hi) ->
                        st_mem s' a = st_mem s a.

Lemma mem_word_kept lo hi a w s s' :
        mem_kept lo hi s s' ->
        0 <= a ->
        a + 4 <= 2 ^ 64 ->
        a + 4 <= lo \/ hi <= a ->
        mem_word a w s ->
                mem_word a w s'.
Proof.
        intros Hm H0 H1 Ha. unfold mem_word, _mem_read. intros <-.
        f_equal. f_equal. apply map_ext_in. intros b Hb.
        change (definitions.bv_seq (definitions.Z_to_bv 64 a) (Z.of_N 4))
                with (definitions.bv_add_Z (definitions.Z_to_bv 64 a) 0
                        :: definitions.bv_add_Z (definitions.Z_to_bv 64 a) 1
                        :: definitions.bv_add_Z (definitions.Z_to_bv 64 a) 2
                        :: definitions.bv_add_Z (definitions.Z_to_bv 64 a) 3
                        :: nil) in Hb.
        apply Hm.
        destruct Hb as [<- | [<- | [<- | [<- | [ ]]]]];
                rewrite definitions.bv_add_Z_unsigned, definitions.Z_to_bv_unsigned;
                rewrite (definitions.bv_wrap_small 64 a)
                        by (unfold definitions.bv_modulus; cbn; lia);
                rewrite definitions.bv_wrap_small
                        by (unfold definitions.bv_modulus; cbn; lia);
                lia.
Qed.

(* ========================================================================== *)
(* Bytes                                                                      *)
(* ========================================================================== *)

(* A section of bytes stays in memory where the memory stays. *)
Lemma init_s_data_bytes stmnts addr s s' :
        0 <= addr ->
        addr + Z.of_nat (List.length stmnts) <= 2 ^ 64 ->
        (forall a,
                addr <= definitions.bv_unsigned a < addr + Z.of_nat (List.length stmnts) ->
                        st_mem s' a = st_mem s a) ->
        _init_s_data stmnts addr s ->
                _init_s_data stmnts addr s'.
Proof.
        revert addr. induction stmnts as [| [b] stmnts IH]; intros addr H0 H1 Hm H.
        - exact I.
        - cbn [List.length] in *. destruct H as (Ht & Hb). split.
          + apply IH; [lia | lia | | exact Ht]. intros a Ha. apply Hm. lia.
          + rewrite <- Hb. unfold st_mem_read, _mem_read.
            change (definitions.bv_seq (definitions.Z_to_bv 64 addr) (Z.of_N 1))
                    with (definitions.bv_add_Z (definitions.Z_to_bv 64 addr) 0 :: nil).
            cbn [map]. rewrite Hm; [reflexivity |].
            rewrite definitions.bv_add_Z_unsigned, definitions.Z_to_bv_unsigned.
            rewrite (definitions.bv_wrap_small 64 addr)
                    by (unfold definitions.bv_modulus; cbn; lia).
            rewrite definitions.bv_wrap_small
                    by (unfold definitions.bv_modulus; cbn; lia).
            lia.
Qed.

Lemma exec_init_src_1_data_kept lo hi stmnts addr s s' :
        mem_kept lo hi s s' ->
        0 <= addr ->
        addr + _section_size (s_data stmnts) <= 2 ^ 64 ->
        addr + _section_size (s_data stmnts) <= lo \/ hi <= addr ->
        exec_init_src_1 (s_data stmnts) addr s ->
                exec_init_src_1 (s_data stmnts) addr s'.
Proof.
        cbn [_section_size exec_init_src_1]. intros Hm H0 H1 Ha.
        apply init_s_data_bytes; [lia | lia |].
        intros a Hr. apply Hm. lia.
Qed.
