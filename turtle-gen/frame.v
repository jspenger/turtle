(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* frame.v                                                                    *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require Riscv.rv64d_types.

Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.conf.preserve_conf.
Require Import turtle.gen.eval.

#[local] Open Scope Z_scope.

Module T := rv64d_types.

(* ========================================================================== *)
(* Registers                                                                  *)
(* ========================================================================== *)

Lemma register_beq_eq (r r' : T.register) :
        T.register_beq r r' = true ->
                r = r'.
Proof.
        destruct r, r'; cbn; intros H; try discriminate H; f_equal.
        all: first
                [ apply T.register_HartState_beq_iff
                | apply T.register_Privilege_beq_iff
                | apply T.register_bitvector_1_beq_iff
                | apply T.register_bitvector_128_beq_iff
                | apply T.register_bitvector_192_beq_iff
                | apply T.register_bitvector_3_beq_iff
                | apply T.register_bitvector_32_beq_iff
                | apply T.register_bitvector_320_beq_iff
                | apply T.register_bitvector_4_beq_iff
                | apply T.register_bitvector_5_beq_iff
                | apply T.register_bitvector_64_beq_iff
                | apply T.register_bitvector_704_beq_iff
                | apply T.register_bitvector_exp_8_beq_iff
                | apply T.register_bool_beq_iff
                | apply T.register_list_PMA_Region_beq_iff
                | apply T.register_option_bitvector_64_beq_iff
                | apply T.register_vector_32_bitvector_64_beq_iff
                | apply T.register_vector_64_bitvector_64_beq_iff
                | apply T.register_vector_64_bitvector_8_beq_iff
                | apply T.register_vector_64_option_TLB_Entry_beq_iff ].
        all: exact H.
Qed.

Definition reg_in (l : list T.register) (r : T.register) : bool :=
        existsb (T.register_beq r) l.

Lemma lookup_if r (c : bool) (a b : state) :
        T.register_lookup r (st_regs (if c then a else b))
                = if c then T.register_lookup r (st_regs a) else T.register_lookup r (st_regs b).
Proof.
        destruct c; reflexivity.
Qed.

(* ========================================================================== *)
(* Frames                                                                     *)
(* ========================================================================== *)

(* `s'` is `s` but for the registers of `l`. *)
Definition only (l : list T.register) (s s' : state) : Prop :=
        st_mem s' = st_mem s
        /\ forall r, reg_in l r = false ->
                T.register_lookup r (st_regs s') = T.register_lookup r (st_regs s).

Lemma only_refl l s :
        only l s s.
Proof.
        split; reflexivity.
Qed.

Lemma only_set_reg l r v s s' :
        reg_in l r = true ->
        only l s s' ->
                only l s (set_reg r v s').
Proof.
        intros Hr (Hm & Hl). split.
        - exact Hm.
        - intros r0 H0. rewrite <- (Hl r0 H0).
          apply lookup_set_other.
          destruct (T.register_beq r0 r) eqn:E; [| reflexivity].
          apply register_beq_eq in E. subst r0. rewrite Hr in H0. discriminate H0.
Qed.

Lemma only_if l (c : bool) s a b :
        only l s a ->
        only l s b ->
                only l s (if c then a else b).
Proof.
        destruct c; intros Ha Hb; assumption.
Qed.

(* The state of a goal `only l s s'` is `s` under writes and conditions. *)
Ltac only_tac :=
        repeat first
                [ apply only_if
                | apply only_set_reg; [ reflexivity | ]
                | apply only_refl ].

(* ========================================================================== *)
(* preserve_conf                                                              *)
(* ========================================================================== *)

(* The registers that `preserve_conf` speaks of. *)
Definition preserve_conf_regs : list T.register :=
        T.R_Privilege T.cur_privilege ::
        T.R_bitvector_64 T.misa ::
        T.R_bitvector_64 T.mstatus ::
        T.R_bitvector_64 T.mie ::
        T.R_bitvector_64 T.satp ::
        T.R_bitvector_64 T.senvcfg ::
        T.R_vector_64_bitvector_8 T.pmpcfg_n ::
        T.R_vector_64_bitvector_64 T.pmpaddr_n ::
        T.R_bitvector_1 T.elp ::
        T.R_HartState T.hart_state ::
        T.R_list_PMA_Region T.pma_regions ::
        T.R_option_bitvector_64 T.htif_tohost_base ::
        nil.

(* A change of other registers preserves the conf. *)
Lemma preserve_conf_only l s s' :
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs = true ->
        only l s s' ->
                preserve_conf s s'.
Proof.
        intros Hl (_ & Ho).
        assert (Hr : forall r, In r preserve_conf_regs ->
                T.register_lookup r (st_regs s') = T.register_lookup r (st_regs s)).
        { intros r Hin. apply Ho.
          rewrite forallb_forall in Hl. specialize (Hl r Hin).
          destruct (reg_in l r); [discriminate Hl | reflexivity]. }
        unfold preserve_conf, st_regs_read, _regs_read.
        rewrite !Hr by (cbn; tauto).
        repeat split.
Qed.

(* The registers of `preserve_conf` but the landing pad. *)
Definition preserve_conf_regs_elp : list T.register :=
        T.R_Privilege T.cur_privilege ::
        T.R_bitvector_64 T.misa ::
        T.R_bitvector_64 T.mstatus ::
        T.R_bitvector_64 T.mie ::
        T.R_bitvector_64 T.satp ::
        T.R_bitvector_64 T.senvcfg ::
        T.R_vector_64_bitvector_8 T.pmpcfg_n ::
        T.R_vector_64_bitvector_64 T.pmpaddr_n ::
        T.R_HartState T.hart_state ::
        T.R_list_PMA_Region T.pma_regions ::
        T.R_option_bitvector_64 T.htif_tohost_base ::
        nil.

(* A change of other registers, with the landing pad as before, preserves
        the conf. *)
Lemma preserve_conf_only_elp l s s' :
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs_elp = true ->
        only l s s' ->
        T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s')
                = T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s) ->
                preserve_conf s s'.
Proof.
        intros Hl (_ & Ho) He.
        assert (Hr : forall r, In r preserve_conf_regs_elp ->
                T.register_lookup r (st_regs s') = T.register_lookup r (st_regs s)).
        { intros r Hin. apply Ho.
          rewrite forallb_forall in Hl. specialize (Hl r Hin).
          destruct (reg_in l r); [discriminate Hl | reflexivity]. }
        unfold preserve_conf, st_regs_read, _regs_read.
        rewrite He.
        rewrite !Hr by (cbn; tauto).
        repeat split.
Qed.

(* ========================================================================== *)
(* Memory                                                                     *)
(* ========================================================================== *)

(* The four bytes at `a` are the word `w`. *)
Definition mem_word (a w : Z) (s : state) : Prop :=
        _mem_read (st_mem s) (definitions.Z_to_bv 64 a) 4 = definitions.Z_to_bv 32 w.

Lemma mem_word_only l a w s s' :
        only l s s' ->
        mem_word a w s ->
                mem_word a w s'.
Proof.
        intros (Hm & _). unfold mem_word. rewrite Hm. exact (fun H => H).
Qed.

(* A section stays in memory where the memory stays. *)
Lemma init_s_text_mem stmnts addr s s' :
        st_mem s' = st_mem s ->
        _init_s_text stmnts addr s ->
                _init_s_text stmnts addr s'.
Proof.
        intros Hm. revert addr. induction stmnts as [| [ins] stmnts IH]; intros addr H.
        - exact I.
        - destruct H as (H1 & H2). split; [exact (IH _ H1) |].
          unfold st_mem_read in *. rewrite Hm. exact H2.
Qed.

Lemma init_s_data_mem stmnts addr s s' :
        st_mem s' = st_mem s ->
        _init_s_data stmnts addr s ->
                _init_s_data stmnts addr s'.
Proof.
        intros Hm. revert addr. induction stmnts as [| [b] stmnts IH]; intros addr H.
        - exact I.
        - destruct H as (H1 & H2). split; [exact (IH _ H1) |].
          unfold st_mem_read in *. rewrite Hm. exact H2.
Qed.

Lemma exec_init_src_1_mem sec addr s s' :
        st_mem s' = st_mem s ->
        exec_init_src_1 sec addr s ->
                exec_init_src_1 sec addr s'.
Proof.
        intros Hm. destruct sec as [l | l]; cbn [exec_init_src_1].
        - exact (init_s_text_mem l addr s s' Hm).
        - exact (init_s_data_mem l addr s s' Hm).
Qed.

Lemma exec_init_src_1_only l sec addr s s' :
        only l s s' ->
        exec_init_src_1 sec addr s ->
                exec_init_src_1 sec addr s'.
Proof.
        intros (Hm & _). exact (exec_init_src_1_mem sec addr s s' Hm).
Qed.
