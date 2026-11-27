(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.conf.preserve_conf.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.
Require Import turtle.gen.reg.
Require Import turtle.gen.ev.
Require Import turtle.gen.step.
Require Import turtle.gen.tla.
Require Import turtle.gen.load.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.compat.sail.riscv.examples.print32.conf_default.
Require Import turtle.compat.sail.riscv.examples.print32.main_1.
Require Import turtle.compat.sail.riscv.examples.print32.main_2.
Require Import turtle.compat.sail.riscv.examples.print32.thm.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Module T := rv64d_types.

(* ========================================================================== *)
(* The conf                                                                   *)
(* ========================================================================== *)

(* `conf_intro` of ev.v: the facts of `conf_default`. *)
Ltac conf_intro ::=
        repeat match goal with
                | H : conf_default _ |- _ =>
                        unfold conf_default, conf_cur_privilege, conf_misa, conf_mstatus_sxl,
                                conf_mstatus_uxl, conf_mstatus_mprv, conf_mie, conf_satp64_mode,
                                conf_senvcfg_pmm, conf_senvcfg_lpe, conf_pmpcfg0, conf_pmpaddr0,
                                conf_elp, conf_hart_state, conf_htif_tohost_base in H;
                        ev_init H
                end.

(* A step that preserves the conf keeps `conf_default`. *)
Lemma conf_keep s s' :
        preserve_conf s s' ->
        conf_default s ->
                conf_default s'.
Proof.
        unfold preserve_conf, conf_default.
        intros (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14)
                (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
        repeat split; congruence.
Qed.

(* Two states of `conf_default`: the conf is preserved. *)
Lemma conf_same s s' :
        conf_default s ->
        conf_default s' ->
                preserve_conf s s'.
Proof.
        unfold preserve_conf, conf_default.
        intros (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14)
                (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
        repeat split; congruence.
Qed.

(* A change of other registers keeps `conf_default`. *)
Lemma conf_default_only l s s' :
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs = true ->
        only l s s' ->
        conf_default s ->
                conf_default s'.
Proof.
        intros Hl Ho. exact (conf_keep s s' (preserve_conf_only l s s' Hl Ho)).
Qed.

(* A change of other registers, and of the landing pad to none expected,
        keeps `conf_default`. *)
Lemma conf_default_only_elp l s s' :
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs_elp = true ->
        only l s s' ->
        T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0 ->
        conf_default s ->
                conf_default s'.
Proof.
        intros Hl Ho He Hi. apply (conf_keep s s'); [| exact Hi].
        apply (preserve_conf_only_elp l s s' Hl Ho). rewrite He. symmetry.
        destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). exact Hi.
Qed.

(* ========================================================================== *)
(* Registers                                                                  *)
(* ========================================================================== *)

(* The stack pointer of the first state. *)
Lemma reg_sp s :
        exec_init_sp_1 (conf_stack_addr + conf_stack_size) s ->
                reg T.x2 0x4000000000 s.
Proof.
        intros Hsp. unfold exec_init_sp_1, st_regs_read, _regs_read in Hsp. unfold reg.
        change (conf_stack_addr + conf_stack_size) with 0x4000000000 in Hsp.
        rewrite <- Hsp. symmetry. apply definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma sp_reg s :
        reg T.x2 0x4000000000 s ->
                exec_init_sp_1 (conf_stack_addr + conf_stack_size) s.
Proof.
        intros Hx. unfold exec_init_sp_1. change (conf_stack_addr + conf_stack_size) with 0x4000000000.
        exact (reg_abi _ _ _ Hx ltac:(lia)).
Qed.

(* ========================================================================== *)
(* The instructions of `main_2.main_sec e_static`, main + 0 to main + 12.     *)
(* ========================================================================== *)

Section step.

(* main + 0: addi a1, zero, 32 *)
Lemma main_2_ins_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10000 ->
        mem_word 0x10000 33555859 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10004
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 0x20.
Proof.
        step_tac.
Qed.

(* main + 4: lui a0, 0x100 *)
Lemma main_2_ins_1 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10004 ->
        mem_word 0x10004 1049911 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10008
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 8: addi a0, a0, 0 *)
Lemma main_2_ins_2 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10008 ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 0x100000 ->
        mem_word 0x10008 328979 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1000c
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 12: lui ra, 0x14 *)
Lemma main_2_ins_3 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1000c ->
        mem_word 0x1000c 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10010
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The instructions of `main_2.main_sec e_static`, main + 16 to main + 28.    *)
(* ========================================================================== *)

Section step.

(* main + 16: jalr ra, ra, 0: call printf *)
Lemma main_2_ins_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10010 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x10010 32999 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14000
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10014.
Proof.
        step_tac.
Qed.

(* main + 20: addi a0, zero, 0 *)
Lemma main_2_ins_5 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10014 ->
        mem_word 0x10014 1299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10018
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x0.
Proof.
        step_tac.
Qed.

(* main + 24: lui ra, 0x14 *)
Lemma main_2_ins_6 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10018 ->
        mem_word 0x10018 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1001c
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 28: jalr ra, ra, 256: call exit *)
Lemma main_2_ins_7 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1001c ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x1001c 268468455 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14100
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10020.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The run of `main_2_s e_static`: a stage for each instruction, the call of  *)
(* printf, the exit.                                                          *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The stages                                                                 *)
(* ========================================================================== *)

(* The words of `main_2.main_sec e_static` and the format. *)
Definition main_2_prog (s : state) : Prop :=
        conf_default s
        /\ mem_word 0x10000 33555859 s
        /\ mem_word 0x10004 1049911 s
        /\ mem_word 0x10008 328979 s
        /\ mem_word 0x1000c 82103 s
        /\ mem_word 0x10010 32999 s
        /\ mem_word 0x10014 1299 s
        /\ mem_word 0x10018 82103 s
        /\ mem_word 0x1001c 268468455 s
        /\ exec_init_src_1 main_2._tl_fmt_sec 0x100000 s.

(* The address of the instruction of stage `k`; of stage 5, printf; of stage
        9, exit. *)
Definition main_2_pc (k : nat) : Z :=
        match k with
                | 0%nat  => 0x10000
                | 1%nat  => 0x10004
                | 2%nat  => 0x10008
                | 3%nat  => 0x1000c
                | 4%nat  => 0x10010
                | 5%nat  => 0x14000
                | 6%nat  => 0x10014
                | 7%nat  => 0x10018
                | 8%nat  => 0x1001c
                | _      => 0x14100
                end.

(* What the instructions before stage `k` have set; the stack pointer, the
        first state. *)
Definition main_2_regs (k : nat) (s : state) : Prop :=
        match k with
                | 0%nat  => reg T.x2 0x4000000000 s
                | 1%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x11 32 s
                | 2%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                | 3%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                | 4%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 5%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10014 s
                | 6%nat  => reg T.x2 0x4000000000 s
                | 7%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x10 0 s
                | 8%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x10 0 s
                        /\ reg T.x1 0x14000 s
                | _      => reg T.x2 0x4000000000 s
                        /\ reg T.x10 0 s
                        /\ reg T.x1 0x10020 s
                end.

Definition main_2_stage (k : nat) (s : state) : Prop :=
        main_2_prog s
        /\ reg T.PC (main_2_pc k) s
        /\ main_2_regs k s.

Lemma main_2_prog_only l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs = true ->
        main_2_prog s ->
                main_2_prog s'.
Proof.
        intros Ho Hl (Hi & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & Hf).
        split; [exact (conf_default_only l s s' Hl Ho Hi) |].
        split; [exact (mem_word_only l _ _ s s' Ho M0) |].
        split; [exact (mem_word_only l _ _ s s' Ho M1) |].
        split; [exact (mem_word_only l _ _ s s' Ho M2) |].
        split; [exact (mem_word_only l _ _ s s' Ho M3) |].
        split; [exact (mem_word_only l _ _ s s' Ho M4) |].
        split; [exact (mem_word_only l _ _ s s' Ho M5) |].
        split; [exact (mem_word_only l _ _ s s' Ho M6) |].
        split; [exact (mem_word_only l _ _ s s' Ho M7) |].
        exact (exec_init_src_1_only l _ _ s s' Ho Hf).
Qed.

Lemma main_2_prog_only_elp l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs_elp = true ->
        T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0 ->
        main_2_prog s ->
                main_2_prog s'.
Proof.
        intros Ho Hl He (Hi & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & Hf).
        split; [exact (conf_default_only_elp l s s' Hl Ho He Hi) |].
        split; [exact (mem_word_only l _ _ s s' Ho M0) |].
        split; [exact (mem_word_only l _ _ s s' Ho M1) |].
        split; [exact (mem_word_only l _ _ s s' Ho M2) |].
        split; [exact (mem_word_only l _ _ s s' Ho M3) |].
        split; [exact (mem_word_only l _ _ s s' Ho M4) |].
        split; [exact (mem_word_only l _ _ s s' Ho M5) |].
        split; [exact (mem_word_only l _ _ s s' Ho M6) |].
        split; [exact (mem_word_only l _ _ s s' Ho M7) |].
        exact (exec_init_src_1_only l _ _ s s' Ho Hf).
Qed.

Lemma main_2_stage_pc k s :
        main_2_stage k s ->
                _pc_addr s = main_2_pc k.
Proof.
        intros (_ & Hpc & _). apply (reg_pc _ _ Hpc).
        do 9 (destruct k as [| k]; [cbn; lia |]). cbn; lia.
Qed.

(* A tick keeps the stage. *)
Lemma main_2_tick k s s' :
        main_2_stage k s ->
        only (T.R_bitvector_64 T.mcycle :: T.R_bitvector_64 T.mtime :: nil) s s' ->
                main_2_stage k s'.
Proof.
        intros (Hp & Hpc & Hx) Hl.
        split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
        split; [exact (reg_only _ _ _ _ _ Hl Hpc eq_refl) |].
        destruct k as [| [| [| [| [| [| [| [| [| k]]]]]]]]];
                cbn [main_2_regs] in *;
                repeat match goal with
                        | H : _ /\ _ |- _ => destruct H
                        end;
                regs_after Hl.
Qed.

(* ========================================================================== *)
(* One instruction                                                            *)
(* ========================================================================== *)

Section run.

(* A step from stage `k`, an instruction of main. *)
Lemma main_2_step k s :
        (k < 9)%nat ->
        k <> 5%nat ->
        main_2_stage k s ->
                forall n b, exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ main_2_stage (S k) s'.
Proof.
        intros Hk Hc (Hp & Hpc & Hx) n b.
        pose proof Hp as (Hi & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & Hf).
        destruct k as [| [| [| [| [| [| [| [| [| k]]]]]]]]]; [ .. | lia ].
        all: cbn [main_2_pc main_2_regs] in Hpc, Hx.
        - (* 0: main + 0 *)
          rename Hx into X2.
          destruct (main_2_ins_0 n b s Hi Hpc M0) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 1: main + 4 *)
          destruct Hx as (X2 & X11).
          destruct (main_2_ins_1 n b s Hi Hpc M1) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 2: main + 8 *)
          destruct Hx as (X2 & X11 & X10).
          destruct (main_2_ins_2 n b s Hi Hpc X10 M2) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 3: main + 12 *)
          destruct Hx as (X2 & X11 & X10).
          destruct (main_2_ins_3 n b s Hi Hpc M3) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 4: main + 16 *)
          destruct Hx as (X2 & X11 & X10 & X1).
          destruct (main_2_ins_4 n b s Hi Hpc X1 M4) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 5: printf *)
          exfalso. exact (Hc eq_refl).
        - (* 6: main + 20 *)
          rename Hx into X2.
          destruct (main_2_ins_5 n b s Hi Hpc M5) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 7: main + 24 *)
          destruct Hx as (X2 & X10).
          destruct (main_2_ins_6 n b s Hi Hpc M6) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
        - (* 8: main + 28 *)
          destruct Hx as (X2 & X10 & X1).
          destruct (main_2_ins_7 n b s Hi Hpc X1 M7) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_2_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_2_regs]. regs_after Hl.
Qed.

End run.

(* ========================================================================== *)
(* printf                                                                     *)
(* ========================================================================== *)

(* The return from printf, as main_2's run takes it. *)
Definition main_2_ret (s : state) : state :=
        ret_to 0x10014 s.

Lemma main_2_ret_stage s :
        main_2_stage 5 s ->
                main_2_stage 6 (main_2_ret s).
Proof.
        intros (Hp & _ & Hx). cbn [main_2_regs] in Hx. destruct Hx as (X2 & _ & _ & _).
        split; [exact (main_2_prog_only _ _ _ (ret_to_only _ s) eq_refl Hp) |].
        split; [exact (ret_to_pc _ s) |].
        cbn [main_2_regs]. exact (reg_only _ _ _ _ _ (ret_to_only _ s) X2 eq_refl).
Qed.

Lemma main_2_ret_abi s :
        main_2_stage 5 s ->
                abi_stepcond s (main_2_ret s)
                /\ abi_opt_stepcond_preserve_mem s (main_2_ret s)
                /\ abi_opt_stepcond_return s (main_2_ret s).
Proof.
        intros (_ & _ & Hx). cbn [main_2_regs] in Hx. destruct Hx as (_ & _ & _ & X1).
        apply ret_to_abi; [lia |]. unfold abi_ra. exact (reg_abi _ _ _ X1 ltac:(lia)).
Qed.

(* The format at `a0`: what printf expects. *)
Lemma main_2_fmt s :
        exec_init_src_1 main_2._tl_fmt_sec 0x100000 s ->
        abi_arg0 s = 0x100000 ->
                _printf_precond s.
Proof.
        intros Hf Ha. unfold _printf_precond. rewrite Ha. cbv zeta.
        destruct Hf as (((((_ & H4) & H3) & H2) & H1) & H0).
        split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 | exact H4].
Qed.

(* At printf, with 32. *)
Lemma main_2_prints s :
        main_2_stage 5 s ->
                prints e_static 32 s = true.
Proof.
        intros Hs. pose proof (main_2_stage_pc 5 s Hs) as Hpc.
        destruct Hs as (_ & _ & Hx).
        cbn [main_2_regs] in Hx. destruct Hx as (_ & X11 & _ & _).
        unfold prints. rewrite Hpc.
        unfold abi_arg1, abi_a1. rewrite (reg_abi _ _ _ X11 ltac:(lia)). reflexivity.
Qed.

(* What is seen: 32 at printf, nothing else. *)
Lemma main_2_obs k s :
        (k <= 9)%nat ->
        main_2_stage k s ->
                rm e_static s = if (k =? 5)%nat then Some 32 else None.
Proof.
        intros Hk Hs. pose proof (main_2_stage_pc k s Hs) as Hpc.
        destruct Hs as (_ & _ & Hx). unfold rm, prints. rewrite Hpc.
        destruct k as [| [| [| [| [| [| [| [| [| [| k]]]]]]]]]]; [ .. | lia ];
                try reflexivity.
        cbn [main_2_regs] in Hx. destruct Hx as (_ & X11 & _ & _).
        unfold abi_arg1, abi_a1. rewrite (reg_abi _ _ _ X11 ltac:(lia)). reflexivity.
Qed.

(* ========================================================================== *)
(* The first state                                                            *)
(* ========================================================================== *)

Lemma main_2_start_state s :
        conf_default s ->
        exec_init_pc_1 (e_static "main"%string) s ->
        exec_init_sp_1 (conf_stack_addr + conf_stack_size) s ->
        exec_init_src_1 main_2._tl_fmt_sec (e_static ".tl_fmt"%string) s ->
        exec_init_src_1 (main_2.main_sec e_static) (e_static "main"%string) s ->
                main_2_stage 0 s.
Proof.
        intros Hi Hpc Hsp Hfmt Hmain.
        let l := eval vm_compute in (main_2.main_sec e_static) in
        change (main_2.main_sec e_static) with l in Hmain.
        change (e_static "main"%string) with 0x10000 in Hmain.
        cbn [exec_init_src_1 _init_s_text] in Hmain.
        destruct Hmain as ((((((((_ & I7) & I6) & I5) & I4) & I3) & I2) & I1) & I0).
        instr_word I0. instr_word I1. instr_word I2. instr_word I3. instr_word I4. instr_word I5. instr_word I6. instr_word I7.
        change (e_static ".tl_fmt"%string) with 0x100000 in Hfmt.
        split; [| split].
        - exact (conj Hi (conj I0 (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 Hfmt))))))))).
        - apply pc_reg. exact Hpc.
        - cbn [main_2_regs]. exact (reg_sp s Hsp).
Qed.

Lemma main_2_start (sigma : behavior state) :
        exec_static main_2_s sigma ->
                main_2_stage 0 (sigma 0%nat).
Proof.
        intros (Hi & Hpc & Hsp & Hinit & _).
        destruct Hinit as ((_ & Hmain) & Hfmt).
        exact (main_2_start_state _ Hi Hpc Hsp Hfmt Hmain).
Qed.

(* ========================================================================== *)
(* Stage by stage                                                             *)
(* ========================================================================== *)

Lemma main_2_at_pc k s :
        (k < 9)%nat ->
        k <> 5%nat ->
        main_2_stage k s ->
                at_pc (main_2.main_sec e_static) (e_static "main"%string) s.
Proof.
        intros Hk Hc Hs. unfold at_pc. rewrite (main_2_stage_pc k s Hs).
        change (_section_size (main_2.main_sec e_static)) with 32.
        change (e_static "main"%string) with 0x10000.
        do 9 (destruct k as [| k]; [cbn [main_2_pc]; lia |]). lia.
Qed.

(* The stages at printf and at the exit are outside the text of main. *)
Lemma main_2_not_at_pc k s :
        (k = 5 \/ k = 9)%nat ->
        main_2_stage k s ->
                ~ at_pc (main_2.main_sec e_static) (e_static "main"%string) s.
Proof.
        intros Hk Hs. unfold at_pc. rewrite (main_2_stage_pc k s Hs).
        change (_section_size (main_2.main_sec e_static)) with 32.
        change (e_static "main"%string) with 0x10000.
        destruct Hk as [-> | ->]; cbn [main_2_pc]; lia.
Qed.

(* The format is never at the PC of a stage. *)
Lemma main_2_fmt_not_at_pc j s :
        main_2_stage j s ->
                ~ at_pc main_2._tl_fmt_sec (e_static ".tl_fmt"%string) s.
Proof.
        intros Hs. unfold at_pc. rewrite (main_2_stage_pc j s Hs).
        change (_section_size main_2._tl_fmt_sec) with 5.
        change (e_static ".tl_fmt"%string) with 0x100000.
        destruct j as [| [| [| [| [| [| [| [| [| [| j]]]]]]]]]];
                cbn [main_2_pc]; lia.
Qed.

Section leads.

Lemma main_2_step_tla k s :
        (k < 9)%nat ->
        k <> 5%nat ->
        main_2_stage k s ->
                (forall s', exec_eval_step_1 s s' -> main_2_stage (S k) s')
                /\ (exists s', exec_eval_step_1 s s' /\ main_2_stage (S k) s').
Proof.
        intros Hk Hc Hs. exact (step_tla s _ (main_2_step k s Hk Hc Hs)).
Qed.

(* The next stage is reached, from an instruction of main. *)
Lemma main_2_leads (sigma : behavior state) k :
        (k < 9)%nat ->
        k <> 5%nat ->
        exec_static main_2_s sigma ->
        forall i,
        main_2_stage k (sigma i) ->
                exists j,
                main_2_stage (S k) (sigma j).
Proof.
        intros Hk Hc (_ & _ & _ & _ & Hnext & Hwf).
        destruct Hnext as ((_ & Hnext) & _).
        destruct Hwf as ((_ & Hwf) & _).
        apply (leads sigma (main_2.main_sec e_static) (e_static "main"%string)
                (main_2_stage k) (main_2_stage (S k))
                (next_at sigma _ Hnext) (wf_at sigma _ Hwf)).
        - intros s Hs. exact (main_2_at_pc k s Hk Hc Hs).
        - intros s s' Hs. exact (proj1 (main_2_step_tla k s Hk Hc Hs) s').
        - intros s Hs. destruct (proj2 (main_2_step_tla k s Hk Hc Hs)) as (s' & Ho & Hs').
          exists s'. split; [exact Ho |]. intros <-.
          pose proof (main_2_stage_pc k s Hs) as P1. pose proof (main_2_stage_pc (S k) s Hs') as P2.
          rewrite P1 in P2. clear - Hk P2.
          do 9 (destruct k as [| k]; [cbn [main_2_pc] in P2; lia |]). lia.
        - intros s s' Hs Ht. exact (main_2_tick k s s' Hs (tick_tla s s' Ht)).
Qed.

End leads.

(* ========================================================================== *)
(* A behaviour of main_2, paced                                               *)
(* ========================================================================== *)

(* The run of stages `t 0` to `t 9`, paced: up to the call before `k`, at
        printf from `k` to `k + m`, then to the exit, there for ever. *)

Section paced.

Variable t : nat -> state.

Hypothesis Ht : forall j, (j <= 9)%nat -> main_2_stage j (t j).
Hypothesis Hok : forall j, (j < 9)%nat -> j <> 5%nat -> exec_eval_step_1 (t j) (t (S j)).
Hypothesis Hret : t 6%nat = main_2_ret (t 5%nat).
Hypothesis Hfmt : exec_init_src_1 main_2._tl_fmt_sec (e_static ".tl_fmt"%string) (t 0%nat).
Hypothesis Htext : exec_init_src_1 (main_2.main_sec e_static) (e_static "main"%string) (t 0%nat).

Variables k m : nat.

Hypothesis Hk : (5 <= k)%nat.
Hypothesis Hm : (1 <= m)%nat.

Definition paced_idx (n : nat) : nat :=
        if (n <? 4)%nat then n
        else if (n <? k)%nat then 4%nat
        else if (n <? k + m)%nat then 5%nat
        else if (n <? k + m + 3)%nat then (6 + (n - (k + m)))%nat
        else 9%nat.

Definition paced (n : nat) : state :=
        t (paced_idx n).

Lemma paced_idx_le n :
        (paced_idx n <= 9)%nat.
Proof.
        unfold paced_idx.
        destruct (Nat.ltb_spec n 4), (Nat.ltb_spec n k), (Nat.ltb_spec n (k + m)),
                (Nat.ltb_spec n (k + m + 3)); lia.
Qed.

Lemma paced_idx_succ n :
        paced_idx (S n) = paced_idx n
        \/ paced_idx (S n) = S (paced_idx n).
Proof.
        unfold paced_idx.
        destruct (Nat.ltb_spec n 4), (Nat.ltb_spec n k), (Nat.ltb_spec n (k + m)),
                (Nat.ltb_spec n (k + m + 3)),
                (Nat.ltb_spec (S n) 4), (Nat.ltb_spec (S n) k), (Nat.ltb_spec (S n) (k + m)),
                (Nat.ltb_spec (S n) (k + m + 3)); lia.
Qed.

Lemma paced_idx_end n :
        (k + m + 3 <= n)%nat ->
                paced_idx n = 9%nat.
Proof.
        intros Hn. unfold paced_idx.
        destruct (Nat.ltb_spec n 4), (Nat.ltb_spec n k), (Nat.ltb_spec n (k + m)),
                (Nat.ltb_spec n (k + m + 3)); lia.
Qed.

Lemma paced_idx_call n :
        paced_idx n = 5%nat <-> (k <= n < k + m)%nat.
Proof.
        unfold paced_idx.
        destruct (Nat.ltb_spec n 4), (Nat.ltb_spec n k), (Nat.ltb_spec n (k + m)),
                (Nat.ltb_spec n (k + m + 3)); lia.
Qed.

Lemma paced_stage n :
        main_2_stage (paced_idx n) (paced n).
Proof.
        exact (Ht _ (paced_idx_le n)).
Qed.

Lemma paced_end n :
        (k + m + 3 <= n)%nat ->
                paced n = paced (k + m + 3)%nat.
Proof.
        intros Hn. unfold paced.
        rewrite (paced_idx_end n Hn), (paced_idx_end (k + m + 3)) by lia.
        reflexivity.
Qed.

Lemma paced_end_stage :
        main_2_stage 9 (paced (k + m + 3)%nat).
Proof.
        pose proof (paced_stage (k + m + 3)) as H. rewrite paced_idx_end in H by lia. exact H.
Qed.

(* A step of the paced run: a stutter, or from `t j` to `t (S j)`. *)
Lemma paced_step n :
        paced n = paced (S n)
        \/ exists j,
                (j < 9)%nat
                /\ paced n = t j
                /\ paced (S n) = t (S j).
Proof.
        unfold paced. destruct (paced_idx_succ n) as [H | H].
        - left. rewrite H. reflexivity.
        - right. exists (paced_idx n). split; [| split; [reflexivity | rewrite H; reflexivity]].
          pose proof (paced_idx_le (S n)). lia.
Qed.

Lemma paced_obs n :
        rm e_static (paced n) = if andb (k <=? n)%nat (n <? k + m)%nat then Some 32 else None.
Proof.
        rewrite (main_2_obs _ _ (paced_idx_le n) (paced_stage n)).
        pose proof (paced_idx_call n) as H.
        destruct (Nat.eqb_spec (paced_idx n) 5), (Nat.leb_spec k n), (Nat.ltb_spec n (k + m));
                cbn [andb]; first [ reflexivity | exfalso; lia ].
Qed.

(* Weak fairness of an action that only stutters at the exit. *)
Lemma paced_wf (A : state -> state -> Prop) :
        (forall s s', main_2_stage 9 s -> A s s' -> s' = s) ->
                (\wf (\lift2 A) \sub exec_vars) paced.
Proof.
        intros HA. apply (wf_end paced A (k + m + 3)).
        - exact paced_end.
        - intros s'. exact (HA _ s' paced_end_stage).
Qed.

Lemma paced_sail_pc j :
        (j <= 9)%nat ->
                _pc_addr (t j) = main_2_pc j.
Proof.
        intros Hj. exact (main_2_stage_pc j _ (Ht j Hj)).
Qed.

Lemma paced_fmt_tla :
        ([][\lift2 (exec_next_src_1 main_2._tl_fmt_sec (e_static ".tl_fmt"%string))]_ exec_vars) paced
        /\ (\wf (\lift2 (exec_fair_src_1 main_2._tl_fmt_sec (e_static ".tl_fmt"%string))) \sub exec_vars) paced.
Proof.
        split.
        - apply next_intro. intros n. left. intros Hat.
          exfalso. exact (main_2_fmt_not_at_pc _ _ (paced_stage n) Hat).
        - apply paced_wf. intros s s' Hse (Hat & _).
          exfalso. exact (main_2_fmt_not_at_pc 9 s Hse Hat).
Qed.

(* A stage before the exit is not at `a`, an address of the libc but printf. *)
Lemma paced_not_at j a :
        (j < 9)%nat ->
        a = 0x14100 \/ a = 0x14200 ->
                _pc_addr (t j) <> a.
Proof.
        intros Hj Ha. rewrite (paced_sail_pc j ltac:(lia)).
        clear - Hj Ha. do 9 (destruct j as [| j]; [cbn [main_2_pc]; lia |]). lia.
Qed.

(* The step of main: the instructions but the call of printf. *)
Lemma paced_main_tla :
        ([][\lift2 (exec_next_src_1 (main_2.main_sec e_static) (e_static "main"%string))]_ exec_vars) paced
        /\ (\wf (\lift2 (exec_fair_src_1 (main_2.main_sec e_static) (e_static "main"%string))) \sub exec_vars) paced.
Proof.
        split.
        - apply next_intro. intros n.
          destruct (paced_step n) as [Hs | (j & Hj & Hn & Hn')]; [right; exact Hs |].
          left. rewrite Hn, Hn'. intros Hat.
          destruct (Nat.eq_dec j 5) as [-> | Hc].
          + exfalso. exact (main_2_not_at_pc 5 _ (or_introl eq_refl) (Ht 5%nat ltac:(lia)) Hat).
          + left. exact (Hok j Hj Hc).
        - apply paced_wf. intros s s' Hse (Hat & _).
          exfalso. exact (main_2_not_at_pc 9 s (or_intror eq_refl) Hse Hat).
Qed.

Lemma paced_main_2_tla :
        exec_static main_2_s paced.
Proof.
        pose proof paced_fmt_tla as Bf.
        split; [| split; [| split; [| split; [| split]]]].
        - exact (proj1 (proj1 (Ht 0%nat ltac:(lia)))).
        - exact (main_2_stage_pc 0 _ (Ht 0%nat ltac:(lia))).
        - exact (sp_reg _ (proj2 (proj2 (Ht 0%nat ltac:(lia))))).
        - split; [split |].
          + exact I.
          + exact Htext.
          + exact Hfmt.
        - split; [split |].
          + exact I.
          + exact (proj1 paced_main_tla).
          + exact (proj1 Bf).
        - split; [split |].
          + exact I.
          + exact (proj2 paced_main_tla).
          + exact (proj2 Bf).
Qed.

Lemma paced_libc_tla :
        unsafe_libc e_static paced.
Proof.
        split; [| split].
        - split.
          + apply next_intro. intros n.
            destruct (paced_step n) as [Hs | (j & Hj & Hn & Hn')]; [right; exact Hs |].
            left. rewrite Hn, Hn'. intros Hpc _ _.
            destruct (Nat.eq_dec j 5) as [-> | Hc].
            * rewrite Hret. exact (main_2_ret_abi _ (Ht 5%nat ltac:(lia))).
            * exfalso. rewrite (paced_sail_pc j ltac:(lia)) in Hpc. revert Hpc Hc.
              clear - Hj. do 9 (destruct j as [| j]; [cbn; intros; lia |]). lia.
          + apply paced_wf. intros s s' Hse (Hpc & _).
            exfalso. rewrite (main_2_stage_pc 9 s Hse) in Hpc. cbn in Hpc. lia.
        - apply next_intro. intros n.
          destruct (paced_step n) as [Hs | (j & Hj & Hn & Hn')]; [right; exact Hs |].
          left. rewrite Hn, Hn'. intros Hpc _.
          exfalso. exact (paced_not_at j _ Hj (or_introl eq_refl) Hpc).
        - split.
          + apply next_intro. intros n.
            destruct (paced_step n) as [Hs | (j & Hj & Hn & Hn')]; [right; exact Hs |].
            left. rewrite Hn, Hn'. intros Hpc _.
            exfalso. exact (paced_not_at j _ Hj (or_intror eq_refl) Hpc).
          + apply paced_wf. intros s s' Hse (Hpc & _).
            exfalso. rewrite (main_2_stage_pc 9 s Hse) in Hpc. cbn in Hpc. lia.
Qed.

End paced.

Section thm.

Theorem thm_1 :
        valid ((exec_static main_2_s \land unsafe_libc e_static)
                \impl <> \lift1 (fun s => Is_true (prints e_static 32 s))).
Proof.
        intros sigma (Hmain & _).
        pose proof (main_2_start sigma Hmain) as H0.
        destruct (main_2_leads sigma 0 ltac:(lia) ltac:(lia) Hmain _ H0) as (j1 & H1).
        destruct (main_2_leads sigma 1 ltac:(lia) ltac:(lia) Hmain _ H1) as (j2 & H2).
        destruct (main_2_leads sigma 2 ltac:(lia) ltac:(lia) Hmain _ H2) as (j3 & H3).
        destruct (main_2_leads sigma 3 ltac:(lia) ltac:(lia) Hmain _ H3) as (j4 & H4).
        destruct (main_2_leads sigma 4 ltac:(lia) ltac:(lia) Hmain _ H4) as (j5 & H5).
        exists j5. unfold Lift1, util_suffix. rewrite Nat.add_0_r.
        apply Is_true_eq_left. exact (main_2_prints (sigma j5) H5).
Qed.

End thm.

(* The statement of thm.v. *)
Definition thm_1_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.print32.thm.thm_1 in exact t) :=
        thm_1.

Print Assumptions thm_1.

(* ========================================================================== *)
(* The instructions of `main_1.main_sec e_static` outside the loop.           *)
(* ========================================================================== *)

Section step.

(* main + 0: addi s1, zero, 2 *)
Lemma main_1_ins_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10000 ->
        mem_word 0x10000 2098323 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x9)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10004
                /\ T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s') = definitions.Z_to_bv 64 0x2.
Proof.
        step_tac.
Qed.

(* main + 4: addi s2, zero, 4 *)
Lemma main_1_ins_1 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10004 ->
        mem_word 0x10004 4196627 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x18)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10008
                /\ T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s') = definitions.Z_to_bv 64 0x4.
Proof.
        step_tac.
Qed.

(* main + 48: addi a0, zero, 0 *)
Lemma main_1_ins_12 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10030 ->
        mem_word 0x10030 1299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10034
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x0.
Proof.
        step_tac.
Qed.

(* main + 52: lui ra, 0x14 *)
Lemma main_1_ins_13 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10034 ->
        mem_word 0x10034 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10038
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 56: jalr ra, ra, 256: call exit *)
Lemma main_1_ins_14 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10038 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x10038 268468455 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14100
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x1003c.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* main + 8: add s1, s1, s1                                                   *)
(* ========================================================================== *)

Section step.

(* main + 8: add s1, s1, s1, s1 = 2 *)
Lemma main_1_ins_2_2 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10008 ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x2 ->
        mem_word 0x10008 9733299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x9)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1000c
                /\ T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s') = definitions.Z_to_bv 64 0x4.
Proof.
        step_tac.
Qed.

(* main + 8: add s1, s1, s1, s1 = 4 *)
Lemma main_1_ins_2_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10008 ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x4 ->
        mem_word 0x10008 9733299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x9)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1000c
                /\ T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s') = definitions.Z_to_bv 64 0x8.
Proof.
        step_tac.
Qed.

(* main + 8: add s1, s1, s1, s1 = 8 *)
Lemma main_1_ins_2_8 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10008 ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x8 ->
        mem_word 0x10008 9733299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x9)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1000c
                /\ T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s') = definitions.Z_to_bv 64 0x10.
Proof.
        step_tac.
Qed.

(* main + 8: add s1, s1, s1, s1 = 16 *)
Lemma main_1_ins_2_16 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10008 ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x10 ->
        mem_word 0x10008 9733299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x9)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1000c
                /\ T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s') = definitions.Z_to_bv 64 0x20.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* main + 12: addi a1, s1, 0                                                  *)
(* ========================================================================== *)

Section step.

(* main + 12: addi a1, s1, 0, s1 = 4 *)
Lemma main_1_ins_3_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1000c ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x4 ->
        mem_word 0x1000c 296339 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10010
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 0x4.
Proof.
        step_tac.
Qed.

(* main + 12: addi a1, s1, 0, s1 = 8 *)
Lemma main_1_ins_3_8 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1000c ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x8 ->
        mem_word 0x1000c 296339 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10010
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 0x8.
Proof.
        step_tac.
Qed.

(* main + 12: addi a1, s1, 0, s1 = 16 *)
Lemma main_1_ins_3_16 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1000c ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x10 ->
        mem_word 0x1000c 296339 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10010
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 0x10.
Proof.
        step_tac.
Qed.

(* main + 12: addi a1, s1, 0, s1 = 32 *)
Lemma main_1_ins_3_32 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1000c ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 0x20 ->
        mem_word 0x1000c 296339 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10010
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 0x20.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* main + 16 to main + 28: the call of printf                                 *)
(* ========================================================================== *)

Section step.

(* main + 16: lui a0, 0x100 *)
Lemma main_1_ins_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10010 ->
        mem_word 0x10010 1049911 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10014
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 20: addi a0, a0, 0 *)
Lemma main_1_ins_5 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10014 ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 0x100000 ->
        mem_word 0x10014 328979 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10018
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 24: lui ra, 0x14 *)
Lemma main_1_ins_6 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10018 ->
        mem_word 0x10018 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1001c
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 28: jalr ra, ra, 0: call printf *)
Lemma main_1_ins_7 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1001c ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x1001c 32999 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14000
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10020.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* main + 32: addi s2, s2, -1                                                 *)
(* ========================================================================== *)

Section step.

(* main + 32: addi s2, s2, -1, s2 = 4 *)
Lemma main_1_ins_8_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10020 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x4 ->
        mem_word 0x10020 4294510867 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x18)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10024
                /\ T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s') = definitions.Z_to_bv 64 0x3.
Proof.
        step_tac.
Qed.

(* main + 32: addi s2, s2, -1, s2 = 3 *)
Lemma main_1_ins_8_3 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10020 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x3 ->
        mem_word 0x10020 4294510867 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x18)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10024
                /\ T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s') = definitions.Z_to_bv 64 0x2.
Proof.
        step_tac.
Qed.

(* main + 32: addi s2, s2, -1, s2 = 2 *)
Lemma main_1_ins_8_2 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10020 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x2 ->
        mem_word 0x10020 4294510867 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x18)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10024
                /\ T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s') = definitions.Z_to_bv 64 0x1.
Proof.
        step_tac.
Qed.

(* main + 32: addi s2, s2, -1, s2 = 1 *)
Lemma main_1_ins_8_1 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10020 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x1 ->
        mem_word 0x10020 4294510867 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x18)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10024
                /\ T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s') = definitions.Z_to_bv 64 0x0.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* main + 36: beq s2, zero, 12                                                *)
(* ========================================================================== *)

Section step.

(* main + 36: beq s2, zero, 12, s2 = 3 *)
Lemma main_1_ins_9_3 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10024 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x3 ->
        mem_word 0x10024 591459 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10028.
Proof.
        step_tac.
Qed.

(* main + 36: beq s2, zero, 12, s2 = 2 *)
Lemma main_1_ins_9_2 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10024 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x2 ->
        mem_word 0x10024 591459 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10028.
Proof.
        step_tac.
Qed.

(* main + 36: beq s2, zero, 12, s2 = 1 *)
Lemma main_1_ins_9_1 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10024 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x1 ->
        mem_word 0x10024 591459 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10028.
Proof.
        step_tac.
Qed.

(* main + 36: beq s2, zero, 12, s2 = 0 *)
Lemma main_1_ins_9_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10024 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 0x0 ->
        mem_word 0x10024 591459 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10030.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* main + 40 to main + 44: the jump to the loop                               *)
(* ========================================================================== *)

Section step.

(* main + 40: lui t0, 0x10 *)
Lemma main_1_ins_10 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10028 ->
        mem_word 0x10028 66231 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x5)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1002c
                /\ T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s') = definitions.Z_to_bv 64 0x10000.
Proof.
        step_tac.
Qed.

(* main + 44: jalr zero, t0, 8 *)
Lemma main_1_ins_11 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1002c ->
        T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s) = definitions.Z_to_bv 64 0x10000 ->
        mem_word 0x1002c 8552551 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10008.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The run of `main_1_s e_static`: a stage for each instruction that runs,    *)
(* each call of printf, the exit.                                             *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The stages                                                                 *)
(* ========================================================================== *)

(* The words of `main_1.main_sec e_static` and the format. *)
Definition main_1_prog (s : state) : Prop :=
        conf_default s
        /\ mem_word 0x10000 2098323 s
        /\ mem_word 0x10004 4196627 s
        /\ mem_word 0x10008 9733299 s
        /\ mem_word 0x1000c 296339 s
        /\ mem_word 0x10010 1049911 s
        /\ mem_word 0x10014 328979 s
        /\ mem_word 0x10018 82103 s
        /\ mem_word 0x1001c 32999 s
        /\ mem_word 0x10020 4294510867 s
        /\ mem_word 0x10024 591459 s
        /\ mem_word 0x10028 66231 s
        /\ mem_word 0x1002c 8552551 s
        /\ mem_word 0x10030 1299 s
        /\ mem_word 0x10034 82103 s
        /\ mem_word 0x10038 268468455 s
        /\ exec_init_src_1 main_1._tl_fmt_sec 0x100000 s.

(* The address of the instruction of stage `k`; of stages 8, 19, 30, 41, printf; of stage
        47, exit. *)
Definition main_1_pc (k : nat) : Z :=
        match k with
                | 0%nat  => 0x10000
                | 1%nat  => 0x10004
                | 2%nat  => 0x10008
                | 3%nat  => 0x1000c
                | 4%nat  => 0x10010
                | 5%nat  => 0x10014
                | 6%nat  => 0x10018
                | 7%nat  => 0x1001c
                | 8%nat  => 0x14000
                | 9%nat  => 0x10020
                | 10%nat => 0x10024
                | 11%nat => 0x10028
                | 12%nat => 0x1002c
                | 13%nat => 0x10008
                | 14%nat => 0x1000c
                | 15%nat => 0x10010
                | 16%nat => 0x10014
                | 17%nat => 0x10018
                | 18%nat => 0x1001c
                | 19%nat => 0x14000
                | 20%nat => 0x10020
                | 21%nat => 0x10024
                | 22%nat => 0x10028
                | 23%nat => 0x1002c
                | 24%nat => 0x10008
                | 25%nat => 0x1000c
                | 26%nat => 0x10010
                | 27%nat => 0x10014
                | 28%nat => 0x10018
                | 29%nat => 0x1001c
                | 30%nat => 0x14000
                | 31%nat => 0x10020
                | 32%nat => 0x10024
                | 33%nat => 0x10028
                | 34%nat => 0x1002c
                | 35%nat => 0x10008
                | 36%nat => 0x1000c
                | 37%nat => 0x10010
                | 38%nat => 0x10014
                | 39%nat => 0x10018
                | 40%nat => 0x1001c
                | 41%nat => 0x14000
                | 42%nat => 0x10020
                | 43%nat => 0x10024
                | 44%nat => 0x10030
                | 45%nat => 0x10034
                | 46%nat => 0x10038
                | _      => 0x14100
                end.

(* What the instructions before stage `k` have set; the stack pointer, the
        first state. *)
Definition main_1_regs (k : nat) (s : state) : Prop :=
        match k with
                | 0%nat  => reg T.x2 0x4000000000 s
                | 1%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 2 s
                | 2%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 2 s
                        /\ reg T.x18 4 s
                | 3%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                | 4%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                        /\ reg T.x11 4 s
                | 5%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                        /\ reg T.x11 4 s
                        /\ reg T.x10 0x100000 s
                | 6%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                        /\ reg T.x11 4 s
                        /\ reg T.x10 0x100000 s
                | 7%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                        /\ reg T.x11 4 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 8%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                        /\ reg T.x11 4 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10020 s
                | 9%nat  => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 4 s
                | 10%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 3 s
                | 11%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 3 s
                | 12%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 3 s
                        /\ reg T.x5 0x10000 s
                | 13%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 4 s
                        /\ reg T.x18 3 s
                | 14%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                | 15%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                        /\ reg T.x11 8 s
                | 16%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                        /\ reg T.x11 8 s
                        /\ reg T.x10 0x100000 s
                | 17%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                        /\ reg T.x11 8 s
                        /\ reg T.x10 0x100000 s
                | 18%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                        /\ reg T.x11 8 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 19%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                        /\ reg T.x11 8 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10020 s
                | 20%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 3 s
                | 21%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 2 s
                | 22%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 2 s
                | 23%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 2 s
                        /\ reg T.x5 0x10000 s
                | 24%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 8 s
                        /\ reg T.x18 2 s
                | 25%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                | 26%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                        /\ reg T.x11 16 s
                | 27%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                        /\ reg T.x11 16 s
                        /\ reg T.x10 0x100000 s
                | 28%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                        /\ reg T.x11 16 s
                        /\ reg T.x10 0x100000 s
                | 29%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                        /\ reg T.x11 16 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 30%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                        /\ reg T.x11 16 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10020 s
                | 31%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 2 s
                | 32%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 1 s
                | 33%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 1 s
                | 34%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 1 s
                        /\ reg T.x5 0x10000 s
                | 35%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 16 s
                        /\ reg T.x18 1 s
                | 36%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                | 37%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                        /\ reg T.x11 32 s
                | 38%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                | 39%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                | 40%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 41%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                        /\ reg T.x11 32 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10020 s
                | 42%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 1 s
                | 43%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 0 s
                | 44%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 0 s
                | 45%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 0 s
                        /\ reg T.x10 0 s
                | 46%nat => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 0 s
                        /\ reg T.x10 0 s
                        /\ reg T.x1 0x14000 s
                | _      => reg T.x2 0x4000000000 s
                        /\ reg T.x9 32 s
                        /\ reg T.x18 0 s
                        /\ reg T.x10 0 s
                        /\ reg T.x1 0x1003c s
                end.

Definition main_1_stage (k : nat) (s : state) : Prop :=
        main_1_prog s
        /\ reg T.PC (main_1_pc k) s
        /\ main_1_regs k s.

(* The stages at printf. *)
Definition main_1_call (k : nat) : bool :=
        (k =? 8)%nat || (k =? 19)%nat || (k =? 30)%nat || (k =? 41)%nat.

Lemma main_1_prog_only l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs = true ->
        main_1_prog s ->
                main_1_prog s'.
Proof.
        intros Ho Hl (Hi & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & Hf).
        split; [exact (conf_default_only l s s' Hl Ho Hi) |].
        split; [exact (mem_word_only l _ _ s s' Ho M0) |].
        split; [exact (mem_word_only l _ _ s s' Ho M1) |].
        split; [exact (mem_word_only l _ _ s s' Ho M2) |].
        split; [exact (mem_word_only l _ _ s s' Ho M3) |].
        split; [exact (mem_word_only l _ _ s s' Ho M4) |].
        split; [exact (mem_word_only l _ _ s s' Ho M5) |].
        split; [exact (mem_word_only l _ _ s s' Ho M6) |].
        split; [exact (mem_word_only l _ _ s s' Ho M7) |].
        split; [exact (mem_word_only l _ _ s s' Ho M8) |].
        split; [exact (mem_word_only l _ _ s s' Ho M9) |].
        split; [exact (mem_word_only l _ _ s s' Ho M10) |].
        split; [exact (mem_word_only l _ _ s s' Ho M11) |].
        split; [exact (mem_word_only l _ _ s s' Ho M12) |].
        split; [exact (mem_word_only l _ _ s s' Ho M13) |].
        split; [exact (mem_word_only l _ _ s s' Ho M14) |].
        exact (exec_init_src_1_only l _ _ s s' Ho Hf).
Qed.

Lemma main_1_prog_only_elp l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs_elp = true ->
        T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0 ->
        main_1_prog s ->
                main_1_prog s'.
Proof.
        intros Ho Hl He (Hi & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & Hf).
        split; [exact (conf_default_only_elp l s s' Hl Ho He Hi) |].
        split; [exact (mem_word_only l _ _ s s' Ho M0) |].
        split; [exact (mem_word_only l _ _ s s' Ho M1) |].
        split; [exact (mem_word_only l _ _ s s' Ho M2) |].
        split; [exact (mem_word_only l _ _ s s' Ho M3) |].
        split; [exact (mem_word_only l _ _ s s' Ho M4) |].
        split; [exact (mem_word_only l _ _ s s' Ho M5) |].
        split; [exact (mem_word_only l _ _ s s' Ho M6) |].
        split; [exact (mem_word_only l _ _ s s' Ho M7) |].
        split; [exact (mem_word_only l _ _ s s' Ho M8) |].
        split; [exact (mem_word_only l _ _ s s' Ho M9) |].
        split; [exact (mem_word_only l _ _ s s' Ho M10) |].
        split; [exact (mem_word_only l _ _ s s' Ho M11) |].
        split; [exact (mem_word_only l _ _ s s' Ho M12) |].
        split; [exact (mem_word_only l _ _ s s' Ho M13) |].
        split; [exact (mem_word_only l _ _ s s' Ho M14) |].
        exact (exec_init_src_1_only l _ _ s s' Ho Hf).
Qed.

(* A call keeps the code: it keeps the memory. *)
Lemma main_1_prog_kept s s' :
        abi_opt_stepcond_preserve_mem s s' ->
        abi_stepcond_preserve_conf s s' ->
        main_1_prog s ->
                main_1_prog s'.
Proof.
        intros Hm Hi (H0 & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & Hf).
        unfold abi_opt_stepcond_preserve_mem in Hm.
        split; [exact (conf_keep s s' Hi H0) |].
        unfold mem_word in *. rewrite <- Hm.
        repeat (split; [assumption |]).
        exact (exec_init_src_1_mem _ _ s s' (eq_sym Hm) Hf).
Qed.

Lemma main_1_stage_pc k s :
        main_1_stage k s ->
                _pc_addr s = main_1_pc k.
Proof.
        intros (_ & Hpc & _). apply (reg_pc _ _ Hpc).
        do 47 (destruct k as [| k]; [cbn; lia |]). cbn; lia.
Qed.

(* A tick keeps the stage. *)
Lemma main_1_tick k s s' :
        main_1_stage k s ->
        only (T.R_bitvector_64 T.mcycle :: T.R_bitvector_64 T.mtime :: nil) s s' ->
                main_1_stage k s'.
Proof.
        intros (Hp & Hpc & Hx) Hl.
        split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
        split; [exact (reg_only _ _ _ _ _ Hl Hpc eq_refl) |].
        destruct k as [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| k]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
                cbn [main_1_regs] in *;
                repeat match goal with
                        | H : _ /\ _ |- _ => destruct H
                        end;
                regs_after Hl.
Qed.

(* Consecutive stages are at different addresses. *)
Lemma main_1_stage_succ_ne k s :
        (k < 47)%nat ->
        main_1_stage k s ->
        main_1_stage (S k) s ->
                False.
Proof.
        intros Hk Hs Hs'.
        pose proof (main_1_stage_pc k s Hs) as P1. pose proof (main_1_stage_pc (S k) s Hs') as P2.
        rewrite P1 in P2. clear - Hk P2.
        do 47 (destruct k as [| k]; [cbn [main_1_pc] in P2; lia |]). lia.
Qed.

(* ========================================================================== *)
(* One instruction                                                            *)
(* ========================================================================== *)

Section run.

(* A step from stage `k`, an instruction of main. *)
Lemma main_1_step_main k s :
        (k < 47)%nat ->
        main_1_call k = false ->
        main_1_stage k s ->
                forall n b, exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ main_1_stage (S k) s'.
Proof.
        intros Hk Hc (Hp & Hpc & Hx) n b.
        pose proof Hp as (Hi & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & Hf).
        destruct k as [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| k]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia ].
        all: cbn [main_1_pc main_1_regs] in Hpc, Hx.
        - (* 0: main + 0 *)
          rename Hx into X2.
          destruct (main_1_ins_0 n b s Hi Hpc M0) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 1: main + 4 *)
          destruct Hx as (X2 & X9).
          destruct (main_1_ins_1 n b s Hi Hpc M1) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 2: main + 8 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_2_2 n b s Hi Hpc X9 M2) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 3: main + 12 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_3_4 n b s Hi Hpc X9 M3) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 4: main + 16 *)
          destruct Hx as (X2 & X9 & X18 & X11).
          destruct (main_1_ins_4 n b s Hi Hpc M4) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 5: main + 20 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_5 n b s Hi Hpc X10 M5) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 6: main + 24 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_6 n b s Hi Hpc M6) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 7: main + 28 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10 & X1).
          destruct (main_1_ins_7 n b s Hi Hpc X1 M7) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 8: printf *)
          cbn in Hc. discriminate Hc.
        - (* 9: main + 32 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_8_4 n b s Hi Hpc X18 M8) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 10: main + 36 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_9_3 n b s Hi Hpc X18 M9) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 11: main + 40 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_10 n b s Hi Hpc M10) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 12: main + 44 *)
          destruct Hx as (X2 & X9 & X18 & X5).
          destruct (main_1_ins_11 n b s Hi Hpc X5 M11) as (s' & Ho & Hl & He & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 13: main + 8 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_2_4 n b s Hi Hpc X9 M2) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 14: main + 12 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_3_8 n b s Hi Hpc X9 M3) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 15: main + 16 *)
          destruct Hx as (X2 & X9 & X18 & X11).
          destruct (main_1_ins_4 n b s Hi Hpc M4) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 16: main + 20 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_5 n b s Hi Hpc X10 M5) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 17: main + 24 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_6 n b s Hi Hpc M6) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 18: main + 28 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10 & X1).
          destruct (main_1_ins_7 n b s Hi Hpc X1 M7) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 19: printf *)
          cbn in Hc. discriminate Hc.
        - (* 20: main + 32 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_8_3 n b s Hi Hpc X18 M8) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 21: main + 36 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_9_2 n b s Hi Hpc X18 M9) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 22: main + 40 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_10 n b s Hi Hpc M10) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 23: main + 44 *)
          destruct Hx as (X2 & X9 & X18 & X5).
          destruct (main_1_ins_11 n b s Hi Hpc X5 M11) as (s' & Ho & Hl & He & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 24: main + 8 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_2_8 n b s Hi Hpc X9 M2) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 25: main + 12 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_3_16 n b s Hi Hpc X9 M3) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 26: main + 16 *)
          destruct Hx as (X2 & X9 & X18 & X11).
          destruct (main_1_ins_4 n b s Hi Hpc M4) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 27: main + 20 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_5 n b s Hi Hpc X10 M5) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 28: main + 24 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_6 n b s Hi Hpc M6) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 29: main + 28 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10 & X1).
          destruct (main_1_ins_7 n b s Hi Hpc X1 M7) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 30: printf *)
          cbn in Hc. discriminate Hc.
        - (* 31: main + 32 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_8_2 n b s Hi Hpc X18 M8) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 32: main + 36 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_9_1 n b s Hi Hpc X18 M9) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 33: main + 40 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_10 n b s Hi Hpc M10) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 34: main + 44 *)
          destruct Hx as (X2 & X9 & X18 & X5).
          destruct (main_1_ins_11 n b s Hi Hpc X5 M11) as (s' & Ho & Hl & He & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 35: main + 8 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_2_16 n b s Hi Hpc X9 M2) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 36: main + 12 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_3_32 n b s Hi Hpc X9 M3) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 37: main + 16 *)
          destruct Hx as (X2 & X9 & X18 & X11).
          destruct (main_1_ins_4 n b s Hi Hpc M4) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 38: main + 20 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_5 n b s Hi Hpc X10 M5) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 39: main + 24 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10).
          destruct (main_1_ins_6 n b s Hi Hpc M6) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 40: main + 28 *)
          destruct Hx as (X2 & X9 & X18 & X11 & X10 & X1).
          destruct (main_1_ins_7 n b s Hi Hpc X1 M7) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 41: printf *)
          cbn in Hc. discriminate Hc.
        - (* 42: main + 32 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_8_1 n b s Hi Hpc X18 M8) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 43: main + 36 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_9_0 n b s Hi Hpc X18 M9) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 44: main + 48 *)
          destruct Hx as (X2 & X9 & X18).
          destruct (main_1_ins_12 n b s Hi Hpc M12) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 45: main + 52 *)
          destruct Hx as (X2 & X9 & X18 & X10).
          destruct (main_1_ins_13 n b s Hi Hpc M13) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
        - (* 46: main + 56 *)
          destruct Hx as (X2 & X9 & X18 & X10 & X1).
          destruct (main_1_ins_14 n b s Hi Hpc X1 M14) as (s' & Ho & Hl & He & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (main_1_prog_only_elp _ _ _ Hl eq_refl He Hp) |].
          split; [exact Hpc' |]. cbn [main_1_regs]. regs_after Hl.
Qed.

Lemma main_1_step_tla k s :
        (k < 47)%nat ->
        main_1_call k = false ->
        main_1_stage k s ->
                (forall s', exec_eval_step_1 s s' -> main_1_stage (S k) s')
                /\ (exists s', exec_eval_step_1 s s' /\ main_1_stage (S k) s').
Proof.
        intros Hk Hc Hs. exact (step_tla s _ (main_1_step_main k s Hk Hc Hs)).
Qed.

End run.

(* ========================================================================== *)
(* printf and exit                                                            *)
(* ========================================================================== *)

(* At a call: printf with what it expects, the return address after the call. *)
Lemma main_1_call_at k s :
        main_1_call k = true ->
        main_1_stage k s ->
                _pc_addr s = e_static "printf"%string
                /\ _printf_precond s
                /\ abi_precond s
                /\ abi_ra s = 0x10020
                /\ abi_sp s = 0x4000000000.
Proof.
        intros Hc Hs. pose proof (main_1_stage_pc k s Hs) as Hpc.
        destruct Hs as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf) & _ & Hx).
        assert (Hk : k = 8%nat \/ k = 19%nat \/ k = 30%nat \/ k = 41%nat).
        { unfold main_1_call in Hc.
          destruct (Nat.eqb_spec k 8), (Nat.eqb_spec k 19), (Nat.eqb_spec k 30), (Nat.eqb_spec k 41);
                cbn in Hc; first [ discriminate Hc | lia ]. }
        destruct Hk as [-> | [-> | [-> | ->]]];
                cbn [main_1_regs] in Hx; destruct Hx as (X2 & X9 & X18 & X11 & X10 & X1);
                (split; [exact Hpc |]);
                (split;
                        [ apply (main_2_fmt s Hf); unfold abi_arg0, abi_a0;
                                exact (reg_abi _ _ _ X10 ltac:(lia)) |]);
                (split;
                        [ unfold abi_precond, abi_sp; rewrite (reg_abi _ _ _ X2 ltac:(lia)); reflexivity |]);
                (split;
                        [ unfold abi_ra; exact (reg_abi _ _ _ X1 ltac:(lia))
                        | unfold abi_sp; exact (reg_abi _ _ _ X2 ltac:(lia)) ]).
Qed.

(* The return from a call: the stage after. *)
Lemma main_1_ret k s s' :
        main_1_call k = true ->
        main_1_stage k s ->
        abi_stepcond s s'
                /\ abi_opt_stepcond_preserve_mem s s'
                /\ abi_opt_stepcond_return s s' ->
                main_1_stage (S k) s'.
Proof.
        intros Hc Hs ((Hregs & Hconf) & Hmem & Hret).
        destruct (main_1_call_at k s Hc Hs) as (_ & _ & _ & Hra & _).
        destruct Hs as (Hp & _ & Hx).
        assert (Hk : k = 8%nat \/ k = 19%nat \/ k = 30%nat \/ k = 41%nat).
        { unfold main_1_call in Hc.
          destruct (Nat.eqb_spec k 8), (Nat.eqb_spec k 19), (Nat.eqb_spec k 30), (Nat.eqb_spec k 41);
                cbn in Hc; first [ discriminate Hc | lia ]. }
        split; [exact (main_1_prog_kept s s' Hmem Hconf Hp) |].
        unfold abi_opt_stepcond_return in Hret. rewrite Hra in Hret.
        destruct Hk as [-> | [-> | [-> | ->]]];
                cbn [main_1_regs] in Hx; destruct Hx as (X2 & X9 & X18 & _ & _ & _);
                (split; [apply pc_reg; exact Hret |]);
                cbn [main_1_regs];
                repeat match goal with
                        | |- _ /\ _ => split
                        end;
                (eapply reg_preserved; [exact Hregs | reflexivity | eassumption]).
Qed.

(* At the exit. *)
Lemma main_1_exit_at s :
        main_1_stage 47 s ->
                _pc_addr s = e_static "exit"%string
                /\ abi_precond s.
Proof.
        intros Hs. pose proof (main_1_stage_pc 47 s Hs) as Hpc.
        destruct Hs as (_ & _ & Hx). cbn [main_1_regs] in Hx. destruct Hx as (X2 & _ & _ & _ & _).
        split; [exact Hpc |].
        unfold abi_precond, abi_sp. rewrite (reg_abi _ _ _ X2 ltac:(lia)). reflexivity.
Qed.

(* Every stage but the calls and the exit is in the text of main. *)
Lemma main_1_at_main k s :
        main_1_call k = false ->
        (k < 47)%nat ->
        main_1_stage k s ->
                at_pc (main_1.main_sec e_static) (e_static "main"%string) s.
Proof.
        intros Hc Hk Hs. unfold at_pc. rewrite (main_1_stage_pc k s Hs).
        change (_section_size (main_1.main_sec e_static)) with 60.
        change (e_static "main"%string) with 0x10000.
        do 47 (destruct k as [| k]; [cbn [main_1_pc]; first [ lia | (cbn in Hc; discriminate Hc) ] |]). lia.
Qed.

(* What is seen: 32 at the fourth call, nothing else. *)
Lemma main_1_obs k s :
        (k <= 47)%nat ->
        main_1_stage k s ->
                rm e_static s = if (k =? 41)%nat then Some 32 else None.
Proof.
        intros Hk Hs. pose proof (main_1_stage_pc k s Hs) as Hpc.
        destruct Hs as (_ & _ & Hx). unfold rm, prints. rewrite Hpc.
        destruct k as [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| k]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia ];
                try reflexivity.
        all: cbn [main_1_regs] in Hx; destruct Hx as (_ & _ & _ & X11 & _ & _);
                unfold abi_arg1, abi_a1; rewrite (reg_abi _ _ _ X11 ltac:(lia)); reflexivity.
Qed.

(* ========================================================================== *)
(* The first state                                                            *)
(* ========================================================================== *)

Lemma main_1_start (sigma : behavior state) :
        exec_static main_1_s sigma ->
                main_1_stage 0 (sigma 0%nat).
Proof.
        intros (Hi & Hpc & Hsp & Hsrc & _ & _).
        destruct Hsrc as ((_ & Hmain) & Hfmt).
        unfold Lift1 in Hi, Hpc, Hsp, Hfmt, Hmain.
        let l := eval vm_compute in (main_1.main_sec e_static) in
        change (main_1.main_sec e_static) with l in Hmain.
        change (e_static "main"%string) with 0x10000 in Hmain.
        cbn [exec_init_src_1 _init_s_text] in Hmain.
        destruct Hmain as (((((((((((((((_ & I14) & I13) & I12) & I11) & I10) & I9) & I8) & I7) & I6) & I5) & I4) & I3) & I2) & I1) & I0).
        instr_word I0. instr_word I1. instr_word I2. instr_word I3. instr_word I4. instr_word I5. instr_word I6. instr_word I7. instr_word I8. instr_word I9. instr_word I10. instr_word I11. instr_word I12. instr_word I13. instr_word I14.
        change (e_static ".tl_fmt"%string) with 0x100000 in Hfmt.
        split; [| split].
        - exact (conj Hi (conj I0 (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj I11 (conj I12 (conj I13 (conj I14 Hfmt)))))))))))))))).
        - apply pc_reg. exact Hpc.
        - cbn [main_1_regs]. exact (reg_sp _ Hsp).
Qed.

(* ========================================================================== *)
(* A behaviour, stage by stage                                                *)
(* ========================================================================== *)

(* What a behaviour of main_1 and the libc allows a step to do: main's, printf's and exit's. *)
Definition main_1_next (s s' : state) : Prop :=
        ((at_pc (main_1.main_sec e_static) (e_static "main"%string) s ->
                exec_eval_step_1 s s' \/ exec_eval_step_2 s s') \/ s = s')
        /\ ((_pc_addr s = e_static "printf"%string ->
                _printf_precond s ->
                        abi_precond s ->
                                abi_stepcond s s'
                                /\ abi_opt_stepcond_preserve_mem s s'
                                /\ abi_opt_stepcond_return s s') \/ s = s')
        /\ ((_pc_addr s = e_static "exit"%string ->
                abi_precond s ->
                        s' = s) \/ s = s').

Lemma main_1_next_at (sigma : behavior state) :
        exec_static main_1_s sigma ->
        unsafe_libc e_static sigma ->
                forall i, main_1_next (sigma i) (sigma (S i)).
Proof.
        intros Hmain Hlibc i.
        destruct Hmain as (_ & _ & _ & _ & Hnext & _).
        destruct Hnext as ((_ & Hnext) & _).
        destruct Hlibc as ((Hprintf & _) & Hexit & _).
        split; [| split].
        - exact (next_at sigma _ Hnext i).
        - exact (next_at sigma _ Hprintf i).
        - exact (next_at sigma _ Hexit i).
Qed.

Section behaviour.

(* A step stays at the stage or goes to the next. *)
Lemma main_1_step k s s' :
        (k < 47)%nat ->
        main_1_stage k s ->
        main_1_next s s' ->
                main_1_stage k s' \/ main_1_stage (S k) s'.
Proof.
        intros Hk Hs (Hm & Hp & _).
        destruct (main_1_call k) eqn:Hc.
        - destruct Hp as [Hp | <-]; [| left; exact Hs].
          right. apply (main_1_ret k s s' Hc Hs).
          destruct (main_1_call_at k s Hc Hs) as (Hpc & Hpre & Habi & _). exact (Hp Hpc Hpre Habi).
        - destruct Hm as [Hm | <-]; [| left; exact Hs].
          destruct (Hm (main_1_at_main k s Hc Hk Hs)) as [Hok | Htick].
          + right. exact (proj1 (main_1_step_tla k s Hk Hc Hs) s' Hok).
          + left. exact (main_1_tick k s s' Hs (tick_tla s s' Htick)).
Qed.

(* The exit, for ever. *)
Lemma main_1_step_end s s' :
        main_1_stage 47 s ->
        main_1_next s s' ->
                main_1_stage 47 s'.
Proof.
        intros Hs (_ & _ & He).
        destruct He as [He | <-]; [| exact Hs].
        destruct (main_1_exit_at s Hs) as (Hpc & Hpre). rewrite (He Hpc Hpre). exact Hs.
Qed.

(* Every stage but the exit is left, by the fairness of main or of printf. *)
Lemma main_1_progress (sigma : behavior state) k :
        exec_static main_1_s sigma ->
        unsafe_libc e_static sigma ->
        (k < 47)%nat ->
        forall i,
        main_1_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ main_1_stage (S k) (sigma j).
Proof.
        intros Hmain Hlibc Hk.
        pose proof (main_1_next_at sigma Hmain Hlibc) as Hn.
        assert (Hst : forall i, main_1_stage k (sigma i) ->
                main_1_stage k (sigma (S i)) \/ main_1_stage (S k) (sigma (S i)))
                by (intros i Hi; exact (main_1_step k _ _ Hk Hi (Hn i))).
        destruct (main_1_call k) eqn:Hc.
        - destruct Hlibc as ((_ & Hwf) & _).
          apply (leads_wf sigma _ (main_1_stage k) (main_1_stage (S k)) Hwf Hst).
          + intros s Hs. destruct (main_1_call_at k s Hc Hs) as (Hpc & Hpre & Habi & Hra & _).
            exists (ret_to 0x10020 s). split.
            * split; [exact Hpc |]. split; [exact Hpre |]. split; [exact Habi |].
              exact (ret_to_abi 0x10020 s ltac:(lia) Hra).
            * apply ret_to_ne; [lia |]. rewrite Hpc. cbn. lia.
          + intros s s' Hs (_ & _ & _ & Ha). exact (main_1_ret k s s' Hc Hs Ha).
        - destruct Hmain as (_ & _ & _ & _ & _ & Hwf). destruct Hwf as ((_ & Hwf) & _).
          apply (leads_wf sigma (exec_fair_src_1 (main_1.main_sec e_static) (e_static "main"%string))
                (main_1_stage k) (main_1_stage (S k)) Hwf Hst).
          + intros s Hs.
            destruct (main_1_step_tla k s Hk Hc Hs) as (_ & (s' & Hok & Hs')).
            exists s'. split.
            * split; [exact (main_1_at_main k s Hc Hk Hs) | exact Hok].
            * intros <-. exact (main_1_stage_succ_ne k s Hk Hs Hs').
          + intros s s' Hs (_ & Hok).
            exact (proj1 (main_1_step_tla k s Hk Hc Hs) s' Hok).
Qed.

(* What is seen of a behaviour: nothing, 32 from `k` to `k + m`, nothing. *)
Lemma main_1_obs_shape (sigma : behavior state) :
        exec_static main_1_s sigma ->
        unsafe_libc e_static sigma ->
                exists k m,
                (5 <= k)%nat
                /\ (1 <= m)%nat
                /\ forall n,
                        rm e_static (sigma n)
                                = if andb (k <=? n)%nat (n <? k + m)%nat then Some 32 else None.
Proof.
        intros Hmain Hlibc.
        pose proof (main_1_next_at sigma Hmain Hlibc) as Hn.
        pose proof (main_1_start sigma Hmain) as H0.
        (* every state is at a stage, no later than its index *)
        assert (F1 : forall n, exists j, (j <= n)%nat /\ (j <= 47)%nat /\ main_1_stage j (sigma n)).
        { induction n as [| n IH].
          - exists 0%nat. split; [lia | split; [lia | exact H0]].
          - destruct IH as (j & Hj & HjE & Hs).
            destruct (Nat.lt_ge_cases j 47) as [Hlt | Hge].
            + destruct (main_1_step j _ _ Hlt Hs (Hn n)) as [H | H].
              * exists j. split; [lia | split; [lia | exact H]].
              * exists (S j). split; [lia | split; [lia | exact H]].
            + assert (j = 47%nat) as -> by lia.
              exists 47%nat. split; [lia | split; [lia | exact (main_1_step_end _ _ Hs (Hn n))]]. }
        (* the stage never decreases *)
        assert (F2 : forall n j, (j <= 47)%nat -> main_1_stage j (sigma n) ->
                forall d, exists j', (j <= j' <= 47)%nat /\ main_1_stage j' (sigma (n + d)%nat)).
        { intros n j Hj Hs d. induction d as [| d IH].
          - exists j. rewrite Nat.add_0_r. split; [lia | exact Hs].
          - destruct IH as (j' & Hj' & Hs'). rewrite Nat.add_succ_r.
            destruct (Nat.lt_ge_cases j' 47) as [Hlt | Hge].
            + destruct (main_1_step j' _ _ Hlt Hs' (Hn (n + d)%nat)) as [H | H].
              * exists j'. split; [lia | exact H].
              * exists (S j'). split; [lia | exact H].
            + assert (j' = 47%nat) as -> by lia.
              exists 47%nat. split; [lia | exact (main_1_step_end _ _ Hs' (Hn (n + d)%nat))]. }
        (* every stage is reached *)
        assert (Hreach : forall p, (p <= 47)%nat -> exists n, main_1_stage p (sigma n)).
        { induction p as [| p IH]; intros Hp.
          - exists 0%nat. exact H0.
          - destruct (IH ltac:(lia)) as (n & Hs).
            destruct (main_1_progress sigma p Hmain Hlibc ltac:(lia) n Hs) as (n' & _ & Hs').
            exists n'. exact Hs'. }
        (* the first 32 *)
        destruct (least (fun n => rm e_static (sigma n) = Some 32)) as (k & Hk & Hkmin).
        { destruct (Hreach 41%nat ltac:(lia)) as (n & Hs). exists n. cbv beta.
          rewrite (main_1_obs 41 _ ltac:(lia) Hs). reflexivity. }
        cbv beta in Hk, Hkmin.
        assert (HC : main_1_stage 41 (sigma k) /\ (41 <= k)%nat).
        { destruct (F1 k) as (j & Hjk & Hj & Hs).
          rewrite (main_1_obs j _ Hj Hs) in Hk.
          destruct (j =? 41)%nat eqn:E; [| discriminate Hk].
          apply Nat.eqb_eq in E. rewrite E in Hs, Hjk. split; [exact Hs | exact Hjk]. }
        destruct HC as (HC & HkC).
        (* the first nothing after it *)
        destruct (least (fun n => (k < n)%nat /\ rm e_static (sigma n) = None)) as (e & He & Hemin).
        { destruct (main_1_progress sigma 41 Hmain Hlibc ltac:(lia) k HC) as (n' & Hn' & Hs').
          exists n'. cbv beta. rewrite (main_1_obs 42 _ ltac:(lia) Hs'). split; [| reflexivity].
          destruct (Nat.eq_dec n' k) as [-> | Hne]; [| lia].
          exfalso. rewrite (main_1_obs 42 _ ltac:(lia) Hs') in Hk. discriminate Hk. }
        cbv beta in He, Hemin. destruct He as (Hke & He).
        exists k, (e - k)%nat. split; [lia |]. split; [lia |].
        intros n.
        destruct (Nat.leb_spec k n) as [Hkn | Hkn];
                destruct (Nat.ltb_spec n (k + (e - k))) as [Hne | Hne]; cbn [andb].
        - destruct (Nat.eq_dec n k) as [-> | Hnk]; [exact Hk |].
          unfold rm. destruct (prints _ _ _) eqn:Hb; [reflexivity |].
          exfalso. apply (Hemin n); [lia |]. split; [lia |]. unfold rm. rewrite Hb. reflexivity.
        - destruct (F2 k 41%nat ltac:(lia) HC (e - k)%nat) as (j' & Hj' & Hs').
          replace (k + (e - k))%nat with e in Hs' by lia.
          rewrite (main_1_obs j' _ ltac:(lia) Hs') in He.
          destruct (j' =? 41)%nat eqn:E'; [discriminate He |].
          apply Nat.eqb_neq in E'.
          destruct (F2 e j' ltac:(lia) Hs' (n - e)%nat) as (j'' & Hj'' & Hs'').
          replace (e + (n - e))%nat with n in Hs'' by lia.
          rewrite (main_1_obs j'' _ ltac:(lia) Hs'').
          destruct (j'' =? 41)%nat eqn:E''; [| reflexivity].
          apply Nat.eqb_eq in E''. lia.
        - unfold rm. destruct (prints _ _ _) eqn:Hb; [| reflexivity].
          exfalso. apply (Hkmin n); [lia |]. unfold rm. rewrite Hb. reflexivity.
        - lia.
Qed.

End behaviour.

(* ========================================================================== *)
(* The text of main_2 in memory                                               *)
(* ========================================================================== *)

(* The words of `main_2.main_sec e_static`. *)
Definition main_2_words : list Z :=
        33555859 :: 1049911 :: 328979 :: 82103 :: 32999 ::
        1299 :: 82103 :: 268468455 :: nil.

(* Byte `i` of the text of main_2, little-endian. *)
Definition main_2_byte (i : Z) : definitions.bv 8 :=
        definitions.Z_to_bv 8 (Z.shiftr (nth (Z.to_nat (i / 4)) main_2_words 0) (8 * (i mod 4))).

(* The state `s` with the text of main_2 at main. *)
Definition main_2_put (s : state) : state :=
        Build_state (st_regs s) (fun a =>
                if andb (0x10000 <=? definitions.bv_unsigned a) (definitions.bv_unsigned a <? 0x10020)
                        then main_2_byte (definitions.bv_unsigned a - 0x10000)
                        else st_mem s a).

Lemma main_2_put_outside s a :
        ~ (0x10000 <= definitions.bv_unsigned a < 0x10020) ->
                st_mem (main_2_put s) a = st_mem s a.
Proof.
        intros Hr. cbn [st_mem main_2_put].
        destruct (Z.leb_spec 0x10000 (definitions.bv_unsigned a)),
                (Z.ltb_spec (definitions.bv_unsigned a) 0x10020); cbn [andb];
                first [ reflexivity | lia ].
Qed.

(* A section of bytes outside the text of main_2 stays in memory. *)
Lemma main_2_put_data stmnts addr s :
        0 <= addr ->
        addr + Z.of_nat (List.length stmnts) <= 2 ^ 64 ->
        addr + Z.of_nat (List.length stmnts) <= 0x10000 \/ 0x10020 <= addr ->
        _init_s_data stmnts addr s ->
                _init_s_data stmnts addr (main_2_put s).
Proof.
        intros H0 H1 Ha. apply init_s_data_bytes; [lia | lia |].
        intros a Hr. apply main_2_put_outside. lia.
Qed.

(* The text of main_2 is in memory. *)
Lemma main_2_put_text s :
        exec_init_src_1 (main_2.main_sec e_static) (e_static "main"%string) (main_2_put s).
Proof.
        let l := eval vm_compute in (main_2.main_sec e_static) in
        change (main_2.main_sec e_static) with l.
        change (e_static "main"%string) with 0x10000.
        cbn [exec_init_src_1 _init_s_text].
        repeat match goal with
                | |- _ /\ _ => split
                | |- True => exact I
                end.
        all: instr_intro.
Qed.

(* The length of a closed list, computed. *)
Ltac length_closed :=
        repeat match goal with
                | |- context [List.length ?l] =>
                        let n := eval vm_compute in (List.length l) in
                        change (List.length l) with n
                end.

(* ========================================================================== *)
(* thm_2                                                                      *)
(* ========================================================================== *)

Section thm.

Theorem thm_2 :
        valid ((\rmap (rm e_static)
                        (exec_static main_1_s \land unsafe_libc e_static))
                \impl (\rmap (rm e_static)
                        (exec_static main_2_s \land unsafe_libc e_static))).
Proof.
        intros beh2 (beh1 & Heq & Hmain & Hlibc).
        destruct (main_1_obs_shape beh1 Hmain Hlibc) as (k & m & Hk & Hm & Hobs).
        (* the first state of main_1 *)
        pose proof Hmain as (Hi & Hpc & Hsp & Hinit & _).
        destruct Hinit as ((_ & _) & Hfmt).
        (* the first state of main_2 *)
        pose proof (main_2_put_text (beh1 0%nat)) as Htext.
        assert (Hfmt' : exec_init_src_1 main_2._tl_fmt_sec (e_static ".tl_fmt"%string)
                        (main_2_put (beh1 0%nat))).
        { unfold main_1._tl_fmt_sec in Hfmt. unfold main_2._tl_fmt_sec.
          cbn [exec_init_src_1] in Hfmt |- *.
          change (e_static ".tl_fmt"%string) with 0x100000 in Hfmt |- *.
          apply main_2_put_data; [lia | length_closed; lia | length_closed; lia | exact Hfmt]. }
        pose proof (main_2_start_state (main_2_put (beh1 0%nat)) Hi Hpc Hsp Hfmt' Htext) as T0.
        (* the run of main_2 *)
        destruct (main_2_step 0 _ ltac:(lia) ltac:(lia) T0 0 true) as (t1 & O1 & T1).
        destruct (main_2_step 1 _ ltac:(lia) ltac:(lia) T1 0 true) as (t2 & O2 & T2).
        destruct (main_2_step 2 _ ltac:(lia) ltac:(lia) T2 0 true) as (t3 & O3 & T3).
        destruct (main_2_step 3 _ ltac:(lia) ltac:(lia) T3 0 true) as (t4 & O4 & T4).
        destruct (main_2_step 4 _ ltac:(lia) ltac:(lia) T4 0 true) as (t5 & O5 & T5).
        pose proof (main_2_ret_stage t5 T5) as T6.
        destruct (main_2_step 6 _ ltac:(lia) ltac:(lia) T6 0 true) as (t7 & O7 & T7).
        destruct (main_2_step 7 _ ltac:(lia) ltac:(lia) T7 0 true) as (t8 & O8 & T8).
        destruct (main_2_step 8 _ ltac:(lia) ltac:(lia) T8 0 true) as (t9 & O9 & T9).
        pose (t := fun j : nat =>
                match j with
                        | 0%nat  => main_2_put (beh1 0%nat)
                        | 1%nat  => t1
                        | 2%nat  => t2
                        | 3%nat  => t3
                        | 4%nat  => t4
                        | 5%nat  => t5
                        | 6%nat  => main_2_ret t5
                        | 7%nat  => t7
                        | 8%nat  => t8
                        | _      => t9
                        end).
        assert (Ht : forall j, (j <= 9)%nat -> main_2_stage j (t j)).
        { intros j Hj.
          destruct j as [| [| [| [| [| [| [| [| [| [| j]]]]]]]]]];
                [ exact T0 | exact T1 | exact T2 | exact T3 | exact T4 | exact T5 | exact T6 | exact T7 | exact T8 | exact T9 | lia ]. }
        assert (Hok : forall j, (j < 9)%nat -> j <> 5%nat -> exec_eval_step_1 (t j) (t (S j))).
        { intros j Hj Hc.
          destruct j as [| [| [| [| [| [| [| [| [| j]]]]]]]]];
                [ exact (step_1_of _ _ O1)
                | exact (step_1_of _ _ O2)
                | exact (step_1_of _ _ O3)
                | exact (step_1_of _ _ O4)
                | exact (step_1_of _ _ O5)
                | exfalso; exact (Hc eq_refl)
                | exact (step_1_of _ _ O7)
                | exact (step_1_of _ _ O8)
                | exact (step_1_of _ _ O9)
                | lia ]. }
        assert (Hret : t 6%nat = main_2_ret (t 5%nat)) by reflexivity.
        change (main_2_put (beh1 0%nat)) with (t 0%nat) in Hfmt', Htext.
        (* the paced run, with the same images *)
        exists (paced t k m). split.
        - destruct Heq as (f & g & Hf & Hg & Hfs & Hgs & Hfg).
          exists f, g. split; [exact Hf |]. split; [exact Hg |].
          split; [exact Hfs |]. split; [exact Hgs |].
          intros n. rewrite <- (Hfg n). cbv beta.
          rewrite paced_obs by assumption. rewrite Hobs. reflexivity.
        - split.
          + apply paced_main_2_tla; assumption.
          + apply paced_libc_tla; assumption.
Qed.

End thm.

(* The statement of thm.v. *)
Definition thm_2_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.print32.thm.thm_2 in exact t) :=
        thm_2.

Print Assumptions thm_2.
