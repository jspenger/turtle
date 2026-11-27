(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Logic.Classical.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require SailStdpp.MachineWord.
Require SailStdpp.Operators_mwords.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.tla.TLA.
Require Import turtle.gen.base.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.conf.preserve_conf.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.glu.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.
Require Import turtle.gen.reg.
Require Import turtle.gen.ev.
Require Import turtle.gen.step.
Require Import turtle.gen.word.
Require turtle.gen.bits.
Require Import turtle.gen.tla.
Require Import turtle.gen.load.
Require Import turtle.compat.sail.riscv.examples.fib.conf_default.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require turtle.compat.sail.riscv.examples.fib.spec_tla.
Require Import turtle.compat.sail.riscv.examples.fib.spec.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Module T := rv64d_types.
Module B := stdpp.bitvector.definitions.
Module O := SailStdpp.Operators_mwords.
Module W := SailStdpp.MachineWord.MachineWord.
Module U := turtle.gen.bits.

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
(* A branch on an unknown register                                            *)
(* ========================================================================== *)

(* `beq rs1, zero, _` with `rs1` not 0: not taken. *)
Lemma eq_zero_reg (c : Z) :
        c mod 2 ^ 64 <> 0 ->
                O.eq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 c)) (rv64d.regval_from_reg rv64d.zero_reg) = false.
Proof.
        intros H. unfold rv64d.regval_from_reg.
        rewrite U.eq_vec_unsigned.
        replace (B.bv_unsigned rv64d.zero_reg) with 0 by (vm_compute; reflexivity).
        match goal with
                | |- context [Z.eqb ?a 0] =>
                        destruct (Z.eqb_spec a 0) as [E | E]; [exfalso; apply H; exact E | reflexivity]
                end.
Qed.

(* `ev_extra` of word.v, with the branch of `beq`. *)
Ltac ev_extra ::=
        first
                [ match goal with
                        | H : ?c mod 2 ^ 64 <> 0
                          |- context [O.eq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 ?c))
                                        (rv64d.regval_from_reg rv64d.zero_reg)] =>
                                ev_replace (eq_zero_reg c H)
                        end
                | progress (try unfold rv64d.is_aligned_paddr; try unfold rv64d.is_aligned_vaddr);
                  cbv beta iota ].

(* ========================================================================== *)
(* The instructions of tl_fib up to the first branch.                         *)
(* ========================================================================== *)

Section step.

(* tl_fib + 0: addi a1, zero, 0 *)
Lemma fib_ins_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11000 ->
        mem_word 0x11000 1427 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11004
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 0.
Proof.
        step_tac.
Qed.

(* tl_fib + 4: addi a2, zero, 1 *)
Lemma fib_ins_1 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11004 ->
        mem_word 0x11004 1050131 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x12)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11008
                /\ T.register_lookup (T.R_bitvector_64 T.x12) (st_regs s') = definitions.Z_to_bv 64 1.
Proof.
        step_tac.
Qed.

(* tl_fib + 8: addi a3, a0, 0 *)
Lemma fib_ins_2 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11008 ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x11008 329363 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x13)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1100c
                /\ T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s') = definitions.Z_to_bv 64 v.
Proof.
        step_tac_sym.
Qed.

(* tl_fib + 12: beq a3, zero, 8, a3 = 0 *)
Lemma fib_ins_3_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1100c ->
        T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s) = definitions.Z_to_bv 64 0 ->
        mem_word 0x1100c 427107 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11014.
Proof.
        step_tac.
Qed.

(* tl_fib + 12: beq a3, zero, 8, a3 not 0 *)
Lemma fib_ins_3 n b s c :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1100c ->
        T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s) = definitions.Z_to_bv 64 c ->
        c mod 2 ^ 64 <> 0 ->
        mem_word 0x1100c 427107 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11010.
Proof.
        step_tac_sym.
Qed.

End step.

(* ========================================================================== *)
(* The jump to the loop, and the return of 0.                                 *)
(* ========================================================================== *)

Section step.

(* tl_fib + 16: jal zero, 12 *)
Lemma fib_ins_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11010 ->
        mem_word 0x11010 12583023 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1101c.
Proof.
        step_tac.
Qed.

(* tl_fib + 20: addi a0, a1, 0 *)
Lemma fib_ins_5 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11014 ->
        T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x11014 361747 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11018
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 v.
Proof.
        step_tac_sym.
Qed.

End step.

(* ========================================================================== *)
(* The loop of tl_fib.                                                        *)
(* ========================================================================== *)

Section step.

(* tl_fib + 28: add a4, a1, a2 *)
Lemma fib_ins_7 n b s x y :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1101c ->
        T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s) = definitions.Z_to_bv 64 x ->
        T.register_lookup (T.R_bitvector_64 T.x12) (st_regs s) = definitions.Z_to_bv 64 y ->
        mem_word 0x1101c 12945203 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x14)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11020
                /\ T.register_lookup (T.R_bitvector_64 T.x14) (st_regs s') = definitions.Z_to_bv 64 (x + y).
Proof.
        step_tac_sym.
Qed.

(* tl_fib + 32: addi a1, a2, 0 *)
Lemma fib_ins_8 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11020 ->
        T.register_lookup (T.R_bitvector_64 T.x12) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x11020 394643 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11024
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 v.
Proof.
        step_tac_sym.
Qed.

(* tl_fib + 36: addi a2, a4, 0 *)
Lemma fib_ins_9 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11024 ->
        T.register_lookup (T.R_bitvector_64 T.x14) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x11024 460307 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x12)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11028
                /\ T.register_lookup (T.R_bitvector_64 T.x12) (st_regs s') = definitions.Z_to_bv 64 v.
Proof.
        step_tac_sym.
Qed.

(* tl_fib + 40: addi a3, a3, -1 *)
Lemma fib_ins_10 n b s c :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11028 ->
        T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s) = definitions.Z_to_bv 64 c ->
        mem_word 0x11028 4294346387 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x13)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1102c
                /\ T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s') = definitions.Z_to_bv 64 (c - 1).
Proof.
        step_tac_sym.
Qed.

End step.

(* ========================================================================== *)
(* The end of the loop of tl_fib.                                             *)
(* ========================================================================== *)

Section step.

(* tl_fib + 44: beq a3, zero, 8, a3 = 0 *)
Lemma fib_ins_11_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1102c ->
        T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s) = definitions.Z_to_bv 64 0 ->
        mem_word 0x1102c 427107 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11034.
Proof.
        step_tac.
Qed.

(* tl_fib + 44: beq a3, zero, 8, a3 not 0 *)
Lemma fib_ins_11 n b s c :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1102c ->
        T.register_lookup (T.R_bitvector_64 T.x13) (st_regs s) = definitions.Z_to_bv 64 c ->
        c mod 2 ^ 64 <> 0 ->
        mem_word 0x1102c 427107 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11030.
Proof.
        step_tac_sym.
Qed.

(* tl_fib + 48: jal zero, -20 *)
Lemma fib_ins_12 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11030 ->
        mem_word 0x11030 4276088943 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1101c.
Proof.
        step_tac.
Qed.

(* tl_fib + 52: addi a0, a1, 0 *)
Lemma fib_ins_13 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11034 ->
        T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x11034 361747 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11038
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 v.
Proof.
        step_tac_sym.
Qed.

End step.

(* ========================================================================== *)
(* The returns of tl_fib, to an unknown even return address.                  *)
(* ========================================================================== *)

Lemma access_unsigned {n : Z} (w : Values.mword n) (i : Z) :
        0 <= i ->
                B.bv_unsigned (O.access_vec_dec w i) = (B.bv_unsigned w / 2 ^ i) mod 2.
Proof.
        intros Hi. unfold O.access_vec_dec, Values.access_mword_dec, W.slice.
        rewrite B.bv_extract_unsigned. unfold B.bv_wrap, B.bv_modulus, W.Z_idx.
        rewrite Z2N.id by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* Bit 0 of a word replaced: the other bits, and the new bit. *)
Lemma update0_unsigned (w : Values.mword 64) (b : Values.mword 1) :
        B.bv_unsigned (O.update_vec_dec w 0 b) = B.bv_unsigned w / 2 * 2 + B.bv_unsigned b.
Proof.
        unfold O.update_vec_dec, Values.update_mword_dec, W.update_slice, W.slice.
        rewrite B.bv_concat_unsigned by reflexivity.
        rewrite B.bv_concat_unsigned by reflexivity.
        rewrite !B.bv_extract_unsigned.
        change (W.Z_idx 64 - W.Z_idx 1 - W.Z_idx 0)%N with 63%N.
        change (Z.of_N (W.Z_idx 0 + W.Z_idx 1)) with 1.
        change (Z.of_N (W.Z_idx 0)) with 0.
        change (W.Z_idx 0) with 0%N.
        change (Z.of_N 0) with 0.
        rewrite Z.shiftl_0_r, Z.shiftr_0_r.
        unfold B.bv_wrap, B.bv_modulus. change (Z.of_N 0) with 0. change (Z.of_N 63) with 63.
        rewrite Z.pow_0_r, Z.mod_1_r, Z.lor_0_r.
        rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
        change (2 ^ 1) with 2. change (2 ^ 63) with 9223372036854775808.
        pose proof (B.bv_unsigned_in_range _ w) as Hw. pose proof (B.bv_unsigned_in_range _ b) as Hb.
        unfold B.bv_modulus in Hw, Hb.
        change (2 ^ Z.of_N (W.Z_idx 64)) with 18446744073709551616 in Hw.
        change (2 ^ Z.of_N (W.Z_idx 1)) with 2 in Hb.
        rewrite (Z.mod_small (B.bv_unsigned w / 2)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        assert (Hl : Z.land (B.bv_unsigned w / 2 * 2) (B.bv_unsigned b) = 0).
        { destruct (Z.eq_dec (B.bv_unsigned b) 0) as [E | E]; [rewrite E; apply Z.land_0_r |].
          replace (B.bv_unsigned b) with (Z.ones 1) by (change (Z.ones 1) with 1; lia).
          rewrite Z.land_ones by lia. change (2 ^ 1) with 2. apply Z.mod_mul. lia. }
        rewrite <- (Z.lxor_lor _ _ Hl), <- (Z.add_nocarry_lxor _ _ Hl). reflexivity.
Qed.

(* The bit written at 0, read again. *)
Lemma access0_update0 (w : Values.mword 64) (b : Values.mword 1) :
        O.access_vec_dec (O.update_vec_dec w 0 b) 0 = b.
Proof.
        apply B.bv_eq. rewrite access_unsigned by lia. rewrite update0_unsigned.
        change (2 ^ 0) with 1. rewrite Z.div_1_r.
        pose proof (B.bv_unsigned_in_range _ b) as Hb. unfold B.bv_modulus in Hb.
        change (2 ^ Z.of_N (W.Z_idx 1)) with 2 in Hb.
        rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* The target of `jalr zero, ra, 0`, `ra` even: `ra`. *)
Lemma ret_target (r : Z) (x : Values.mword 64) (z : Values.mword 1) :
        B.bv_unsigned x = 0 ->
        B.bv_unsigned z = 0 ->
        r mod 2 = 0 ->
                O.update_vec_dec (O.add_vec (B.Z_to_bv 64 r : Values.mword 64) x) 0 z = B.Z_to_bv 64 r.
Proof.
        intros Hx Hz Hr. apply B.bv_eq.
        rewrite update0_unsigned, Hz.
        rewrite (add_vec_mod (n := 64) (B.Z_to_bv 64 r) x), Hx.
        repeat match goal with
                | |- context [?u] =>
                        lazymatch u with B.bv_unsigned (B.Z_to_bv 64 r) => idtac end;
                        let H := fresh "H" in
                        assert (H : u = r mod 18446744073709551616) by exact (Z_to_bv_mod 64 r);
                        rewrite H; clear H
                end.
        change (2 ^ Z.of_N (W.Z_idx 64)) with 18446744073709551616.
        rewrite !Z.add_0_r, Z.mod_mod by lia.
        assert (He : (r mod 18446744073709551616) mod 2 = 0).
        { rewrite Z.mod_mod_divide; [exact Hr |]. exists 9223372036854775808. reflexivity. }
        pose proof (Z.div_mod (r mod 18446744073709551616) 2 ltac:(lia)). lia.
Qed.

(* The assertion of `jump_to` that bit 0 of the target is 0. *)
Ltac ev_decide ::=
        lazymatch goal with
                | |- ?c = _ =>
                        first
                                [ is_closed c; vm_compute; reflexivity
                                | reflexivity
                                | rewrite access0_update0, U.eq_vec_unsigned, Z.eqb_refl; reflexivity ]
                end.

(* After `ev`: the PC of the state of a `ret`. *)
Ltac ret_pc Hr :=
        rewrite ?lookup_if;
        repeat first
                [ rewrite lookup_set_same
                | rewrite lookup_set_other by reflexivity ];
        rewrite ?if_same;
        unfold rv64d.regval_into_reg, rv64d.regval_from_reg;
        apply ret_target; [reflexivity | reflexivity | exact Hr].

Section step.

(* tl_fib + 24: jalr zero, ra, 0: ret, `ra` even *)
Lemma fib_ins_6 n b s r :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11018 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 r ->
        r mod 2 = 0 ->
        mem_word 0x11018 32871 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 r.
Proof.
        intros Hi Hpc Hra Hr Hm.
        conf_intro. unfold mem_word in Hm.
        ev_base s.
        eexists; split.
        - eapply outcome_conv; [ev | reflexivity].
        - split; [only_tac |]. split; [step_value | ret_pc Hr].
Qed.

(* tl_fib + 56: jalr zero, ra, 0: ret, `ra` even *)
Lemma fib_ins_14 n b s r :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x11038 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 r ->
        r mod 2 = 0 ->
        mem_word 0x11038 32871 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 r.
Proof.
        intros Hi Hpc Hra Hr Hm.
        conf_intro. unfold mem_word in Hm.
        ev_base s.
        eexists; split.
        - eapply outcome_conv; [ev | reflexivity].
        - split; [only_tac |]. split; [step_value | ret_pc Hr].
Qed.

End step.

(* ========================================================================== *)
(* Registers                                                                  *)
(* ========================================================================== *)

(* A step that writes fewer registers. *)
Lemma only_incl l l' s s' :
        forallb (reg_in l') l = true ->
        only l s s' ->
                only l' s s'.
Proof.
        intros H (Hm & Ho). split; [exact Hm |].
        intros r Hr. apply Ho.
        destruct (reg_in l r) eqn:E; [| reflexivity]. exfalso.
        unfold reg_in in E. apply existsb_exists in E. destruct E as (x & Hx & Hb).
        apply register_beq_eq in Hb. subst x.
        rewrite forallb_forall in H. rewrite (H r Hx) in Hr. discriminate Hr.
Qed.

(* ========================================================================== *)
(* tl_fib at `e_static`: the section, the facts of a call                     *)
(* ========================================================================== *)

(* The PC is in tl_fib. *)
Definition in_fib (s : state) : Prop :=
        0x11000 <= _pc_addr s < 0x1103c.

Lemma in_fib_at_pc s :
        at_pc (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s <-> in_fib s.
Proof.
        unfold at_pc, in_fib.
        change (_section_size (tl_fib_impl_sec e_static)) with 60.
        change (e_static "tl_fib"%string) with 0x11000. lia.
Qed.

Lemma pc_internal_iff s :
        pc_internal e_static s = true <-> 0x11000 < _pc_addr s < 0x1103c.
Proof.
        unfold pc_internal.
        change (_section_size (tl_fib_impl_sec e_static)) with 60.
        change (e_static "tl_fib"%string) with 0x11000.
        rewrite andb_true_iff, !Z.ltb_lt. lia.
Qed.

Lemma pc_internal_false s :
        pc_internal e_static s = false <-> ~ (0x11000 < _pc_addr s < 0x1103c).
Proof.
        rewrite <- pc_internal_iff. destruct (pc_internal e_static s); split; intros H; congruence.
Qed.

Lemma rm_none s :
        rm e_static s = None <-> pc_internal e_static s = true.
Proof.
        unfold rm. destruct (pc_internal e_static s); split; intros H; congruence.
Qed.

(* The return address is not in tl_fib, as written in `E`. *)
Definition ra_out_tl_fib (e : env) (s : state) : Prop :=
        abi_ra s < e "tl_fib"%string
                \/ e "tl_fib"%string + _section_size (tl_fib_impl_sec e) <= abi_ra s.

Lemma ra_out_tl_fib_iff s :
        ra_out_tl_fib e_static s <-> ~ (0x11000 <= abi_ra s < 0x1103c).
Proof.
        unfold ra_out_tl_fib.
        change (_section_size (tl_fib_impl_sec e_static)) with 60.
        change (e_static "tl_fib"%string) with 0x11000.
        lia.
Qed.

(* What stays true during a call of tl_fib: the configuration, the code, an
        even return address outside tl_fib. *)
Definition fib_facts (s : state) : Prop :=
        conf_default s
        /\ exec_init_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s
        /\ abi_ra s mod 2 = 0
        /\ ra_out_tl_fib e_static s.

Lemma ra_out_tl_fib_only l s s' :
        only l s s' ->
        reg_in l (T.R_bitvector_64 T.x1) = false ->
                abi_ra s' = abi_ra s
                /\ ra_out_tl_fib e_static s' = ra_out_tl_fib e_static s.
Proof.
        intros Ho Hr.
        assert (H : abi_ra s' = abi_ra s) by exact (abi_only l T.x1 s s' Ho Hr).
        split; [exact H |]. unfold ra_out_tl_fib. rewrite H. reflexivity.
Qed.

Lemma fib_facts_only l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs = true ->
        reg_in l (T.R_bitvector_64 T.x1) = false ->
        fib_facts s ->
                fib_facts s'.
Proof.
        intros Ho Hl Hr (Hi & Hc & He & Ha).
        destruct (ra_out_tl_fib_only l s s' Ho Hr) as (E1 & E2).
        split; [exact (conf_default_only l s s' Hl Ho Hi) |].
        split; [exact (exec_init_src_1_only l _ _ s s' Ho Hc) |].
        split; [rewrite E1; exact He | rewrite E2; exact Ha].
Qed.

(* The words of `tl_fib_impl_sec e_static`. *)
Definition fib_words (s : state) : Prop :=
        mem_word 0x11000 1427 s
        /\ mem_word 0x11004 1050131 s
        /\ mem_word 0x11008 329363 s
        /\ mem_word 0x1100c 427107 s
        /\ mem_word 0x11010 12583023 s
        /\ mem_word 0x11014 361747 s
        /\ mem_word 0x11018 32871 s
        /\ mem_word 0x1101c 12945203 s
        /\ mem_word 0x11020 394643 s
        /\ mem_word 0x11024 460307 s
        /\ mem_word 0x11028 4294346387 s
        /\ mem_word 0x1102c 427107 s
        /\ mem_word 0x11030 4276088943 s
        /\ mem_word 0x11034 361747 s
        /\ mem_word 0x11038 32871 s.

Lemma fib_code_words s :
        exec_init_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s ->
                fib_words s.
Proof.
        intros H.
        let l := eval vm_compute in (tl_fib_impl_sec e_static) in
        change (tl_fib_impl_sec e_static) with l in H.
        change (e_static "tl_fib"%string) with 0x11000 in H.
        cbn [exec_init_src_1 _init_s_text] in H.
        destruct H as (((((((((((((((_ & I14) & I13) & I12) & I11) & I10) & I9) & I8) & I7) & I6) & I5) & I4) & I3) & I2) & I1) & I0).
        instr_word I0. instr_word I1. instr_word I2. instr_word I3. instr_word I4.
        instr_word I5. instr_word I6. instr_word I7. instr_word I8. instr_word I9.
        instr_word I10. instr_word I11. instr_word I12. instr_word I13. instr_word I14.
        unfold fib_words. tauto.
Qed.

(* ========================================================================== *)
(* The points of a call of tl_fib                                             *)
(* ========================================================================== *)

(* A point of a call: before the loop (and the return of 0), or in round `i`
        of the loop. *)
Inductive point : Type :=
        | Head (j : nat)
        | Loop (i j : nat).

Definition pt_pc (p : point) : Z :=
        match p with
                | Head 0%nat => 0x11000
                | Head 1%nat => 0x11004
                | Head 2%nat => 0x11008
                | Head 3%nat => 0x1100c
                | Head 4%nat => 0x11010
                | Head 5%nat => 0x11014
                | Head _     => 0x11018
                | Loop _ 0%nat => 0x1101c
                | Loop _ 1%nat => 0x11020
                | Loop _ 2%nat => 0x11024
                | Loop _ 3%nat => 0x11028
                | Loop _ 4%nat => 0x1102c
                | Loop _ 5%nat => 0x11030
                | Loop _ 6%nat => 0x11034
                | Loop _ _     => 0x11038
                end.

(* What the instructions before the point have set, in a call with the
        argument `N`. *)
Definition pt_regs (N : Z) (p : point) (s : state) : Prop :=
        match p with
                | Head 0%nat => reg T.x10 N s
                | Head 1%nat => reg T.x10 N s
                        /\ reg T.x11 0 s
                | Head 2%nat => reg T.x10 N s
                        /\ reg T.x11 0 s
                        /\ reg T.x12 1 s
                | Head 3%nat => reg T.x11 0 s
                        /\ reg T.x12 1 s
                        /\ reg T.x13 N s
                | Head 4%nat => reg T.x11 0 s
                        /\ reg T.x12 1 s
                        /\ reg T.x13 N s
                        /\ N <> 0
                | Head 5%nat => reg T.x11 0 s
                        /\ N = 0
                | Head 6%nat => reg T.x10 0 s
                        /\ N = 0
                | Head _     => False
                | Loop i 0%nat => reg T.x11 (spec_tla.fib i) s
                        /\ reg T.x12 (spec_tla.fib (S i)) s
                        /\ reg T.x13 (N - Z.of_nat i) s
                        /\ Z.of_nat i < N
                | Loop i 1%nat => reg T.x11 (spec_tla.fib i) s
                        /\ reg T.x12 (spec_tla.fib (S i)) s
                        /\ reg T.x14 (spec_tla.fib (S (S i))) s
                        /\ reg T.x13 (N - Z.of_nat i) s
                        /\ Z.of_nat i < N
                | Loop i 2%nat => reg T.x11 (spec_tla.fib (S i)) s
                        /\ reg T.x14 (spec_tla.fib (S (S i))) s
                        /\ reg T.x13 (N - Z.of_nat i) s
                        /\ Z.of_nat i < N
                | Loop i 3%nat => reg T.x11 (spec_tla.fib (S i)) s
                        /\ reg T.x12 (spec_tla.fib (S (S i))) s
                        /\ reg T.x13 (N - Z.of_nat i) s
                        /\ Z.of_nat i < N
                | Loop i 4%nat => reg T.x11 (spec_tla.fib (S i)) s
                        /\ reg T.x12 (spec_tla.fib (S (S i))) s
                        /\ reg T.x13 (N - Z.of_nat (S i)) s
                        /\ Z.of_nat i < N
                | Loop i 5%nat => reg T.x11 (spec_tla.fib (S i)) s
                        /\ reg T.x12 (spec_tla.fib (S (S i))) s
                        /\ reg T.x13 (N - Z.of_nat (S i)) s
                        /\ Z.of_nat (S i) < N
                | Loop i 6%nat => reg T.x11 (spec_tla.fib (S i)) s
                        /\ Z.of_nat (S i) = N
                | Loop i 7%nat => reg T.x10 (spec_tla.fib (S i)) s
                        /\ Z.of_nat (S i) = N
                | Loop _ _     => False
                end.

Definition call_pt (N : Z) (p : point) (s : state) : Prop :=
        0 <= N < 2 ^ 64
        /\ reg T.PC (pt_pc p) s
        /\ pt_regs N p s.

(* The instructions that are left, at most. *)
Definition mu (N : Z) (p : point) : nat :=
        match p with
                | Head j   => (9 * Z.to_nat N + 20 - j)%nat
                | Loop i j => (9 * (Z.to_nat N - i) + (8 - j))%nat
                end.

Lemma pt_pc_range p :
        0x11000 <= pt_pc p < 0x1103c.
Proof.
        destruct p as [j | i j].
        - do 8 (destruct j as [| j]; [cbn [pt_pc]; lia |]). cbn [pt_pc]. lia.
        - do 9 (destruct j as [| j]; [cbn [pt_pc]; lia |]). cbn [pt_pc]. lia.
Qed.

Lemma call_pt_pc N p s :
        call_pt N p s ->
                _pc_addr s = pt_pc p.
Proof.
        intros (_ & Hpc & _). apply (reg_pc _ _ Hpc). pose proof (pt_pc_range p). lia.
Qed.

Lemma call_pt_in N p s :
        call_pt N p s ->
                in_fib s.
Proof.
        intros H. unfold in_fib. rewrite (call_pt_pc N p s H). exact (pt_pc_range p).
Qed.

(* At the label: the argument. *)
Lemma call_pt_label N p s :
        call_pt N p s ->
        _pc_addr s = 0x11000 ->
                reg T.x10 N s.
Proof.
        intros H Hpc. rewrite (call_pt_pc N p s H) in Hpc. destruct H as (_ & _ & Hr).
        destruct p as [j | i j].
        - destruct j as [| j]; [exact Hr |].
          do 7 (destruct j as [| j]; [cbn [pt_pc] in Hpc; lia |]). cbn [pt_pc] in Hpc. lia.
        - do 9 (destruct j as [| j]; [cbn [pt_pc] in Hpc; lia |]). cbn [pt_pc] in Hpc. lia.
Qed.

(* The registers that a step of a call may write: those of an instruction of
        tl_fib, and the clock. *)
Definition fib_all : list T.register :=
        T.R_bitvector_1 T.elp ::
        T.R_bitvector_64 T.mip ::
        T.R_bool T.minstret_increment ::
        T.R_bitvector_64 T.nextPC ::
        T.R_bitvector_64 T.PC ::
        T.R_bitvector_64 T.minstret ::
        T.R_bitvector_64 T.mcycle ::
        T.R_bitvector_64 T.mtime ::
        T.R_bitvector_64 T.x10 ::
        T.R_bitvector_64 T.x11 ::
        T.R_bitvector_64 T.x12 ::
        T.R_bitvector_64 T.x13 ::
        T.R_bitvector_64 T.x14 ::
        nil.

(* The return of a call with the argument `N`: to the return address, with
        the result in `a0`. *)
Definition fib_ret (N : Z) (s s' : state) : Prop :=
        only (step_regs_elp (T.R_bitvector_64 T.PC)) s s'
        /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
        /\ reg T.PC (abi_ra s) s'
        /\ reg T.x10 (spec_tla.fib (Z.to_nat N)) s
        /\ pc_internal e_static s = true.

(* A tick keeps the facts and the point. *)
Lemma call_tick N p s s' :
        only (T.R_bitvector_64 T.mcycle :: T.R_bitvector_64 T.mtime :: nil) s s' ->
        fib_facts s ->
        call_pt N p s ->
                fib_facts s'
                /\ call_pt N p s'.
Proof.
        intros Hl Hf (HN & Hpc & Hr).
        split; [exact (fib_facts_only _ _ _ Hl eq_refl eq_refl Hf) |].
        split; [exact HN |].
        split; [exact (reg_only _ _ _ _ _ Hl Hpc eq_refl) |].
        destruct p as [j | i j].
        - do 8 (destruct j as [| j];
                [ cbn [pt_regs] in *;
                  repeat match goal with
                          | H : _ /\ _ |- _ => destruct H
                          end;
                  regs_after Hl | ]).
          exact Hr.
        - do 9 (destruct j as [| j];
                [ cbn [pt_regs] in *;
                  repeat match goal with
                          | H : _ /\ _ |- _ => destruct H
                          end;
                  regs_after Hl | ]).
          exact Hr.
Qed.

(* ========================================================================== *)
(* The conditions of the spec, from the registers that a step writes          *)
(* ========================================================================== *)

(* A step of a call that is not its return. *)
Lemma frame_internal s s' :
        only fib_all s s' ->
        conf_default s ->
        conf_default s' ->
                stepcond_internal s s'.
Proof.
        intros Ho Hi Hi'. pose proof Ho as (Hm & Hr).
        split; [split |].
        - unfold abi_stepcond_preserve_regs, _state_regs_to_bv, st_regs_read, _regs_read.
          repeat split; symmetry;
                  match goal with
                          | |- T.register_lookup ?r _ = _ => exact (Hr r eq_refl)
                          end.
        - exact (conf_same s s' Hi Hi').
        - split.
          + unfold abi_opt_stepcond_preserve_mem. symmetry. exact Hm.
          + exact (abi_only fib_all T.x1 s s' Ho eq_refl).
Qed.

(* The return of a call. *)
Lemma frame_ret N s s' :
        fib_facts s ->
        fib_ret N s s' ->
                stepcond s s'
                /\ abi_res0 s' = definitions.bv_wrap 64 (spec_tla.fib (Z.to_nat N))
                /\ ~ in_fib s'
                /\ _pc_addr s' <> _pc_addr s.
Proof.
        intros (Hi & _ & _ & Ha) (Ho & He & Hpc & Hx & Hin).
        pose proof Ho as (Hm & Hr).
        assert (Hpc' : _pc_addr s' = abi_ra s).
        { apply (reg_pc _ _ Hpc). exact (abi_range T.x1 s). }
        apply ra_out_tl_fib_iff in Ha. apply pc_internal_iff in Hin.
        split; [| split; [| split]].
        - split; [split |].
          + unfold abi_stepcond_preserve_regs, _state_regs_to_bv, st_regs_read, _regs_read.
            repeat split; symmetry;
                    match goal with
                            | |- T.register_lookup ?r _ = _ => exact (Hr r eq_refl)
                            end.
          + exact (conf_same s s' Hi
                    (conf_default_only_elp (step_regs_elp (T.R_bitvector_64 T.PC)) s s' eq_refl Ho He Hi)).
          + split.
            * unfold abi_opt_stepcond_preserve_mem. symmetry. exact Hm.
            * exact Hpc'.
        - assert (Hx' : reg T.x10 (spec_tla.fib (Z.to_nat N)) s')
                by exact (reg_only _ _ _ _ _ Ho Hx eq_refl).
          unfold abi_res0, abi_a0, _state_regs_to_z, st_regs_read, _regs_read.
          unfold reg in Hx'. rewrite Hx'. apply definitions.Z_to_bv_unsigned.
        - unfold in_fib. rewrite Hpc'. exact Ha.
        - rewrite Hpc'. lia.
Qed.

(* ========================================================================== *)
(* One instruction of a call                                                  *)
(* ========================================================================== *)

Lemma fib_SS (i : nat) :
        spec_tla.fib (S (S i)) = spec_tla.fib i + spec_tla.fib (S i).
Proof.
        change (spec_tla.fib (S (S i))) with (spec_tla.fib (S i) + spec_tla.fib i).
        apply Z.add_comm.
Qed.

(* After a step that wrote `Hl`, with the facts `Hf` before it: the rest of
        what a step inside a call gives. *)
Ltac call_fin Hl Hf :=
        split; [cbn [mu]; lia |];
        split; [cbn [pt_pc]; lia |];
        split; [cbn [pt_pc]; lia |];
        split; [exact (fib_facts_only _ _ _ Hl eq_refl eq_refl Hf) |];
        refine (only_incl _ fib_all _ _ _ Hl); reflexivity.

(* A step of the instruction of a point of a call: the next point, with fewer
        instructions left, or the return. *)
Lemma call_step N p s :
        fib_facts s ->
        call_pt N p s ->
                forall n b, exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ ((exists p',
                        call_pt N p' s'
                        /\ (mu N p' < mu N p)%nat
                        /\ pt_pc p' <> pt_pc p
                        /\ pt_pc p' <> 0x11000
                        /\ fib_facts s'
                        /\ only fib_all s s')
                    \/ fib_ret N s s').
Proof.
        intros Hf (HN & Hpc & Hx) n b.
        pose proof Hf as (Hi & Hc & He & Ha).
        pose proof (fib_code_words s Hc) as
                (M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14).
        destruct p as [j | i j].
        - destruct j as [| [| [| [| [| [| [| j]]]]]]]; cbn [pt_pc pt_regs] in Hpc, Hx.
          + (* tl_fib + 0 *)
            rename Hx into X10.
            destruct (fib_ins_0 n b s Hi Hpc M0) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Head 1).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 4 *)
            destruct Hx as (X10 & X11).
            destruct (fib_ins_1 n b s Hi Hpc M1) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Head 2).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 8 *)
            destruct Hx as (X10 & X11 & X12).
            destruct (fib_ins_2 n b s N Hi Hpc X10 M2) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Head 3).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 12 *)
            destruct Hx as (X11 & X12 & X13).
            destruct (Z.eq_dec N 0) as [E | E].
            * subst N.
              destruct (fib_ins_3_0 n b s Hi Hpc X13 M3) as (s' & Ho & Hl & Hpc').
              exists s'. split; [exact Ho |]. left. exists (Head 5).
              split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
              call_fin Hl Hf.
            * assert (Hnz : N mod 2 ^ 64 <> 0) by (rewrite Z.mod_small by lia; exact E).
              destruct (fib_ins_3 n b s N Hi Hpc X13 Hnz M3) as (s' & Ho & Hl & Hpc').
              exists s'. split; [exact Ho |]. left. exists (Head 4).
              split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
              call_fin Hl Hf.
          + (* tl_fib + 16 *)
            destruct Hx as (X11 & X12 & X13 & E).
            destruct (fib_ins_4 n b s Hi Hpc M4) as (s' & Ho & Hl & Hpc').
            exists s'. split; [exact Ho |]. left. exists (Loop 0 0).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs];
                    replace (N - Z.of_nat 0) with N by lia; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 20 *)
            destruct Hx as (X11 & E).
            destruct (fib_ins_5 n b s 0 Hi Hpc X11 M5) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Head 6).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 24: the return of 0 *)
            destruct Hx as (X10 & E). subst N.
            destruct (fib_ins_6 n b s (abi_ra s) Hi Hpc (abi_reg T.x1 s) He M6)
                    as (s' & Ho & Hl & He' & Hpc').
            exists s'. split; [exact Ho |]. right.
            split; [exact Hl |]. split; [exact He' |]. split; [exact Hpc' |].
            split; [exact X10 |].
            apply pc_internal_iff. rewrite (reg_pc _ _ Hpc ltac:(lia)). lia.
          + destruct Hx.
        - destruct j as [| [| [| [| [| [| [| [| j]]]]]]]]; cbn [pt_pc pt_regs] in Hpc, Hx.
          + (* tl_fib + 28 *)
            destruct Hx as (X11 & X12 & X13 & Hlt).
            destruct (fib_ins_7 n b s _ _ Hi Hpc X11 X12 M7) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Loop i 1).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs];
                    rewrite fib_SS; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 32 *)
            destruct Hx as (X11 & X12 & X14 & X13 & Hlt).
            destruct (fib_ins_8 n b s _ Hi Hpc X12 M8) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Loop i 2).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 36 *)
            destruct Hx as (X11 & X14 & X13 & Hlt).
            destruct (fib_ins_9 n b s _ Hi Hpc X14 M9) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Loop i 3).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 40 *)
            destruct Hx as (X11 & X12 & X13 & Hlt).
            destruct (fib_ins_10 n b s _ Hi Hpc X13 M10) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Loop i 4).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs];
                    replace (N - Z.of_nat (S i)) with (N - Z.of_nat i - 1) by lia;
                    regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 44 *)
            destruct Hx as (X11 & X12 & X13 & Hlt).
            destruct (Z.eq_dec (N - Z.of_nat (S i)) 0) as [E | E].
            * rewrite E in X13.
              destruct (fib_ins_11_0 n b s Hi Hpc X13 M11) as (s' & Ho & Hl & Hpc').
              exists s'. split; [exact Ho |]. left. exists (Loop i 6).
              split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
              call_fin Hl Hf.
            * assert (Hnz : (N - Z.of_nat (S i)) mod 2 ^ 64 <> 0)
                      by (rewrite Z.mod_small by lia; exact E).
              destruct (fib_ins_11 n b s _ Hi Hpc X13 Hnz M11) as (s' & Ho & Hl & Hpc').
              exists s'. split; [exact Ho |]. left. exists (Loop i 5).
              split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
              call_fin Hl Hf.
          + (* tl_fib + 48 *)
            destruct Hx as (X11 & X12 & X13 & Hlt).
            destruct (fib_ins_12 n b s Hi Hpc M12) as (s' & Ho & Hl & Hpc').
            exists s'. split; [exact Ho |]. left. exists (Loop (S i) 0).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 52 *)
            destruct Hx as (X11 & E).
            destruct (fib_ins_13 n b s _ Hi Hpc X11 M13) as (s' & Ho & Hl & Hpc' & Hx').
            exists s'. split; [exact Ho |]. left. exists (Loop i 7).
            split; [split; [exact HN |]; split; [exact Hpc' |]; cbn [pt_regs]; regs_after Hl |].
            call_fin Hl Hf.
          + (* tl_fib + 56: the return of the result *)
            destruct Hx as (X10 & E).
            destruct (fib_ins_14 n b s (abi_ra s) Hi Hpc (abi_reg T.x1 s) He M14)
                    as (s' & Ho & Hl & He' & Hpc').
            exists s'. split; [exact Ho |]. right.
            split; [exact Hl |]. split; [exact He' |]. split; [exact Hpc' |].
            split; [replace (Z.to_nat N) with (S i) by lia; exact X10 |].
            apply pc_internal_iff. rewrite (reg_pc _ _ Hpc ltac:(lia)). lia.
          + destruct Hx.
Qed.

(* ========================================================================== *)
(* A step of a call                                                           *)
(* ========================================================================== *)

(* A step of an instruction, from a point of a call. *)
Lemma call_step_1 N p s s' :
        fib_facts s ->
        call_pt N p s ->
        exec_eval_step_1 s s' ->
                (exists p',
                        call_pt N p' s'
                        /\ (mu N p' < mu N p)%nat
                        /\ pt_pc p' <> pt_pc p
                        /\ pt_pc p' <> 0x11000
                        /\ fib_facts s'
                        /\ only fib_all s s')
                \/ fib_ret N s s'.
Proof.
        intros Hf Hp. exact (proj1 (step_tla s _ (call_step N p s Hf Hp)) s').
Qed.

(* The instruction of a point of a call can be stepped, to another state. *)
Lemma call_step_enabled N p s :
        fib_facts s ->
        call_pt N p s ->
                exists s',
                exec_eval_step_1 s s'
                /\ s <> s'.
Proof.
        intros Hf Hp.
        destruct (proj2 (step_tla s _ (call_step N p s Hf Hp)))
                as (s' & Ho & [(p' & Hp' & _ & Hne & _) | Hr]).
        - exists s'. split; [exact Ho |]. intros <-.
          apply Hne. rewrite <- (call_pt_pc N p' s Hp'). exact (call_pt_pc N p s Hp).
        - exists s'. split; [exact Ho |]. intros <-.
          destruct (frame_ret N s s Hf Hr) as (_ & _ & _ & Hne). apply Hne. reflexivity.
Qed.

(* The model is internal after a step: the PC is in tl_fib past the label, or
        at the label before and after. *)
Definition int_of (s s' : state) : bool :=
        pc_internal e_static s'
        || ((_pc_addr s =? 0x11000) && (_pc_addr s' =? 0x11000)).

Lemma int_of_true s s' :
        int_of s s' = true ->
                in_fib s'.
Proof.
        unfold int_of. rewrite orb_true_iff, andb_true_iff, !Z.eqb_eq, pc_internal_iff.
        unfold in_fib. lia.
Qed.

Lemma int_of_stay s s' :
        in_fib s ->
        _pc_addr s' = _pc_addr s ->
                int_of s s' = true.
Proof.
        intros Hin Hpc. unfold int_of.
        rewrite orb_true_iff, andb_true_iff, !Z.eqb_eq, pc_internal_iff.
        unfold in_fib in Hin. lia.
Qed.

Lemma int_of_internal s s' :
        pc_internal e_static s' = true ->
                int_of s s' = true.
Proof.
        intros H. unfold int_of. rewrite H. reflexivity.
Qed.

Lemma int_of_out s s' :
        ~ in_fib s' ->
                int_of s s' = false.
Proof.
        intros H. destruct (int_of s s') eqn:E; [| reflexivity].
        exfalso. exact (H (int_of_true s s' E)).
Qed.

(* A step of a behaviour from a point of a call: the call goes on, or it
        returns. *)
Lemma call_next N p s s' :
        fib_facts s ->
        call_pt N p s ->
        exec_next_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s s' \/ s = s' ->
                (int_of s s' = true
                        /\ fib_facts s'
                        /\ (exists p', call_pt N p' s')
                        /\ only fib_all s s')
                \/ (int_of s s' = false
                        /\ fib_ret N s s').
Proof.
        intros Hf Hp [Hn | <-].
        - destruct (Hn (proj2 (in_fib_at_pc s) (call_pt_in N p s Hp))) as [H1 | H2].
          + destruct (call_step_1 N p s s' Hf Hp H1) as [(p' & Hp' & _ & _ & Hl & Hf' & Ho) | Hr].
            * left. split; [| split; [exact Hf' | split; [exists p'; exact Hp' | exact Ho]]].
              apply int_of_internal. apply pc_internal_iff.
              rewrite (call_pt_pc N p' s' Hp'). pose proof (pt_pc_range p'). lia.
            * right. split; [| exact Hr].
              destruct (frame_ret N s s' Hf Hr) as (_ & _ & Hout & _).
              exact (int_of_out s s' Hout).
          + pose proof (tick_tla s s' H2) as Hl.
            destruct (call_tick N p s s' Hl Hf Hp) as (Hf' & Hp').
            left. split; [| split; [exact Hf' | split; [exists p; exact Hp' |]]].
            * apply int_of_stay; [exact (call_pt_in N p s Hp) |].
              rewrite (call_pt_pc N p s' Hp'), (call_pt_pc N p s Hp). reflexivity.
            * refine (only_incl _ fib_all _ _ _ Hl). reflexivity.
        - left. split; [| split; [exact Hf | split; [exists p; exact Hp | apply only_refl]]].
          apply int_of_stay; [exact (call_pt_in N p s Hp) | reflexivity].
Qed.

(* ========================================================================== *)
(* Weak fairness                                                              *)
(* ========================================================================== *)

Lemma wf_intro {St V : Type} (b : behavior St) (A : St -> St -> Prop) (v : St -> V) :
        (forall k,
                (forall j, exists s', A (b (k + j)%nat) s') ->
                        exists m,
                        A (b (k + m)%nat) (b (S (k + m)))
                        /\ v (b (k + m)%nat) <> v (b (S (k + m)))) ->
                (\wf (\lift2 A) \sub v) b.
Proof.
        intros H k Hen.
        destruct (H k) as (m & HA & Hne).
        - intros j. destruct (Hen j) as (beh' & H0 & (HA & _)).
          exists (beh' 1%nat). unfold Lift2 in HA. rewrite H0 in HA.
          unfold util_suffix in HA. rewrite Nat.add_0_r in HA. exact HA.
        - exists m. split.
          + unfold Lift2, util_suffix.
            rewrite Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r. exact HA.
          + unfold Not, Unchanged, Lift2, util_suffix.
            rewrite Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r. exact Hne.
Qed.

(* ========================================================================== *)
(* A behaviour of tl_fib and its environment                                  *)
(* ========================================================================== *)

Section run.

Variable sigma : behavior state.
Hypothesis HE : E e_static sigma.
Hypothesis Hexec : exec_static tl_fib_impl_s sigma.

Lemma run_pc0 :
        _pc_addr (sigma 0%nat) = 0x10000.
Proof.
        destruct Hexec as (_ & Hpc & _). exact Hpc.
Qed.

Lemma run_next i :
        exec_next_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) (sigma i) (sigma (S i))
        \/ sigma i = sigma (S i).
Proof.
        destruct Hexec as (_ & _ & _ & _ & Hnext & _).
        destruct Hnext as (_ & Hnext).
        exact (next_at sigma _ Hnext i).
Qed.

Lemma run_wf i :
        (forall j, exists s',
                exec_fair_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) (sigma (i + j)%nat) s'
                /\ sigma (i + j)%nat <> s') ->
                exists m,
                exec_fair_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string)
                        (sigma (i + m)%nat) (sigma (S (i + m))).
Proof.
        destruct Hexec as (_ & _ & _ & _ & _ & Hwf).
        destruct Hwf as (_ & Hwf).
        exact (wf_at sigma _ Hwf i).
Qed.

(* A state in tl_fib after a state outside: at the label, with the facts of
        a call. *)
Lemma run_enter k :
        ~ in_fib (sigma k) ->
        in_fib (sigma (S k)) ->
                _pc_addr (sigma (S k)) = 0x11000
                /\ fib_facts (sigma (S k)).
Proof.
        intros Hout Hin.
        pose proof (HE k) as H. unfold Lift2, util_suffix in H.
        rewrite Nat.add_0_r, Nat.add_1_r in H. destruct H as (Ha & Hb).
        unfold in_fib in Hout, Hin.
        assert (Hv : rm e_static (sigma k) <> None).
        { intros Hn. apply rm_none in Hn. apply pc_internal_iff in Hn. lia. }
        assert (Hl : _pc_addr (sigma (S k)) = 0x11000).
        { destruct (pc_internal e_static (sigma (S k))) eqn:Ei.
          - exfalso. apply Hout.
            rewrite (Ha Hv (proj2 (rm_none _) Ei)).
            change (e_static "tl_fib"%string) with 0x11000. lia.
          - apply pc_internal_false in Ei. lia. }
        split; [exact Hl |].
        assert (Hne : _pc_addr (sigma k) <> e_static "tl_fib"%string).
        { change (e_static "tl_fib"%string) with 0x11000. lia. }
        destruct (Hb Hv Hne Hl) as (_ & Hi & He & Hr & Hc).
        exact (conj Hi (conj Hc (conj He Hr))).
Qed.

Lemma int_of_enter k :
        ~ in_fib (sigma k) ->
                int_of (sigma k) (sigma (S k)) = false.
Proof.
        intros Hk.
        destruct (excluded_middle (in_fib (sigma (S k)))) as [Hin | Hout]; [| exact (int_of_out _ _ Hout)].
        destruct (run_enter k Hk Hin) as (Hl & _).
        unfold int_of. rewrite orb_false_iff, andb_false_iff, !Z.eqb_neq, pc_internal_false.
        unfold in_fib in Hk. lia.
Qed.

(* ========================================================================== *)
(* The model along the behaviour                                              *)
(* ========================================================================== *)

Definition op_of (s : state) : option string :=
        if _pc_addr s =? 0x11000 then Some "tl_fib"%string else None.

(* The state of the model at `n`: internal as `int_of`, at "tl_fib" at the
        label, the argument of the call that is under way, the result of the
        last call. *)
Fixpoint mdl (n : nat) : spec_tla.state :=
        match n with
                | O =>
                        spec_tla.Build_state false (op_of (sigma 0%nat))
                                (abi_arg0 (sigma 0%nat)) 0
                | S k =>
                        let i := int_of (sigma k) (sigma (S k)) in
                        spec_tla.Build_state i (op_of (sigma (S k)))
                                (if i then spec_tla.arg0 (mdl k) else abi_arg0 (sigma (S k)))
                                (spec_tla.fib (Z.to_nat (spec_tla.arg0 (mdl k))))
                end.

Lemma mdl_op k :
        spec_tla._op (mdl k) = op_of (sigma k).
Proof.
        destruct k; reflexivity.
Qed.

Lemma mdl_int k :
        spec_tla._internal (mdl (S k)) = int_of (sigma k) (sigma (S k)).
Proof.
        reflexivity.
Qed.

(* The model is at "tl_fib" or internal: the PC is in tl_fib. *)
Lemma mdl_active k :
        (spec_tla._op (mdl k) = Some "tl_fib"%string \/ spec_tla._internal (mdl k) = true)
                <-> in_fib (sigma k).
Proof.
        split.
        - intros [H | H].
          + rewrite mdl_op in H. unfold op_of in H.
            destruct (Z.eqb_spec (_pc_addr (sigma k)) 0x11000) as [E | E]; [| discriminate H].
            unfold in_fib. lia.
          + destruct k as [| k]; [discriminate H |]. exact (int_of_true _ _ H).
        - intros Hin.
          destruct (Z.eqb_spec (_pc_addr (sigma k)) 0x11000) as [E | E].
          + left. rewrite mdl_op. unfold op_of. rewrite (proj2 (Z.eqb_eq _ _) E). reflexivity.
          + right. destruct k as [| k].
            * exfalso. unfold in_fib in Hin. rewrite run_pc0 in Hin. lia.
            * rewrite mdl_int. apply int_of_internal. apply pc_internal_iff.
              unfold in_fib in Hin. lia.
Qed.

(* ========================================================================== *)
(* The invariant: a state in tl_fib is a point of a call                      *)
(* ========================================================================== *)

Lemma inv_all k :
        in_fib (sigma k) ->
                fib_facts (sigma k)
                /\ exists p, call_pt (spec_tla.arg0 (mdl k)) p (sigma k).
Proof.
        induction k as [| k IH]; intros Hin.
        - exfalso. unfold in_fib in Hin. rewrite run_pc0 in Hin. lia.
        - destruct (excluded_middle (in_fib (sigma k))) as [Hk | Hk].
          + destruct (IH Hk) as (Hf & p & Hp).
            destruct (call_next _ p _ _ Hf Hp (run_next k))
                    as [(Hi & Hf' & (p' & Hp') & _) | (Hi & Hr)].
            * split; [exact Hf' |]. exists p'.
              cbn [mdl spec_tla.arg0]. rewrite Hi. exact Hp'.
            * exfalso. destruct (frame_ret _ _ _ Hf Hr) as (_ & _ & Hout & _). exact (Hout Hin).
          + destruct (run_enter k Hk Hin) as (Hl & Hf).
            split; [exact Hf |]. exists (Head 0).
            cbn [mdl spec_tla.arg0]. rewrite (int_of_enter k Hk).
            split; [exact (abi_range T.x10 _) |].
            split; [exact (pc_reg _ _ Hl) |].
            exact (abi_reg T.x10 _).
Qed.

(* A step from a state in tl_fib: internal, or the return with the result. *)
Lemma run_step k :
        in_fib (sigma k) ->
                (spec_tla._internal (mdl (S k)) = true
                        /\ stepcond_internal (sigma k) (sigma (S k)))
                \/ (spec_tla._internal (mdl (S k)) = false
                        /\ spec_tla._internal (mdl k) = true
                        /\ stepcond (sigma k) (sigma (S k))
                        /\ res_eq (sigma (S k)) (mdl (S k))).
Proof.
        intros Hin. destruct (inv_all k Hin) as (Hf & p & Hp).
        destruct (call_next _ p _ _ Hf Hp (run_next k)) as [(Hi & Hf' & _ & Ho) | (Hi & Hr)].
        - left. split; [exact Hi |]. exact (frame_internal _ _ Ho (proj1 Hf) (proj1 Hf')).
        - right. destruct (frame_ret _ _ _ Hf Hr) as (Hs & Hres & _ & _).
          split; [exact Hi |]. split; [| split; [exact Hs | exact Hres]].
          destruct Hr as (_ & _ & _ & _ & Hpi).
          destruct k as [| k].
          + exfalso. apply pc_internal_iff in Hpi. rewrite run_pc0 in Hpi. lia.
          + rewrite mdl_int. exact (int_of_internal _ _ Hpi).
Qed.

(* ========================================================================== *)
(* A call returns                                                             *)
(* ========================================================================== *)

(* From a state of `P` in tl_fib, the step of its instruction is taken: the
        instruction of a state of `P` can be stepped, a tick keeps `P`, and
        tl_fib is fair. *)
Lemma fair_step (P : state -> Prop) :
        (forall s, P s -> in_fib s) ->
        (forall s, P s -> exists s', exec_eval_step_1 s s' /\ s <> s') ->
        (forall s s', P s -> exec_eval_step_2 s s' -> P s') ->
        forall i,
        P (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ P (sigma j)
                /\ exec_eval_step_1 (sigma j) (sigma (S j)).
Proof.
        intros Hat Hen Htick i Hi.
        destruct (excluded_middle (exists j,
                (i <= j)%nat /\ P (sigma j) /\ exec_eval_step_1 (sigma j) (sigma (S j))))
                as [H | Hno]; [exact H |].
        assert (Hall : forall d, P (sigma (i + d)%nat)).
        { induction d as [| d IH].
          - rewrite Nat.add_0_r. exact Hi.
          - rewrite Nat.add_succ_r.
            destruct (run_next (i + d)%nat) as [Hn | Heq].
            + destruct (Hn (proj2 (in_fib_at_pc _) (Hat _ IH))) as [Ho | Ht].
              * exfalso. apply Hno. exists (i + d)%nat.
                split; [lia |]. split; [exact IH | exact Ho].
              * exact (Htick _ _ IH Ht).
            + rewrite <- Heq. exact IH. }
        destruct (run_wf i) as (m & _ & Ho).
        - intros j. destruct (Hen _ (Hall j)) as (s' & Ho & Hne).
          exists s'. split; [| exact Hne].
          split; [exact (proj2 (in_fib_at_pc _) (Hat _ (Hall j))) | exact Ho].
        - exfalso. apply Hno. exists (i + m)%nat.
          split; [lia |]. split; [exact (Hall m) | exact Ho].
Qed.

(* A point of a call: the call returns, by induction on the instructions
        that are left. *)
Lemma call_returns m :
        forall k N p,
        mu N p = m ->
        fib_facts (sigma k) ->
        call_pt N p (sigma k) ->
                exists j,
                (k <= j)%nat
                /\ in_fib (sigma j)
                /\ int_of (sigma j) (sigma (S j)) = false.
Proof.
        induction m as [m IH] using lt_wf_ind. intros k N p Hm Hf Hp.
        assert (H1 : forall s, fib_facts s /\ call_pt N p s -> in_fib s).
        { intros s (_ & H). exact (call_pt_in N p s H). }
        assert (H2 : forall s, fib_facts s /\ call_pt N p s ->
                exists s', exec_eval_step_1 s s' /\ s <> s').
        { intros s (Ha & Hb). exact (call_step_enabled N p s Ha Hb). }
        assert (H3 : forall s s', fib_facts s /\ call_pt N p s -> exec_eval_step_2 s s' ->
                fib_facts s' /\ call_pt N p s').
        { intros s s' (Ha & Hb) Ht. exact (call_tick N p s s' (tick_tla s s' Ht) Ha Hb). }
        destruct (fair_step (fun s => fib_facts s /\ call_pt N p s) H1 H2 H3 k (conj Hf Hp))
                as (j & Hkj & (Hfj & Hpj) & Ho).
        destruct (call_step_1 N p _ _ Hfj Hpj Ho) as [(p' & Hp' & Hlt & _ & _ & Hf' & _) | Hr].
        - assert (Hlt' : (mu N p' < m)%nat) by lia.
          destruct (IH (mu N p') Hlt' (S j) N p' eq_refl Hf' Hp') as (j' & Hj' & H').
          exists j'. split; [lia | exact H'].
        - exists j. split; [exact Hkj |]. split; [exact (call_pt_in N p _ Hpj) |].
          destruct (frame_ret N _ _ Hfj Hr) as (_ & _ & Hout & _).
          exact (int_of_out _ _ Hout).
Qed.

(* From a state in tl_fib, the return of the call: the model is internal
        before it, and not after it. *)
Lemma run_returns k :
        in_fib (sigma k) ->
                exists j,
                (k <= j)%nat
                /\ in_fib (sigma j)
                /\ spec_tla._internal (mdl j) = true
                /\ spec_tla._internal (mdl (S j)) = false
                /\ stepcond (sigma j) (sigma (S j))
                /\ res_eq (sigma (S j)) (mdl (S j)).
Proof.
        intros Hin. destruct (inv_all k Hin) as (Hf & p & Hp).
        destruct (call_returns _ k _ p eq_refl Hf Hp) as (j & Hkj & Hj & Hi).
        exists j. split; [exact Hkj |]. split; [exact Hj |].
        destruct (run_step j Hj) as [(H & _) | (H1 & H2 & H3 & H4)].
        - rewrite mdl_int, Hi in H. discriminate H.
        - exact (conj H2 (conj H1 (conj H3 H4))).
Qed.

(* ========================================================================== *)
(* The model                                                                  *)
(* ========================================================================== *)

(* A step of the model: one of its three steps. *)
Lemma mdl_next k :
        (~ (spec_tla._op (mdl k) = Some "tl_fib"%string \/ spec_tla._internal (mdl k) = true)
                /\ spec_tla._internal (mdl (S k)) = false)
        \/ ((spec_tla._op (mdl k) = Some "tl_fib"%string \/ spec_tla._internal (mdl k) = true)
                /\ spec_tla._internal (mdl (S k)) = false
                /\ spec_tla.res0 (mdl (S k)) = spec_tla.fib (Z.to_nat (spec_tla.arg0 (mdl k))))
        \/ ((spec_tla._op (mdl k) = Some "tl_fib"%string \/ spec_tla._internal (mdl k) = true)
                /\ spec_tla._internal (mdl (S k)) = true
                /\ spec_tla.arg0 (mdl (S k)) = spec_tla.arg0 (mdl k)).
Proof.
        destruct (excluded_middle (in_fib (sigma k))) as [Hk | Hk].
        - pose proof (proj2 (mdl_active k) Hk) as Ha.
          destruct (int_of (sigma k) (sigma (S k))) eqn:Ei.
          + right. right. split; [exact Ha |]. split; [exact Ei |].
            cbn [mdl spec_tla.arg0]. rewrite Ei. reflexivity.
          + right. left. split; [exact Ha |]. split; [exact Ei | reflexivity].
        - left. split.
          + intros Ha. exact (Hk (proj1 (mdl_active k) Ha)).
          + exact (int_of_enter k Hk).
Qed.

Lemma mdl_spec :
        spec_tla.spec mdl.
Proof.
        split; [| split].
        - reflexivity.
        - intros k. left.
          unfold spec_tla.next, spec_tla.next_0, spec_tla.next_1, spec_tla.next_2.
          unfold Or, Lift2, util_suffix.
          rewrite Nat.add_0_r, Nat.add_1_r. exact (mdl_next k).
        - unfold spec_tla.F, spec_tla.next_1. apply wf_intro. intros k Hen.
          destruct (Hen 0%nat) as (s' & Ha & _). rewrite Nat.add_0_r in Ha.
          destruct (run_returns k (proj1 (mdl_active k) Ha))
                  as (j & Hkj & Hin & Hi & Hi' & _).
          exists (j - k)%nat. replace (k + (j - k))%nat with j by lia.
          split.
          + split; [exact (proj2 (mdl_active j) Hin) |]. split; [exact Hi' | reflexivity].
          + unfold spec_tla.vars. intros Heq. rewrite Heq in Hi.
            rewrite Hi in Hi'. discriminate Hi'.
Qed.

(* ========================================================================== *)
(* The spec                                                                   *)
(* ========================================================================== *)

(* The label and the argument. *)
Lemma run_label k :
        at_label_eq e_static (sigma k) (mdl k)
        /\ (at_label_asm e_static (sigma k) ->
                precond (sigma k) ->
                        arg_eq (sigma k) (mdl k)).
Proof.
        unfold at_label_eq, at_label_asm, at_label_tla, arg_eq.
        change (e_static "tl_fib"%string) with 0x11000.
        rewrite mdl_op. unfold op_of.
        destruct (Z.eqb_spec (_pc_addr (sigma k)) 0x11000) as [E | E].
        - split; [split; intros _; [reflexivity | exact E] |].
          intros _ _.
          assert (Hin : in_fib (sigma k)) by (unfold in_fib; lia).
          destruct (inv_all k Hin) as (_ & p & Hp).
          pose proof Hp as (HN & _).
          exact (reg_abi _ _ _ (call_pt_label _ p _ Hp E) HN).
        - split; [split; intros H; [exact (False_ind _ (E H)) | discriminate H] |].
          intros H. exact (False_ind _ (E H)).
Qed.

Lemma run_spec :
        tl_fib_spec e_static sigma.
Proof.
        exists (fun n => (sigma n, mdl n)). split.
        - exists (fun n => n), (fun n => n).
          split; [intros n; lia |]. split; [intros n; lia |].
          split; [intros y; exists y; reflexivity |].
          split; [intros y; exists y; reflexivity |].
          intros n. reflexivity.
        - split; [| split; [| split]].
          + (* the model *)
            exists mdl. split; [| exact mdl_spec].
            exists (fun n => n), (fun n => n).
            split; [intros n; lia |]. split; [intros n; lia |].
            split; [intros y; exists y; reflexivity |].
            split; [intros y; exists y; reflexivity |].
            intros n. reflexivity.
          + (* the label and the argument *)
            intros k. unfold Lift1, util_suffix. rewrite Nat.add_0_r.
            exact (run_label k).
          + (* a step *)
            intros k. left. unfold Lift2, util_suffix.
            rewrite Nat.add_0_r, Nat.add_1_r.
            cbv beta zeta. unfold _glu_asm_lower, _glu_tla_lower. cbn [fst snd].
            intros Ha _.
            destruct (run_step k (proj1 (mdl_active k) Ha)) as [(H1 & H2) | (H1 & _ & H2 & H3)].
            * right. exact (conj H1 H2).
            * left. exact (conj H1 (conj H2 H3)).
          + (* fairness *)
            apply wf_intro. intros k Hen.
            destruct (Hen 0%nat) as (s0 & H0). rewrite Nat.add_0_r in H0.
            cbv beta zeta in H0. destruct H0 as (Ha & _).
            destruct (run_returns k (proj1 (mdl_active k) Ha))
                    as (j & Hkj & Hin & Hi & Hi' & Hs & Hres).
            destruct (Hen (j - k)%nat) as (s1 & H1).
            replace (k + (j - k))%nat with j in H1 by lia.
            cbv beta zeta in H1. destruct H1 as (_ & Hpre & _).
            exists (j - k)%nat. replace (k + (j - k))%nat with j by lia.
            split.
            * cbv beta zeta. unfold _glu_asm_lower, _glu_tla_lower. cbn [fst snd].
              split; [exact (proj2 (mdl_active j) Hin) |].
              split; [exact Hpre |]. split; [exact Hi' |]. split; [exact Hs | exact Hres].
            * cbv beta. intros Heq. apply (f_equal snd) in Heq. cbn [snd] in Heq.
              rewrite Heq in Hi. rewrite Hi in Hi'. discriminate Hi'.
Qed.

End run.

(* ========================================================================== *)
(* thm_1                                                                      *)
(* ========================================================================== *)

Theorem thm_1 :
        valid ((\rmap (rm e_static)
                        (E e_static \land exec_static tl_fib_impl_s))
                \impl (\rmap (rm e_static)
                        (tl_fib_spec e_static))).
Proof.
        intros beh (sigma & Heq & HE & Hexec).
        exists sigma. split; [exact Heq |].
        exact (run_spec sigma HE Hexec).
Qed.

(* The statement of thm_1.v. *)
Definition thm_1_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_1.thm_1 in exact t) :=
        thm_1.

Print Assumptions thm_1.
