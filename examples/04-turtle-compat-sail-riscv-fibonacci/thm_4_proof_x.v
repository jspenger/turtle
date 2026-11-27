(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require SailStdpp.MachineWord.
Require SailStdpp.Operators_mwords.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
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
Require Import turtle.compat.sail.riscv.examples.fib.main.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1_proof_x.
Require turtle.compat.sail.riscv.examples.fib.thm_3_proof_x.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Module T := rv64d_types.
Module B := stdpp.bitvector.definitions.
Module O := SailStdpp.Operators_mwords.
Module W := SailStdpp.MachineWord.MachineWord.
Module U := turtle.gen.bits.

(* ========================================================================== *)
(* A branch on two registers                                                  *)
(* ========================================================================== *)

(* `beq rs1, rs2, _` with `rs2` 8 and `rs1` not 8: not taken. *)
Lemma eq_reg_8 (c : Z) :
        c mod 2 ^ 64 <> 8 ->
                O.eq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 c))
                        (rv64d.regval_from_reg (B.Z_to_bv 64 8)) = false.
Proof.
        intros H. unfold rv64d.regval_from_reg.
        rewrite U.eq_vec_unsigned. apply Z.eqb_neq. exact H.
Qed.

(* `ev_extra` of thm_1_proof_x.v, with the branch on 8. *)
Ltac ev_extra ::=
        first
                [ match goal with
                        | H : ?c mod 2 ^ 64 <> 8
                          |- context [O.eq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 ?c))
                                        (rv64d.regval_from_reg (B.Z_to_bv 64 8))] =>
                                ev_replace (eq_reg_8 c H)
                        end
                | match goal with
                        | H : ?c mod 2 ^ 64 <> 0
                          |- context [O.eq_vec (rv64d.regval_from_reg (B.Z_to_bv 64 ?c))
                                        (rv64d.regval_from_reg rv64d.zero_reg)] =>
                                ev_replace (eq_zero_reg c H)
                        end
                | progress (try unfold rv64d.is_aligned_paddr; try unfold rv64d.is_aligned_vaddr);
                  cbv beta iota ].

(* ========================================================================== *)
(* The instructions of main up to the call of getrandom.                      *)
(* ========================================================================== *)

Section step.

(* main + 0: addi sp, sp, -16 *)
Lemma fib_main_0 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10000 ->
        T.register_lookup (T.R_bitvector_64 T.x2) (st_regs s) = definitions.Z_to_bv 64 0x4000000000 ->
        mem_word 0x10000 4278255891 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x2)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10004
                /\ T.register_lookup (T.R_bitvector_64 T.x2) (st_regs s') = definitions.Z_to_bv 64 0x3ffffffff0.
Proof.
        step_tac.
Qed.

(* main + 4: addi a0, sp, 0 *)
Lemma fib_main_1 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10004 ->
        T.register_lookup (T.R_bitvector_64 T.x2) (st_regs s) = definitions.Z_to_bv 64 0x3ffffffff0 ->
        mem_word 0x10004 66835 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10008
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x3ffffffff0.
Proof.
        step_tac.
Qed.

(* main + 8: addi a1, zero, 8 *)
Lemma fib_main_2 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10008 ->
        mem_word 0x10008 8390035 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1000c
                /\ T.register_lookup (T.R_bitvector_64 T.x11) (st_regs s') = definitions.Z_to_bv 64 8.
Proof.
        step_tac.
Qed.

(* main + 12: addi a2, zero, 0 *)
Lemma fib_main_3 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1000c ->
        mem_word 0x1000c 1555 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x12)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10010
                /\ T.register_lookup (T.R_bitvector_64 T.x12) (st_regs s') = definitions.Z_to_bv 64 0.
Proof.
        step_tac.
Qed.

(* main + 16: lui ra, %hi(getrandom) *)
Lemma fib_main_4 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10010 ->
        mem_word 0x10010 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10014
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 20: jalr ra, ra, %lo(getrandom) *)
Lemma fib_main_5 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10014 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x10014 536903911 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14200
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10018.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The check of the result of getrandom.                                      *)
(* ========================================================================== *)

Section step.

(* main + 24: addi t0, zero, 8 *)
Lemma fib_main_6 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10018 ->
        mem_word 0x10018 8389267 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x5)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1001c
                /\ T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s') = definitions.Z_to_bv 64 8.
Proof.
        step_tac.
Qed.

(* main + 28: beq a0, t0, 12, a0 = 8 *)
Lemma fib_main_7_8 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1001c ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 8 ->
        T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s) = definitions.Z_to_bv 64 8 ->
        mem_word 0x1001c 5572195 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10028.
Proof.
        step_tac.
Qed.

(* main + 28: beq a0, t0, 12, a0 not 8 *)
Lemma fib_main_7 n b s c :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1001c ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 c ->
        T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s) = definitions.Z_to_bv 64 8 ->
        c mod 2 ^ 64 <> 8 ->
        mem_word 0x1001c 5572195 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10020.
Proof.
        step_tac_sym.
Qed.

(* main + 32: lui t0, %hi(.tl_err) *)
Lemma fib_main_8 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10020 ->
        mem_word 0x10020 66231 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x5)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10024
                /\ T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s') = definitions.Z_to_bv 64 0x10000.
Proof.
        step_tac.
Qed.

(* main + 36: jalr zero, t0, %lo(.tl_err) *)
Lemma fib_main_9 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10024 ->
        T.register_lookup (T.R_bitvector_64 T.x5) (st_regs s) = definitions.Z_to_bv 64 0x10000 ->
        mem_word 0x10024 121798759 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.PC)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10074.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The read of the random word, and the call of tl_fib.                       *)
(* ========================================================================== *)

Section step.

(* main + 40: lw a0, 0(sp) *)
Lemma fib_main_10 n b s w :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10028 ->
        T.register_lookup (T.R_bitvector_64 T.x2) (st_regs s) = definitions.Z_to_bv 64 0x3ffffffff0 ->
        _mem_read (st_mem s) (definitions.Z_to_bv 64 0x3ffffffff0) 4 = definitions.Z_to_bv 32 w ->
        mem_word 0x10028 75011 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1002c.
Proof.
        step_tac_sym.
Qed.

(* main + 44: andi a0, a0, 31 *)
Lemma fib_main_11 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1002c ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x1002c 32863507 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10030.
Proof.
        step_tac_sym.
Qed.

(* main + 48: addi s1, a0, 0 *)
Lemma fib_main_12 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10030 ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x10030 328851 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x9)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10034.
Proof.
        step_tac_sym.
Qed.

(* main + 52: lui ra, %hi(tl_fib) *)
Lemma fib_main_13 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10034 ->
        mem_word 0x10034 69815 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10038
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x11000.
Proof.
        step_tac.
Qed.

(* main + 56: jalr ra, ra, %lo(tl_fib) *)
Lemma fib_main_14 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10038 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x11000 ->
        mem_word 0x10038 32999 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x11000
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x1003c.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The first call of printf.                                                  *)
(* ========================================================================== *)

Section step.

(* main + 60: addi s2, a0, 0 *)
Lemma fib_main_15 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1003c ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x1003c 330003 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x18)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10040.
Proof.
        step_tac_sym.
Qed.

(* main + 64: addi a1, s1, 0 *)
Lemma fib_main_16 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10040 ->
        T.register_lookup (T.R_bitvector_64 T.x9) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x10040 296339 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10044.
Proof.
        step_tac_sym.
Qed.

(* main + 68: lui a0, %hi(.tl_fmt) *)
Lemma fib_main_17 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10044 ->
        mem_word 0x10044 1049911 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10048
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 72: addi a0, a0, %lo(.tl_fmt) *)
Lemma fib_main_18 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10048 ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 0x100000 ->
        mem_word 0x10048 328979 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1004c
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 76: lui ra, %hi(printf) *)
Lemma fib_main_19 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1004c ->
        mem_word 0x1004c 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10050
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 80: jalr ra, ra, %lo(printf) *)
Lemma fib_main_20 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10050 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x10050 32999 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14000
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10054.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The second call of printf.                                                 *)
(* ========================================================================== *)

Section step.

(* main + 84: addi a1, s2, 0 *)
Lemma fib_main_21 n b s v :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10054 ->
        T.register_lookup (T.R_bitvector_64 T.x18) (st_regs s) = definitions.Z_to_bv 64 v ->
        mem_word 0x10054 591251 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x11)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10058.
Proof.
        step_tac_sym.
Qed.

(* main + 88: lui a0, %hi(.tl_fmt) *)
Lemma fib_main_22 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10058 ->
        mem_word 0x10058 1049911 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1005c
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 92: addi a0, a0, %lo(.tl_fmt) *)
Lemma fib_main_23 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1005c ->
        T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s) = definitions.Z_to_bv 64 0x100000 ->
        mem_word 0x1005c 328979 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10060
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0x100000.
Proof.
        step_tac.
Qed.

(* main + 96: lui ra, %hi(printf) *)
Lemma fib_main_24 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10060 ->
        mem_word 0x10060 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10064
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 100: jalr ra, ra, %lo(printf) *)
Lemma fib_main_25 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10064 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x10064 32999 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14000
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10068.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* The calls of exit.                                                         *)
(* ========================================================================== *)

Section step.

(* main + 104: addi a0, zero, 0 *)
Lemma fib_main_26 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10068 ->
        mem_word 0x10068 1299 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1006c
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 0.
Proof.
        step_tac.
Qed.

(* main + 108: lui ra, %hi(exit) *)
Lemma fib_main_27 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1006c ->
        mem_word 0x1006c 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10070
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 112: jalr ra, ra, %lo(exit) *)
Lemma fib_main_28 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10070 ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x10070 268468455 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14100
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10074.
Proof.
        step_tac.
Qed.

(* main + 116: addi a0, zero, 1 *)
Lemma fib_main_29 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10074 ->
        mem_word 0x10074 1049875 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x10)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x10078
                /\ T.register_lookup (T.R_bitvector_64 T.x10) (st_regs s') = definitions.Z_to_bv 64 1.
Proof.
        step_tac.
Qed.

(* main + 120: lui ra, %hi(exit) *)
Lemma fib_main_30 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x10078 ->
        mem_word 0x10078 82103 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x1007c
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x14000.
Proof.
        step_tac.
Qed.

(* main + 124: jalr ra, ra, %lo(exit) *)
Lemma fib_main_31 n b s :
        conf_default s ->
        T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s) = definitions.Z_to_bv 64 0x1007c ->
        T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s) = definitions.Z_to_bv 64 0x14000 ->
        mem_word 0x1007c 268468455 s ->
                exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ only (step_regs_elp (T.R_bitvector_64 T.x1)) s s'
                /\ T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0
                /\ T.register_lookup (T.R_bitvector_64 T.PC) (st_regs s') = definitions.Z_to_bv 64 0x14100
                /\ T.register_lookup (T.R_bitvector_64 T.x1) (st_regs s') = definitions.Z_to_bv 64 0x10080.
Proof.
        step_tac.
Qed.

End step.

(* ========================================================================== *)
(* Registers and memory across a call                                         *)
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

(* A state whose PC is not past the label of tl_fib. *)
Lemma reg_pc_shown a s :
        reg T.PC a s ->
        0 <= a <= 0x11000 \/ 0x1103c <= a < 2 ^ 64 ->
                pc_internal e_static s = false.
Proof.
        intros Hpc Ha. apply pc_internal_false. rewrite (reg_pc _ _ Hpc ltac:(lia)). lia.
Qed.

(* The PC after a step to another address. *)
Lemma reg_pc_ne a a' s s' :
        reg T.PC a s ->
        reg T.PC a' s' ->
        0 <= a < 2 ^ 64 ->
        0 <= a' < 2 ^ 64 ->
        a' <> a ->
                _pc_addr s' <> _pc_addr s.
Proof.
        intros Hpc Hpc' Ha Ha' Hne. rewrite (reg_pc _ _ Hpc Ha), (reg_pc _ _ Hpc' Ha'). exact Hne.
Qed.

(* The four bytes at `a`, as a word. *)
Lemma mem_word_any a s :
        _mem_read (st_mem s) (definitions.Z_to_bv 64 a) 4
                = definitions.Z_to_bv 32
                        (definitions.bv_unsigned (_mem_read (st_mem s) (definitions.Z_to_bv 64 a) 4)).
Proof.
        symmetry. apply definitions.Z_to_bv_bv_unsigned.
Qed.

(* A section of instructions stays in memory where the memory stays. *)
Lemma init_s_text_kept lo hi stmnts addr s s' :
        mem_kept lo hi s s' ->
        0 <= addr ->
        addr + 4 * Z.of_nat (List.length stmnts) <= 2 ^ 64 ->
        addr + 4 * Z.of_nat (List.length stmnts) <= lo \/ hi <= addr ->
        _init_s_text stmnts addr s ->
                _init_s_text stmnts addr s'.
Proof.
        intros Hk. revert addr. induction stmnts as [| [ins] stmnts IH]; intros addr H0 H1 Hr H.
        - exact I.
        - cbn [List.length] in H1, Hr. destruct H as (Ht & Hw). split.
          + apply IH; [lia | lia | lia | exact Ht].
          + pose proof (mem_word_kept lo hi addr _ s s' Hk H0 ltac:(lia) ltac:(lia)
                    (instr_mem_word ins addr s Hw)) as Hm.
            unfold mem_word in Hm. unfold st_mem_read. rewrite Hm.
            apply definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma exec_init_src_1_kept lo hi sec addr s s' :
        mem_kept lo hi s s' ->
        0 <= addr ->
        addr + _section_size sec <= 2 ^ 64 ->
        addr + _section_size sec <= lo \/ hi <= addr ->
        exec_init_src_1 sec addr s ->
                exec_init_src_1 sec addr s'.
Proof.
        intros Hk H0 H1 Hr. destruct sec as [l | l].
        - cbn [exec_init_src_1 _section_size] in *.
          apply (init_s_text_kept lo hi l addr s s' Hk H0); lia.
        - exact (exec_init_src_1_data_kept lo hi l addr s s' Hk H0 H1 Hr).
Qed.

(* getrandom, asked for 8 bytes at the stack pointer of main: the memory
        outside them is kept. *)
Lemma getrandom_kept s s' :
        abi_arg0 s = 0x3ffffffff0 ->
        abi_arg1 s = 8 ->
        _getrandom_stepcond s s' ->
                mem_kept 0x3ffffffff0 0x3ffffffff8 s s'.
Proof.
        intros Ha Hb H. unfold _getrandom_stepcond in H. cbv zeta in H.
        rewrite Ha, Hb in H. destruct H as (n & Hn & _ & Hm).
        intros a Hr. apply Hm. lia.
Qed.

(* The format at `a0`: what printf expects. *)
Lemma fmt_printf s :
        exec_init_src_1 _tl_fmt_sec (e_static ".tl_fmt"%string) s ->
        abi_arg0 s = 0x100000 ->
                _printf_precond s.
Proof.
        intros Hf Ha. unfold _printf_precond. rewrite Ha. cbv zeta.
        change (e_static ".tl_fmt"%string) with 0x100000 in Hf.
        destruct Hf as (((((_ & H4) & H3) & H2) & H1) & H0).
        split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 | exact H4].
Qed.

(* ========================================================================== *)
(* The stages of main                                                         *)
(* ========================================================================== *)

(* The words of `main_sec e_static`. *)
Definition main_words (s : state) : Prop :=
        mem_word 0x10000 4278255891 s
        /\ mem_word 0x10004 66835 s
        /\ mem_word 0x10008 8390035 s
        /\ mem_word 0x1000c 1555 s
        /\ mem_word 0x10010 82103 s
        /\ mem_word 0x10014 536903911 s
        /\ mem_word 0x10018 8389267 s
        /\ mem_word 0x1001c 5572195 s
        /\ mem_word 0x10020 66231 s
        /\ mem_word 0x10024 121798759 s
        /\ mem_word 0x10028 75011 s
        /\ mem_word 0x1002c 32863507 s
        /\ mem_word 0x10030 328851 s
        /\ mem_word 0x10034 69815 s
        /\ mem_word 0x10038 32999 s
        /\ mem_word 0x1003c 330003 s
        /\ mem_word 0x10040 296339 s
        /\ mem_word 0x10044 1049911 s
        /\ mem_word 0x10048 328979 s
        /\ mem_word 0x1004c 82103 s
        /\ mem_word 0x10050 32999 s
        /\ mem_word 0x10054 591251 s
        /\ mem_word 0x10058 1049911 s
        /\ mem_word 0x1005c 328979 s
        /\ mem_word 0x10060 82103 s
        /\ mem_word 0x10064 32999 s
        /\ mem_word 0x10068 1299 s
        /\ mem_word 0x1006c 82103 s
        /\ mem_word 0x10070 268468455 s
        /\ mem_word 0x10074 1049875 s
        /\ mem_word 0x10078 82103 s
        /\ mem_word 0x1007c 268468455 s.

(* The address of stage `k`: 0 to 31 the instructions of main, 32 getrandom,
        33 and 34 the calls of printf, 35 exit. *)
Definition m_pc (k : nat) : Z :=
        match k with
                | 0%nat   => 0x10000
                | 1%nat   => 0x10004
                | 2%nat   => 0x10008
                | 3%nat   => 0x1000c
                | 4%nat   => 0x10010
                | 5%nat   => 0x10014
                | 6%nat   => 0x10018
                | 7%nat   => 0x1001c
                | 8%nat   => 0x10020
                | 9%nat   => 0x10024
                | 10%nat  => 0x10028
                | 11%nat  => 0x1002c
                | 12%nat  => 0x10030
                | 13%nat  => 0x10034
                | 14%nat  => 0x10038
                | 15%nat  => 0x1003c
                | 16%nat  => 0x10040
                | 17%nat  => 0x10044
                | 18%nat  => 0x10048
                | 19%nat  => 0x1004c
                | 20%nat  => 0x10050
                | 21%nat  => 0x10054
                | 22%nat  => 0x10058
                | 23%nat  => 0x1005c
                | 24%nat  => 0x10060
                | 25%nat  => 0x10064
                | 26%nat  => 0x10068
                | 27%nat  => 0x1006c
                | 28%nat  => 0x10070
                | 29%nat  => 0x10074
                | 30%nat  => 0x10078
                | 31%nat  => 0x1007c
                | 32%nat  => 0x14200
                | 33%nat  => 0x14000
                | 34%nat  => 0x14000
                | _       => 0x14100
                end.

(* What the instructions before stage `k` have set, as far as the next
        steps need it. *)
Definition m_regs (k : nat) (s : state) : Prop :=
        match k with
                | 0%nat   => reg T.x2 0x4000000000 s
                | 1%nat   => reg T.x2 0x3ffffffff0 s
                | 2%nat   => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x3ffffffff0 s
                | 3%nat   => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x3ffffffff0 s
                        /\ reg T.x11 0x8 s
                | 4%nat   => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x3ffffffff0 s
                        /\ reg T.x11 0x8 s
                        /\ reg T.x12 0x0 s
                | 5%nat   => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x3ffffffff0 s
                        /\ reg T.x11 0x8 s
                        /\ reg T.x12 0x0 s
                        /\ reg T.x1 0x14000 s
                | 6%nat   => reg T.x2 0x3ffffffff0 s
                | 7%nat   => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x5 0x8 s
                | 8%nat   => reg T.x2 0x3ffffffff0 s
                | 9%nat   => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x5 0x10000 s
                | 10%nat  => reg T.x2 0x3ffffffff0 s
                | 11%nat  => reg T.x2 0x3ffffffff0 s
                | 12%nat  => reg T.x2 0x3ffffffff0 s
                | 13%nat  => reg T.x2 0x3ffffffff0 s
                | 14%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x1 0x11000 s
                | 15%nat  => reg T.x2 0x3ffffffff0 s
                | 16%nat  => reg T.x2 0x3ffffffff0 s
                | 17%nat  => reg T.x2 0x3ffffffff0 s
                | 18%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                | 19%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                | 20%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 21%nat  => reg T.x2 0x3ffffffff0 s
                | 22%nat  => reg T.x2 0x3ffffffff0 s
                | 23%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                | 24%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                | 25%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x14000 s
                | 26%nat  => reg T.x2 0x3ffffffff0 s
                | 27%nat  => reg T.x2 0x3ffffffff0 s
                | 28%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x1 0x14000 s
                | 29%nat  => reg T.x2 0x3ffffffff0 s
                | 30%nat  => reg T.x2 0x3ffffffff0 s
                | 31%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x1 0x14000 s
                | 32%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x3ffffffff0 s
                        /\ reg T.x11 0x8 s
                        /\ reg T.x12 0x0 s
                        /\ reg T.x1 0x10018 s
                | 33%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10054 s
                | 34%nat  => reg T.x2 0x3ffffffff0 s
                        /\ reg T.x10 0x100000 s
                        /\ reg T.x1 0x10068 s
                | 35%nat  => reg T.x2 0x3ffffffff0 s
                | _       => False
                end.

(* The steps that are left at stage `k`, at most: the instructions and the
        calls of the libc, the call of tl_fib as one step. *)
Definition m_left (k : nat) : nat :=
        match k with
                | 0%nat   => 31
                | 1%nat   => 30
                | 2%nat   => 29
                | 3%nat   => 28
                | 4%nat   => 27
                | 5%nat   => 26
                | 6%nat   => 24
                | 7%nat   => 23
                | 8%nat   => 5
                | 9%nat   => 4
                | 10%nat  => 22
                | 11%nat  => 21
                | 12%nat  => 20
                | 13%nat  => 19
                | 14%nat  => 18
                | 15%nat  => 16
                | 16%nat  => 15
                | 17%nat  => 14
                | 18%nat  => 13
                | 19%nat  => 12
                | 20%nat  => 11
                | 21%nat  => 9
                | 22%nat  => 8
                | 23%nat  => 7
                | 24%nat  => 6
                | 25%nat  => 5
                | 26%nat  => 3
                | 27%nat  => 2
                | 28%nat  => 1
                | 29%nat  => 3
                | 30%nat  => 2
                | 31%nat  => 1
                | 32%nat  => 25
                | 33%nat  => 10
                | 34%nat  => 4
                | _       => 0
                end.

Lemma main_code_words s :
        exec_init_src_1 (main_sec e_static) (e_static "main"%string) s ->
                main_words s.
Proof.
        intros H.
        let l := eval vm_compute in (main_sec e_static) in
        change (main_sec e_static) with l in H.
        change (e_static "main"%string) with 0x10000 in H.
        cbn [exec_init_src_1 _init_s_text] in H.
        destruct H as ((((((((((((((((((((((((((((((((_ & I31) & I30) & I29) & I28) & I27) & I26) & I25) & I24) & I23) & I22) & I21) & I20) & I19) & I18) & I17) & I16) & I15) & I14) & I13) & I12) & I11) & I10) & I9) & I8) & I7) & I6) & I5) & I4) & I3) & I2) & I1) & I0).
        instr_word I0. instr_word I1. instr_word I2. instr_word I3. instr_word I4.
        instr_word I5. instr_word I6. instr_word I7. instr_word I8. instr_word I9.
        instr_word I10. instr_word I11. instr_word I12. instr_word I13. instr_word I14.
        instr_word I15. instr_word I16. instr_word I17. instr_word I18. instr_word I19.
        instr_word I20. instr_word I21. instr_word I22. instr_word I23. instr_word I24.
        instr_word I25. instr_word I26. instr_word I27. instr_word I28. instr_word I29.
        instr_word I30. instr_word I31.
        unfold main_words. tauto.
Qed.

Lemma m_pc_range k :
        (k < 36)%nat ->
                0x10000 <= m_pc k < 0x10080
                \/ m_pc k = 0x14000
                \/ m_pc k = 0x14100
                \/ m_pc k = 0x14200.
Proof.
        intros Hk. do 36 (destruct k as [| k]; [cbn [m_pc]; lia |]). lia.
Qed.

(* ========================================================================== *)
(* The code at `e_static`                                                     *)
(* ========================================================================== *)

(* What the stages keep besides the configuration, main and the format: the
        code of tl_fib in the linked code. Kept where the memory is, and
        where getrandom writes the 8 bytes at the stack pointer of main. *)
Module Type CODE.

Parameter code : state -> Prop.

Parameter code_mem : forall s s',
        st_mem s' = st_mem s ->
        code s ->
                code s'.

Parameter code_kept : forall s s',
        mem_kept 0x3ffffffff0 0x3ffffffff8 s s' ->
        code s ->
                code s'.

End CODE.

Module Stages (Import C : CODE).

(* The configuration, main, the format, and `code`. *)
Definition prog (s : state) : Prop :=
        conf_default s
        /\ exec_init_src_1 (main_sec e_static) (e_static "main"%string) s
        /\ exec_init_src_1 _tl_fmt_sec (e_static ".tl_fmt"%string) s
        /\ code s.

Lemma prog_only l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs = true ->
        prog s ->
                prog s'.
Proof.
        intros Ho Hl (Hi & Hm & Hf & Hc).
        split; [exact (conf_default_only l s s' Hl Ho Hi) |].
        split; [exact (exec_init_src_1_only l _ _ s s' Ho Hm) |].
        split; [exact (exec_init_src_1_only l _ _ s s' Ho Hf) |].
        exact (code_mem s s' (proj1 Ho) Hc).
Qed.

Lemma prog_only_elp l s s' :
        only l s s' ->
        forallb (fun r => negb (reg_in l r)) preserve_conf_regs_elp = true ->
        T.register_lookup (T.R_bitvector_1 T.elp) (st_regs s') = Values.mword_of_int 0 ->
        prog s ->
                prog s'.
Proof.
        intros Ho Hl He (Hi & Hm & Hf & Hc).
        split; [exact (conf_default_only_elp l s s' Hl Ho He Hi) |].
        split; [exact (exec_init_src_1_only l _ _ s s' Ho Hm) |].
        split; [exact (exec_init_src_1_only l _ _ s s' Ho Hf) |].
        exact (code_mem s s' (proj1 Ho) Hc).
Qed.

(* A call that keeps the memory: printf. *)
Lemma prog_mem s s' :
        st_mem s' = st_mem s ->
        conf_default s' ->
        prog s ->
                prog s'.
Proof.
        intros Hm Hi (_ & Ha & Hb & Hc).
        split; [exact Hi |].
        split; [exact (exec_init_src_1_mem _ _ s s' Hm Ha) |].
        split; [exact (exec_init_src_1_mem _ _ s s' Hm Hb) |].
        exact (code_mem s s' Hm Hc).
Qed.

(* A call that keeps the memory outside the 8 bytes at the stack pointer of
        main: getrandom. *)
Lemma prog_kept s s' :
        mem_kept 0x3ffffffff0 0x3ffffffff8 s s' ->
        conf_default s' ->
        prog s ->
                prog s'.
Proof.
        intros Hk Hi (_ & Ha & Hb & Hc).
        split; [exact Hi |].
        split; [| split].
        - apply (exec_init_src_1_kept 0x3ffffffff0 0x3ffffffff8 _ _ s s' Hk); [ | | | exact Ha];
                  change (_section_size (main_sec e_static)) with 128;
                  change (e_static "main"%string) with 0x10000; lia.
        - apply (exec_init_src_1_kept 0x3ffffffff0 0x3ffffffff8 _ _ s s' Hk); [ | | | exact Hb];
                  change (_section_size _tl_fmt_sec) with 5;
                  change (e_static ".tl_fmt"%string) with 0x100000; lia.
        - exact (code_kept s s' Hk Hc).
Qed.

Definition m_stage (k : nat) (s : state) : Prop :=
        prog s
        /\ reg T.PC (m_pc k) s
        /\ m_regs k s.

Lemma m_stage_pc k s :
        (k < 36)%nat ->
        m_stage k s ->
                _pc_addr s = m_pc k.
Proof.
        intros Hk (_ & Hpc & _). apply (reg_pc _ _ Hpc). pose proof (m_pc_range k Hk). lia.
Qed.

(* A stage is not past the label of tl_fib. *)
Lemma m_stage_shown k s :
        (k < 36)%nat ->
        m_stage k s ->
                pc_internal e_static s = false.
Proof.
        intros Hk Hst. apply pc_internal_false. rewrite (m_stage_pc k s Hk Hst).
        pose proof (m_pc_range k Hk). lia.
Qed.

(* An instruction of main is in main. *)
Lemma m_stage_at k s :
        (k < 32)%nat ->
        m_stage k s ->
                at_pc (main_sec e_static) (e_static "main"%string) s.
Proof.
        intros Hk Hst. unfold at_pc. rewrite (m_stage_pc k s ltac:(lia) Hst).
        change (_section_size (main_sec e_static)) with 128.
        change (e_static "main"%string) with 0x10000.
        do 32 (destruct k as [| k]; [cbn [m_pc]; lia |]). lia.
Qed.

(* A tick keeps the stage. *)
Lemma m_tick k s s' :
        m_stage k s ->
        only (T.R_bitvector_64 T.mcycle :: T.R_bitvector_64 T.mtime :: nil) s s' ->
                m_stage k s'.
Proof.
        intros (Hp & Hpc & Hx) Hl.
        split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
        split; [exact (reg_only _ _ _ _ _ Hl Hpc eq_refl) |].
        do 36 (destruct k as [| k];
                [ cbn [m_regs] in *;
                  repeat match goal with
                          | H : _ /\ _ |- _ => destruct H
                          end;
                  regs_after Hl | ]).
        exact Hx.
Qed.

(* At the label of tl_fib, from main. *)
Definition m_call (s : state) : Prop :=
        prog s
        /\ reg T.PC 0x11000 s
        /\ reg T.x2 0x3ffffffff0 s
        /\ reg T.x1 0x1003c s.

(* After the step of stage `k`: a stage with fewer steps left, or the call of
        tl_fib. *)
Definition m_after (k : nat) (s : state) : Prop :=
        (exists k', (k' < 36)%nat /\ (m_left k' < m_left k)%nat /\ m_stage k' s)
        \/ (k = 14%nat /\ m_call s).

(* ========================================================================== *)
(* One instruction of main                                                    *)
(* ========================================================================== *)

(* A step of the instruction of a stage of main: to another address, a stage
        with fewer steps left, or the first point of the call of tl_fib. *)
Lemma main_step k s :
        (k < 32)%nat ->
        m_stage k s ->
                forall n b, exists s',
                outcome (rv64d.try_step n b) s (res_val false s')
                /\ _pc_addr s' <> _pc_addr s
                /\ m_after k s'.
Proof.
        intros Hk (Hp & Hpc & Hx) n b.
        pose proof Hp as (Hi & Hm & _ & _).
        pose proof (main_code_words s Hm) as
                (M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 &
                        M13 & M14 & M15 & M16 & M17 & M18 & M19 & M20 & M21 & M22 &
                        M23 & M24 & M25 & M26 & M27 & M28 & M29 & M30 & M31).
        destruct k as [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| k]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia ].
        all: cbn [m_pc m_regs] in Hpc, Hx.
        - (* 0: main + 0 *)
          rename Hx into X2.
          destruct (fib_main_0 n b s Hi Hpc X2 M0) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 1%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 1: main + 4 *)
          rename Hx into X2.
          destruct (fib_main_1 n b s Hi Hpc X2 M1) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 2%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 2: main + 8 *)
          destruct Hx as (X2 & X10).
          destruct (fib_main_2 n b s Hi Hpc M2) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 3%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 3: main + 12 *)
          destruct Hx as (X2 & X10 & X11).
          destruct (fib_main_3 n b s Hi Hpc M3) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 4%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 4: main + 16 *)
          destruct Hx as (X2 & X10 & X11 & X12).
          destruct (fib_main_4 n b s Hi Hpc M4) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 5%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 5: main + 20 *)
          destruct Hx as (X2 & X10 & X11 & X12 & X1).
          destruct (fib_main_5 n b s Hi Hpc X1 M5) as (s' & Ho & Hl & He' & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 32%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only_elp _ _ _ Hl eq_refl He' Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 6: main + 24 *)
          rename Hx into X2.
          destruct (fib_main_6 n b s Hi Hpc M6) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 7%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 7: main + 28 *)
          destruct Hx as (X2 & X5).
          destruct (Z.eq_dec (_state_regs_to_z s T.x10) 8) as [E | E].
          * assert (X10 : reg T.x10 8 s) by (rewrite <- E; exact (abi_reg T.x10 s)).
            destruct (fib_main_7_8 n b s Hi Hpc X10 X5 M7) as (s' & Ho & Hl & Hpc').
            exists s'. split; [exact Ho |].
            split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
            left. exists 10%nat. split; [lia |]. split; [cbn [m_left]; lia |].
            split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
            split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
          * assert (Hnz : _state_regs_to_z s T.x10 mod 2 ^ 64 <> 8).
            { rewrite Z.mod_small by exact (abi_range T.x10 s). exact E. }
            destruct (fib_main_7 n b s _ Hi Hpc (abi_reg T.x10 s) X5 Hnz M7) as (s' & Ho & Hl & Hpc').
            exists s'. split; [exact Ho |].
            split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
            left. exists 8%nat. split; [lia |]. split; [cbn [m_left]; lia |].
            split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
            split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 8: main + 32 *)
          rename Hx into X2.
          destruct (fib_main_8 n b s Hi Hpc M8) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 9%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 9: main + 36 *)
          destruct Hx as (X2 & X5).
          destruct (fib_main_9 n b s Hi Hpc X5 M9) as (s' & Ho & Hl & He' & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 29%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only_elp _ _ _ Hl eq_refl He' Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 10: main + 40 *)
          rename Hx into X2.
          destruct (fib_main_10 n b s _ Hi Hpc X2 (mem_word_any 0x3ffffffff0 s) M10) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 11%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 11: main + 44 *)
          rename Hx into X2.
          destruct (fib_main_11 n b s _ Hi Hpc (abi_reg T.x10 s) M11) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 12%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 12: main + 48 *)
          rename Hx into X2.
          destruct (fib_main_12 n b s _ Hi Hpc (abi_reg T.x10 s) M12) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 13%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 13: main + 52 *)
          rename Hx into X2.
          destruct (fib_main_13 n b s Hi Hpc M13) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 14%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 14: main + 56 *)
          destruct Hx as (X2 & X1).
          destruct (fib_main_14 n b s Hi Hpc X1 M14) as (s' & Ho & Hl & He' & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          assert (Hp' : prog s') by (exact (prog_only_elp _ _ _ Hl eq_refl He' Hp)).
          assert (X2' : reg T.x2 0x3ffffffff0 s') by (eapply reg_only; [exact Hl | exact X2 | reflexivity]).
          right. split; [reflexivity |]. exact (conj Hp' (conj Hpc' (conj X2' Hx'))).
        - (* 15: main + 60 *)
          rename Hx into X2.
          destruct (fib_main_15 n b s _ Hi Hpc (abi_reg T.x10 s) M15) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 16%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 16: main + 64 *)
          rename Hx into X2.
          destruct (fib_main_16 n b s _ Hi Hpc (abi_reg T.x9 s) M16) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 17%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 17: main + 68 *)
          rename Hx into X2.
          destruct (fib_main_17 n b s Hi Hpc M17) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 18%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 18: main + 72 *)
          destruct Hx as (X2 & X10).
          destruct (fib_main_18 n b s Hi Hpc X10 M18) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 19%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 19: main + 76 *)
          destruct Hx as (X2 & X10).
          destruct (fib_main_19 n b s Hi Hpc M19) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 20%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 20: main + 80 *)
          destruct Hx as (X2 & X10 & X1).
          destruct (fib_main_20 n b s Hi Hpc X1 M20) as (s' & Ho & Hl & He' & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 33%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only_elp _ _ _ Hl eq_refl He' Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 21: main + 84 *)
          rename Hx into X2.
          destruct (fib_main_21 n b s _ Hi Hpc (abi_reg T.x18 s) M21) as (s' & Ho & Hl & Hpc').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 22%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 22: main + 88 *)
          rename Hx into X2.
          destruct (fib_main_22 n b s Hi Hpc M22) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 23%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 23: main + 92 *)
          destruct Hx as (X2 & X10).
          destruct (fib_main_23 n b s Hi Hpc X10 M23) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 24%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 24: main + 96 *)
          destruct Hx as (X2 & X10).
          destruct (fib_main_24 n b s Hi Hpc M24) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 25%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 25: main + 100 *)
          destruct Hx as (X2 & X10 & X1).
          destruct (fib_main_25 n b s Hi Hpc X1 M25) as (s' & Ho & Hl & He' & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 34%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only_elp _ _ _ Hl eq_refl He' Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 26: main + 104 *)
          rename Hx into X2.
          destruct (fib_main_26 n b s Hi Hpc M26) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 27%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 27: main + 108 *)
          rename Hx into X2.
          destruct (fib_main_27 n b s Hi Hpc M27) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 28%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 28: main + 112 *)
          destruct Hx as (X2 & X1).
          destruct (fib_main_28 n b s Hi Hpc X1 M28) as (s' & Ho & Hl & He' & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 35%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only_elp _ _ _ Hl eq_refl He' Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 29: main + 116 *)
          rename Hx into X2.
          destruct (fib_main_29 n b s Hi Hpc M29) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 30%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 30: main + 120 *)
          rename Hx into X2.
          destruct (fib_main_30 n b s Hi Hpc M30) as (s' & Ho & Hl & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 31%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only _ _ _ Hl eq_refl Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
        - (* 31: main + 124 *)
          destruct Hx as (X2 & X1).
          destruct (fib_main_31 n b s Hi Hpc X1 M31) as (s' & Ho & Hl & He' & Hpc' & Hx').
          exists s'. split; [exact Ho |].
          split; [exact (reg_pc_ne _ _ _ _ Hpc Hpc' ltac:(lia) ltac:(lia) ltac:(lia)) |].
          left. exists 35%nat. split; [lia |]. split; [cbn [m_left]; lia |].
          split; [exact (prog_only_elp _ _ _ Hl eq_refl He' Hp) |].
          split; [exact Hpc' |]. cbn [m_regs]. regs_after Hl.
Qed.

(* ========================================================================== *)
(* The calls of the libc                                                      *)
(* ========================================================================== *)

(* At getrandom: what it expects. *)
Lemma m_getrandom_at s :
        m_stage 32 s ->
                _pc_addr s = e_static "getrandom"%string
                /\ _getrandom_precond s
                /\ abi_precond s.
Proof.
        intros (_ & Hpc & Hx). cbn [m_pc m_regs] in Hpc, Hx.
        destruct Hx as (X2 & X10 & X11 & X12 & X1).
        split; [exact (reg_pc _ _ Hpc ltac:(lia)) |]. split.
        - unfold _getrandom_precond. cbv zeta. unfold abi_arg1, abi_a1, abi_arg2, abi_a2.
          rewrite (reg_abi _ _ _ X11 ltac:(lia)), (reg_abi _ _ _ X12 ltac:(lia)). lia.
        - unfold abi_precond, abi_sp. rewrite (reg_abi _ _ _ X2 ltac:(lia)). reflexivity.
Qed.

(* The return of getrandom: the instruction after the call. *)
Lemma m_getrandom_ret s s' :
        m_stage 32 s ->
        _getrandom_stepcond s s' ->
        abi_stepcond s s' ->
        abi_opt_stepcond_return s s' ->
                m_stage 6 s'.
Proof.
        intros (Hprog & Hpc & Hx) Hgs (Hreg & Hconf) Hret. cbn [m_pc m_regs] in Hpc, Hx.
        destruct Hx as (X2 & X10 & X11 & X12 & X1).
        pose proof Hprog as (Hi & _).
        unfold abi_opt_stepcond_return in Hret.
        assert (Hkept : mem_kept 0x3ffffffff0 0x3ffffffff8 s s').
        { apply getrandom_kept; [| | exact Hgs].
          - exact (reg_abi _ _ _ X10 ltac:(lia)).
          - exact (reg_abi _ _ _ X11 ltac:(lia)). }
        split; [exact (prog_kept s s' Hkept (conf_keep s s' Hconf Hi) Hprog) |].
        split; [| exact (reg_preserved T.x2 _ s s' Hreg eq_refl X2)].
        apply pc_reg. rewrite Hret. exact (reg_abi _ _ _ X1 ltac:(lia)).
Qed.

(* At printf, in the call of stage `k`: what it expects. *)
Lemma m_printf_at k s :
        k = 33%nat \/ k = 34%nat ->
        m_stage k s ->
                _pc_addr s = e_static "printf"%string
                /\ _printf_precond s
                /\ abi_precond s.
Proof.
        intros Hk (Hprog & Hpc & Hx).
        pose proof Hprog as (_ & _ & Hfmt & _).
        destruct Hk as [-> | ->]; cbn [m_pc m_regs] in Hpc, Hx; destruct Hx as (X2 & X10 & X1).
        all: split; [exact (reg_pc _ _ Hpc ltac:(lia)) |]; split;
                [ apply fmt_printf; [exact Hfmt | exact (reg_abi _ _ _ X10 ltac:(lia))]
                | unfold abi_precond, abi_sp; rewrite (reg_abi _ _ _ X2 ltac:(lia)); reflexivity ].
Qed.

(* The return of printf, from the call of stage `k`: the instruction after
        the call, stage `k'`. *)
Lemma m_printf_ret k k' s s' :
        (k = 33%nat /\ k' = 21%nat) \/ (k = 34%nat /\ k' = 26%nat) ->
        m_stage k s ->
        abi_stepcond s s' ->
        abi_opt_stepcond_preserve_mem s s' ->
        abi_opt_stepcond_return s s' ->
                m_stage k' s'.
Proof.
        intros Hk (Hprog & Hpc & Hx) (Hreg & Hconf) Hmem Hret.
        pose proof Hprog as (Hi & _).
        unfold abi_opt_stepcond_return in Hret.
        destruct Hk as [(-> & ->) | (-> & ->)]; cbn [m_pc m_regs] in Hpc, Hx;
                destruct Hx as (X2 & X10 & X1).
        all: split; [exact (prog_mem s s' (eq_sym Hmem) (conf_keep s s' Hconf Hi) Hprog) |];
                split; [| exact (reg_preserved T.x2 _ s s' Hreg eq_refl X2)];
                apply pc_reg; rewrite Hret; exact (reg_abi _ _ _ X1 ltac:(lia)).
Qed.

(* At exit: what it expects. *)
Lemma m_exit_at s :
        m_stage 35 s ->
                _pc_addr s = e_static "exit"%string
                /\ abi_precond s.
Proof.
        intros (_ & Hpc & X2). cbn [m_pc m_regs] in Hpc, X2.
        split; [exact (reg_pc _ _ Hpc ltac:(lia)) |].
        unfold abi_precond, abi_sp. rewrite (reg_abi _ _ _ X2 ltac:(lia)). reflexivity.
Qed.

End Stages.

(* ========================================================================== *)
(* The states of the linked code                                              *)
(* ========================================================================== *)

(* The code of tl_fib: what the stages of the linked code keep. *)
Module FibCode <: CODE.

Definition code (s : state) : Prop :=
        exec_init_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s.

Lemma code_mem s s' :
        st_mem s' = st_mem s ->
        code s ->
                code s'.
Proof.
        exact (exec_init_src_1_mem _ _ s s').
Qed.

Lemma code_kept s s' :
        mem_kept 0x3ffffffff0 0x3ffffffff8 s s' ->
        code s ->
                code s'.
Proof.
        intros Hk Hc. unfold code in *.
        apply (exec_init_src_1_kept 0x3ffffffff0 0x3ffffffff8 _ _ s s' Hk); [ | | | exact Hc];
                change (_section_size (tl_fib_impl_sec e_static)) with 60;
                change (e_static "tl_fib"%string) with 0x11000; lia.
Qed.

End FibCode.

Module Stages_fib := Stages FibCode.
Export Stages_fib.

(* A point of the call of tl_fib from main, with what main needs after it. *)
Definition in_call (N : Z) (p : point) (s : state) : Prop :=
        call_pt N p s
        /\ fib_facts s
        /\ exec_init_src_1 (main_sec e_static) (e_static "main"%string) s
        /\ exec_init_src_1 _tl_fmt_sec (e_static ".tl_fmt"%string) s
        /\ reg T.x2 0x3ffffffff0 s
        /\ reg T.x1 0x1003c s.

(* A state of the linked code: a stage of main, or a point of the call of
        tl_fib. *)
Definition G (s : state) : Prop :=
        (exists k, (k < 36)%nat /\ m_stage k s)
        \/ (exists N p, in_call N p s).

(* The call of tl_fib from main. *)
Lemma enter_fib s :
        m_call s ->
                in_call (abi_arg0 s) (Head 0) s.
Proof.
        intros ((Hi & Hm & Hf & Hc) & Hpc & X2 & X1).
        assert (Hra : abi_ra s = 0x1003c) by exact (reg_abi _ _ _ X1 ltac:(lia)).
        split; [| split; [| split; [exact Hm | split; [exact Hf | split; [exact X2 | exact X1]]]]].
        - split; [exact (abi_range T.x10 s) |]. split; [exact Hpc | exact (abi_reg T.x10 s)].
        - split; [exact Hi |]. split; [exact Hc |].
          split; [rewrite Hra; reflexivity |]. apply ra_out_tl_fib_iff. rewrite Hra. lia.
Qed.

Lemma m_after_G k s :
        m_after k s ->
                G s
                /\ pc_internal e_static s = false.
Proof.
        intros [(k' & Hk' & _ & Hst) | (_ & Hc)].
        - split; [left; exists k'; exact (conj Hk' Hst) | exact (m_stage_shown k' s Hk' Hst)].
        - split; [right; exists (abi_arg0 s), (Head 0); exact (enter_fib s Hc) |].
          destruct Hc as (_ & Hpc & _).
          exact (reg_pc_shown _ _ Hpc ltac:(lia)).
Qed.

(* ========================================================================== *)
(* The call of tl_fib                                                         *)
(* ========================================================================== *)

(* A step of an instruction, from a point of the call: a point with fewer
        instructions left, or the stage of main after the call. *)
Lemma in_call_step N p s s' :
        in_call N p s ->
        exec_eval_step_1 s s' ->
                (exists p', (mu N p' < mu N p)%nat /\ in_call N p' s')
                \/ m_stage 15 s'.
Proof.
        intros (Hp & Hf & Hm & Hfm & X2 & X1) H1.
        destruct (call_step_1 N p s s' Hf Hp H1) as [(p' & Hp' & Hlt & _ & _ & Hf' & Ho) | Hr].
        - left. exists p'. split; [exact Hlt |].
          split; [exact Hp' |]. split; [exact Hf' |].
          split; [exact (exec_init_src_1_only _ _ _ s s' Ho Hm) |].
          split; [exact (exec_init_src_1_only _ _ _ s s' Ho Hfm) |].
          split; [exact (reg_only _ _ _ _ _ Ho X2 eq_refl) |].
          exact (reg_only _ _ _ _ _ Ho X1 eq_refl).
        - right. pose proof Hr as (Ho & He' & Hpc' & _ & _).
          assert (Hra : abi_ra s = 0x1003c) by exact (reg_abi _ _ _ X1 ltac:(lia)).
          rewrite Hra in Hpc'.
          split; [| split; [exact Hpc' | exact (reg_only _ _ _ _ _ Ho X2 eq_refl)]].
          destruct Hf as (Hi0 & Hc & _ & _).
          split; [exact (conf_default_only_elp
                  (step_regs_elp (T.R_bitvector_64 T.PC)) s s' eq_refl Ho He' Hi0) |].
          split; [exact (exec_init_src_1_only _ _ _ s s' Ho Hm) |].
          split; [exact (exec_init_src_1_only _ _ _ s s' Ho Hfm) |].
          exact (exec_init_src_1_only _ _ _ s s' Ho Hc).
Qed.

(* A tick keeps the point. *)
Lemma in_call_tick N p s s' :
        in_call N p s ->
        exec_eval_step_2 s s' ->
                in_call N p s'.
Proof.
        intros (Hp & Hf & Hm & Hfm & X2 & X1) H2.
        pose proof (tick_tla s s' H2) as Hl.
        destruct (call_tick N p s s' Hl Hf Hp) as (Hf' & Hp').
        split; [exact Hp' |]. split; [exact Hf' |].
        split; [exact (exec_init_src_1_only _ _ _ s s' Hl Hm) |].
        split; [exact (exec_init_src_1_only _ _ _ s s' Hl Hfm) |].
        split; [exact (reg_only _ _ _ _ _ Hl X2 eq_refl) |].
        exact (reg_only _ _ _ _ _ Hl X1 eq_refl).
Qed.

(* ========================================================================== *)
(* A step of the linked code                                                  *)
(* ========================================================================== *)

(* What `E` says of a step. *)
Definition Ebody (s s' : state) : Prop :=
        (rm e_static s <> None ->
                rm e_static s' = None ->
                        _pc_addr s = e_static "tl_fib"%string)
        /\ (rm e_static s <> None ->
                _pc_addr s <> e_static "tl_fib"%string ->
                        _pc_addr s' = e_static "tl_fib"%string ->
                                abi_precond s'
                                /\ conf_default s'
                                /\ abi_ra s' mod 2 = 0
                                /\ ra_out_tl_fib e_static s'
                                /\ exec_init_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s').

(* A step to a state that is not past the label. *)
Lemma Ebody_shown s s' :
        G s' ->
        pc_internal e_static s' = false ->
                Ebody s s'.
Proof.
        intros Hg Hv. split.
        - intros _ Hn. apply rm_none in Hn. rewrite Hv in Hn. discriminate Hn.
        - intros _ _ Hl. change (e_static "tl_fib"%string) with 0x11000 in Hl.
          destruct Hg as [(k & Hk & Hst) | (N & p & Hp & Hf & _ & _ & X2 & _)].
          + exfalso. pose proof (m_stage_pc k s' Hk Hst) as Hpc.
            pose proof (m_pc_range k Hk). lia.
          + destruct Hf as (Hi & Hc & He & Ha).
            split; [| exact (conj Hi (conj He (conj Ha Hc)))].
            unfold abi_precond, abi_sp. rewrite (reg_abi _ _ _ X2 ltac:(lia)). reflexivity.
Qed.

(* A step from a point of the call. *)
Lemma Ebody_call N p s s' :
        call_pt N p s ->
                Ebody s s'.
Proof.
        intros Hp. pose proof (call_pt_in N p s Hp) as Hin. unfold in_fib in Hin.
        assert (Hl : rm e_static s <> None -> _pc_addr s = 0x11000).
        { intros Hv. destruct (pc_internal e_static s) eqn:E.
          - exfalso. apply Hv. apply rm_none. exact E.
          - apply pc_internal_false in E. lia. }
        split.
        - intros Hv _. exact (Hl Hv).
        - intros Hv Hne. exfalso. exact (Hne (Hl Hv)).
Qed.

(* The steps of the libc. *)
Definition printf_next (s s' : state) : Prop :=
        _pc_addr s = e_static "printf"%string ->
                _printf_precond s ->
                        abi_precond s ->
                                abi_stepcond s s'
                                /\ abi_opt_stepcond_preserve_mem s s'
                                /\ abi_opt_stepcond_return s s'.

Definition exit_next (s s' : state) : Prop :=
        _pc_addr s = e_static "exit"%string ->
                abi_precond s ->
                        s' = s.

Definition getrandom_next (s s' : state) : Prop :=
        _pc_addr s = e_static "getrandom"%string ->
                _getrandom_precond s ->
                        abi_precond s ->
                                _getrandom_stepcond s s'
                                /\ abi_stepcond s s'
                                /\ abi_opt_stepcond_return s s'.

(* A step of the linked code keeps its states, and is a step of `E`. *)
Lemma G_step s s' :
        G s ->
        exec_next_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s s' \/ s = s' ->
        exec_next_src_1 (main_sec e_static) (e_static "main"%string) s s' \/ s = s' ->
        printf_next s s' \/ s = s' ->
        exit_next s s' \/ s = s' ->
        getrandom_next s s' \/ s = s' ->
                G s'
                /\ Ebody s s'.
Proof.
        intros [(k & Hk & Hst) | (N & p & Hc)] Hnf Hnm Hpr Hex Hgr.
        - (* a stage of main *)
          assert (Hto : forall k', (k' < 36)%nat -> m_stage k' s' -> G s' /\ Ebody s s').
          { intros k' Hk' Hst'.
            assert (Hg : G s') by (left; exists k'; exact (conj Hk' Hst')).
            exact (conj Hg (Ebody_shown s s' Hg (m_stage_shown k' s' Hk' Hst'))). }
          assert (Hsame : s = s' -> G s' /\ Ebody s s').
          { intros Heq. apply (Hto k Hk). rewrite <- Heq. exact Hst. }
          destruct (Nat.lt_ge_cases k 32) as [Hk32 | Hk32].
          + (* an instruction *)
            destruct Hnm as [Hn | Heq]; [| exact (Hsame Heq)].
            destruct (Hn (m_stage_at k s Hk32 Hst)) as [H1 | H2].
            * destruct (proj1 (step_tla s _ (main_step k s Hk32 Hst)) s' H1) as (_ & Ha).
              destruct (m_after_G k s' Ha) as (Hg & Hv').
              exact (conj Hg (Ebody_shown s s' Hg Hv')).
            * exact (Hto k Hk (m_tick k s s' Hst (tick_tla s s' H2))).
          + (* a call of the libc *)
            assert (Hl : k = 32%nat \/ k = 33%nat \/ k = 34%nat \/ k = 35%nat) by lia.
            destruct Hl as [-> | [-> | [-> | ->]]].
            * (* getrandom *)
              destruct Hgr as [Hn | Heq]; [| exact (Hsame Heq)].
              destruct (m_getrandom_at s Hst) as (Hpc & Hpre & Habi).
              destruct (Hn Hpc Hpre Habi) as (Hgs & Hs & Hret).
              exact (Hto 6%nat ltac:(lia) (m_getrandom_ret s s' Hst Hgs Hs Hret)).
            * (* printf, first call *)
              destruct Hpr as [Hn | Heq]; [| exact (Hsame Heq)].
              destruct (m_printf_at 33 s (or_introl eq_refl) Hst) as (Hpc & Hpre & Habi).
              destruct (Hn Hpc Hpre Habi) as (Hs & Hmem & Hret).
              exact (Hto 21%nat ltac:(lia)
                      (m_printf_ret 33 21 s s' (or_introl (conj eq_refl eq_refl)) Hst Hs Hmem Hret)).
            * (* printf, second call *)
              destruct Hpr as [Hn | Heq]; [| exact (Hsame Heq)].
              destruct (m_printf_at 34 s (or_intror eq_refl) Hst) as (Hpc & Hpre & Habi).
              destruct (Hn Hpc Hpre Habi) as (Hs & Hmem & Hret).
              exact (Hto 26%nat ltac:(lia)
                      (m_printf_ret 34 26 s s' (or_intror (conj eq_refl eq_refl)) Hst Hs Hmem Hret)).
            * (* exit *)
              destruct Hex as [Hn | Heq]; [| exact (Hsame Heq)].
              destruct (m_exit_at s Hst) as (Hpc & Habi).
              exact (Hsame (eq_sym (Hn Hpc Habi))).
        - (* a point of the call of tl_fib *)
          pose proof Hc as (Hp & _).
          split; [| exact (Ebody_call N p s s' Hp)].
          destruct Hnf as [Hn | <-]; [| right; exists N, p; exact Hc].
          destruct (Hn (proj2 (in_fib_at_pc s) (call_pt_in N p s Hp))) as [H1 | H2].
          + destruct (in_call_step N p s s' Hc H1) as [(p' & _ & Hc') | Hst'].
            * right. exists N, p'. exact Hc'.
            * left. exists 15%nat. split; [lia | exact Hst'].
          + right. exists N, p. exact (in_call_tick N p s s' Hc H2).
Qed.

(* ========================================================================== *)
(* A behaviour of the linked code                                             *)
(* ========================================================================== *)

Section linked.

Variable sigma : behavior state.
Hypothesis Hfib : exec_static tl_fib_impl_s sigma.
Hypothesis Hlibc : unsafe_libc e_static sigma.
Hypothesis Hmain : exec_static main_s sigma.

Lemma linked_first :
        m_stage 0 (sigma 0%nat).
Proof.
        destruct Hmain as (I1 & I2 & I4 & Is & _).
        destruct Is as ((_ & Ism) & Isf).
        destruct Hfib as (_ & _ & _ & Isc & _).
        destruct Isc as (_ & Isc).
        split; [exact (conj I1 (conj Ism (conj Isf Isc))) |].
        split; [exact (pc_reg _ _ I2) | exact (reg_sp _ I4)].
Qed.

Lemma linked_step k :
        G (sigma k) ->
                G (sigma (S k))
                /\ Ebody (sigma k) (sigma (S k)).
Proof.
        intros Hg.
        destruct Hmain as (_ & _ & _ & _ & Hn & _).
        destruct Hn as ((_ & Hnm) & _).
        destruct Hfib as (_ & _ & _ & _ & Hnf & _).
        destruct Hnf as (_ & Hnf).
        destruct Hlibc as ((Hp & _) & He & (Hgr & _)).
        exact (G_step _ _ Hg (next_at sigma _ Hnf k) (next_at sigma _ Hnm k)
                (next_at sigma _ Hp k) (next_at sigma _ He k) (next_at sigma _ Hgr k)).
Qed.

Lemma linked_G k :
        G (sigma k).
Proof.
        induction k as [| k IH]; [| exact (proj1 (linked_step k IH))].
        left. exists 0%nat. split; [lia | exact linked_first].
Qed.

(* The linked code is an environment of tl_fib. *)
Lemma linked_E :
        E e_static sigma.
Proof.
        intros k. unfold Lift2, util_suffix. rewrite Nat.add_0_r, Nat.add_1_r.
        exact (proj2 (linked_step k (linked_G k))).
Qed.

End linked.

(* ========================================================================== *)
(* thm_4                                                                      *)
(* ========================================================================== *)

Theorem thm_4 :
        valid ((\rmap (rm e_static) impl_linked)
                        \impl (\rmap (rm e_static) spec_linked)).
Proof.
        intros tau (sigma & Hs & Himpl & Hlibc & Hmain).
        apply (turtle.compat.sail.riscv.examples.fib.thm_3_proof_x.thm_3 tau).
        exists sigma. split; [exact Hs |].
        exact (conj (linked_E sigma Himpl Hlibc Hmain) (conj Himpl (conj Hlibc Hmain))).
Qed.

(* The statement of thm_4.v. *)
Definition thm_4_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_4.thm_4 in exact t) :=
        thm_4.

Print Assumptions thm_4.
