(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require Riscv.rv64d_types.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.notation.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.
Require Import turtle.gen.reg.
Require Import turtle.gen.step.
Require Import turtle.gen.tla.
Require Import turtle.gen.base.
Require Import turtle.gen.load.
Require Import turtle.gen.init.
Require Import turtle.compat.sail.riscv.examples.print32.conf_default.
Require Import turtle.compat.sail.riscv.examples.print32.main_1.
Require Import turtle.compat.sail.riscv.examples.print32.main_2.
Require Import turtle.compat.sail.riscv.examples.print32.thm.
Require Import turtle.compat.sail.riscv.examples.print32.thm_proof_x.
Require Import turtle.compat.sail.riscv.examples.print32.thm_2_non_trivial.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Module T := rv64d_types.

(* ========================================================================== *)
(* A first state of main_1                                                    *)
(* ========================================================================== *)

Definition main_bytes : list Z := Eval vm_compute in sec_bytes (main_1.main_sec e_static).
Definition fmt_bytes  : list Z := Eval vm_compute in sec_bytes main_1._tl_fmt_sec.

(* main and the format; zero elsewhere, the stack too. *)
Definition s0_mem : memory :=
        put_bytes 0x10000 main_bytes (
        put_bytes 0x100000 fmt_bytes
                zero_mem).

(* The registers of `conf_default`, the PC at main, the stack pointer at the
        end of the stack. *)
Definition s0_regs : T.regstate :=
        T.register_set (T.R_bitvector_64 T.PC) (definitions.Z_to_bv 64 0x10000) (
        T.register_set (T.R_bitvector_64 T.x2) (definitions.Z_to_bv 64 0x4000000000) (
        T.register_set (T.R_Privilege T.cur_privilege) conf_cur_privilege (
        T.register_set (T.R_bitvector_64 T.misa) conf_misa (
        T.register_set (T.R_bitvector_64 T.mstatus) (Values.mword_of_int 0xa00000000) (
        T.register_set (T.R_bitvector_64 T.mie) conf_mie (
        T.register_set (T.R_bitvector_64 T.satp) (Values.mword_of_int 0x0) (
        T.register_set (T.R_bitvector_64 T.senvcfg) (Values.mword_of_int 0x0) (
        T.register_set (T.R_vector_64_bitvector_8 T.pmpcfg_n)
                (Values.vec_update_dec (Values.vector_init 64 (Values.mword_of_int 0x0)) 0
                        conf_pmpcfg0) (
        T.register_set (T.R_vector_64_bitvector_64 T.pmpaddr_n)
                (Values.vec_update_dec (Values.vector_init 64 (Values.mword_of_int 0x0)) 0
                        conf_pmpaddr0) (
        T.register_set (T.R_bitvector_1 T.elp) conf_elp (
        T.register_set (T.R_HartState T.hart_state) conf_hart_state (
        T.register_set (T.R_list_PMA_Region T.pma_regions) conf_pma_regions (
        T.register_set (T.R_option_bitvector_64 T.htif_tohost_base) conf_htif_tohost_base
                T.init_regstate))))))))))))).

Definition s0 : state :=
        Build_state s0_regs s0_mem.

Lemma s0_init :
        conf_default s0.
Proof.
        unfold conf_default.
        repeat match goal with |- _ /\ _ => split end.
        all: closed_eq.
Qed.

Lemma s0_pc :
        exec_init_pc_1 (e_static "main"%string) s0.
Proof.
        closed_eq.
Qed.

Lemma s0_sp :
        exec_init_sp_1 (conf_stack_addr + conf_stack_size) s0.
Proof.
        closed_eq.
Qed.

Lemma s0_main :
        exec_init_src_1 (main_1.main_sec e_static) (e_static "main"%string) s0.
Proof.
        let l := eval vm_compute in (main_1.main_sec e_static) in
        change (main_1.main_sec e_static) with l.
        change (e_static "main"%string) with 0x10000.
        cbn [exec_init_src_1 _init_s_text].
        repeat match goal with |- _ /\ _ => split end.
        all: first [ exact I | instr_intro ].
Qed.

Lemma s0_fmt :
        exec_init_src_1 main_1._tl_fmt_sec (e_static ".tl_fmt"%string) s0.
Proof.
        let l := eval vm_compute in main_1._tl_fmt_sec in
        change main_1._tl_fmt_sec with l.
        change (e_static ".tl_fmt"%string) with 0x100000.
        cbn [exec_init_src_1 _init_s_data].
        repeat match goal with |- _ /\ _ => split end.
        all: first [ exact I | closed_eq ].
Qed.

(* The first stage of main_1, as `main_2_start_state`. *)
Lemma main_1_start_state s :
        conf_default s ->
        exec_init_pc_1 (e_static "main"%string) s ->
        exec_init_sp_1 (conf_stack_addr + conf_stack_size) s ->
        exec_init_src_1 main_1._tl_fmt_sec (e_static ".tl_fmt"%string) s ->
        exec_init_src_1 (main_1.main_sec e_static) (e_static "main"%string) s ->
                main_1_stage 0 s.
Proof.
        intros Hi Hpc Hsp Hfmt Hmain.
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
        - cbn [main_1_regs]. exact (reg_sp s Hsp).
Qed.

Lemma s0_stage :
        main_1_stage 0 s0.
Proof.
        exact (main_1_start_state s0 s0_init s0_pc s0_sp s0_fmt s0_main).
Qed.

(* ========================================================================== *)
(* A step of a run                                                            *)
(* ========================================================================== *)

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

(* A step that every section and every procedure of the libc allows. *)
Definition run_next (s s' : state) : Prop :=
        (exec_next_src_1 (main_1.main_sec e_static) (e_static "main"%string) s s' \/ s = s')
        /\ (exec_next_src_1 main_1._tl_fmt_sec (e_static ".tl_fmt"%string) s s' \/ s = s')
        /\ (printf_next s s' \/ s = s')
        /\ (exit_next s s' \/ s = s')
        /\ (getrandom_next s s' \/ s = s').

(* At the libc: in no section. *)
Lemma libc_out s :
        0x14000 <= _pc_addr s < 0x100000 ->
                ~ at_pc (main_1.main_sec e_static) (e_static "main"%string) s
                /\ ~ at_pc main_1._tl_fmt_sec (e_static ".tl_fmt"%string) s.
Proof.
        unfold at_pc.
        change (_section_size (main_1.main_sec e_static)) with 60.
        change (_section_size main_1._tl_fmt_sec) with 5.
        change (e_static "main"%string) with 0x10000.
        change (e_static ".tl_fmt"%string) with 0x100000.
        intros H. split; lia.
Qed.

Ltac libc_addr :=
        change (e_static "printf"%string) with 0x14000 in *;
        change (e_static "exit"%string) with 0x14100 in *;
        change (e_static "getrandom"%string) with 0x14200 in *.

(* A step of an instruction, below the libc. *)
Lemma run_next_instr s s' :
        exec_eval_step_1 s s' ->
        _pc_addr s < 0x14000 ->
                run_next s s'.
Proof.
        intros H1 Hpc. unfold run_next, printf_next, exit_next, getrandom_next. libc_addr.
        split; [left; intros _; left; exact H1 |].
        split; [left; intros _; left; exact H1 |].
        split; [left; intros Hx; lia |].
        split; [left; intros Hx; lia |].
        left; intros Hx; lia.
Qed.

(* The return from printf, to `ra`. *)
Lemma run_next_ret a s :
        0 <= a < 2 ^ 64 ->
        _pc_addr s = e_static "printf"%string ->
        abi_ra s = a ->
                run_next s (ret_to a s).
Proof.
        intros Ha Hpc Hra. unfold run_next, printf_next, exit_next, getrandom_next. libc_addr.
        destruct (libc_out s ltac:(lia)) as (Nm & Nr).
        split; [left; intros Hx; contradiction |].
        split; [left; intros Hx; contradiction |].
        split; [left; intros _ _ _; exact (ret_to_abi a s Ha Hra) |].
        split; [left; intros Hx; lia |].
        left; intros Hx; lia.
Qed.

(* From a stage but the exit: a step of a run, to the next stage. *)
Lemma stage_run_step k s :
        (k < 47)%nat ->
        main_1_stage k s ->
                exists s',
                run_next s s'
                /\ main_1_stage (S k) s'.
Proof.
        intros Hk Hst.
        destruct (main_1_call k) eqn:Hc.
        - (* the return from printf *)
          destruct (main_1_call_at k s Hc Hst) as (Hpc & _ & _ & Hra & _).
          exists (ret_to 0x10020 s). split.
          + exact (run_next_ret 0x10020 s ltac:(lia) Hpc Hra).
          + exact (main_1_ret k s _ Hc Hst (ret_to_abi 0x10020 s ltac:(lia) Hra)).
        - (* an instruction *)
          destruct (main_1_step_main k s Hk Hc Hst 0 true) as (s' & Ho & Hst').
          exists s'. split; [| exact Hst'].
          apply run_next_instr; [exact (step_1_of s s' Ho) |].
          pose proof (main_1_at_main k s Hc Hk Hst) as Hat. unfold at_pc in Hat.
          change (_section_size (main_1.main_sec e_static)) with 60 in Hat.
          change (e_static "main"%string) with 0x10000 in Hat. lia.
Qed.

(* ========================================================================== *)
(* A run to the exit                                                          *)
(* ========================================================================== *)

(* A run from `s`: it reaches the exit, and stays there. *)
Definition runs (s : state) : Prop :=
        exists f : nat -> state,
        f 0%nat = s
        /\ (forall n, run_next (f n) (f (S n)))
        /\ exists N,
                main_1_stage 47 (f N)
                /\ forall n, (N <= n)%nat -> f n = f N.

Lemma runs_exit s :
        main_1_stage 47 s ->
                runs s.
Proof.
        intros Hs. exists (fun _ => s). split; [reflexivity |]. split.
        - intros _. unfold run_next. repeat split; right; reflexivity.
        - exists 0%nat. split; [exact Hs | intros _ _; reflexivity].
Qed.

Lemma runs_step s s' :
        run_next s s' ->
        runs s' ->
                runs s.
Proof.
        intros Hn (f & H0 & Hf & N & HN & Hend).
        exists (fun n => match n with O => s | S n' => f n' end).
        split; [reflexivity |]. split.
        - intros [| n]; [rewrite H0; exact Hn | exact (Hf n)].
        - exists (S N). split; [exact HN |].
          intros [| n] Hn'; [lia | exact (Hend n ltac:(lia))].
Qed.

(* From a stage, by induction on the stages that are left. *)
Lemma stage_runs d :
        forall k s,
        (k + d = 47)%nat ->
        main_1_stage k s ->
                runs s.
Proof.
        induction d as [| d IH]; intros k s Hk Hst.
        - rewrite Nat.add_0_r in Hk. subst k. exact (runs_exit s Hst).
        - destruct (stage_run_step k s ltac:(lia) Hst) as (s' & Hn & Hst').
          exact (runs_step s s' Hn (IH (S k) s' ltac:(lia) Hst')).
Qed.

(* A run from the first state is a behaviour of main_1 and the libc. *)
Lemma run_impl (f : nat -> state) :
        f 0%nat = s0 ->
        (forall n, run_next (f n) (f (S n))) ->
        (exists N, main_1_stage 47 (f N) /\ forall n, (N <= n)%nat -> f n = f N) ->
                exec_static main_1_s f
                /\ unsafe_libc e_static f.
Proof.
        intros H0 Hn (N & HN & Hend).
        destruct (main_1_exit_at _ HN) as (Hx & _). libc_addr.
        destruct (libc_out (f N) ltac:(lia)) as (Nm & Nr).
        (* no fair action at the exit *)
        assert (Hwf : forall A : state -> state -> Prop,
                (forall s', ~ A (f N) s') ->
                        (\wf (\lift2 A) \sub exec_vars) f).
        { intros A HA. apply (wf_end f A N); [exact Hend |].
          intros s' Ha. exfalso. exact (HA s' Ha). }
        split.
        - (* main_1 *)
          split; [unfold Lift1; rewrite H0; exact s0_init |].
          split; [unfold exec_init_pc, Lift1; rewrite H0; exact s0_pc |].
          split; [unfold exec_init_sp, Lift1; rewrite H0; exact s0_sp |].
          split; [split; [split; [exact I |] |]; unfold Lift1; rewrite H0; [exact s0_main | exact s0_fmt] |].
          split; [split; [split; [exact I |] |] | split; [split; [exact I |] |]].
          + apply next_intro. intros i. exact (proj1 (Hn i)).
          + apply next_intro. intros i. exact (proj1 (proj2 (Hn i))).
          + apply Hwf. intros s' (Hat & _). exact (Nm Hat).
          + apply Hwf. intros s' (Hat & _). exact (Nr Hat).
        - (* the libc *)
          split; [split | split; [| split]].
          + apply next_intro. intros i. exact (proj1 (proj2 (proj2 (Hn i)))).
          + apply Hwf. intros s' (Hpc & _). libc_addr. lia.
          + apply next_intro. intros i. exact (proj1 (proj2 (proj2 (proj2 (Hn i))))).
          + apply next_intro. intros i. exact (proj2 (proj2 (proj2 (proj2 (Hn i))))).
          + apply Hwf. intros s' (Hpc & _). libc_addr. lia.
Qed.

(* A behaviour of main_1 and the libc. *)
Lemma main_1_run :
        exists beh,
        exec_static main_1_s beh
        /\ unsafe_libc e_static beh.
Proof.
        destruct (stage_runs 47 0%nat s0 eq_refl s0_stage) as (f & H0 & Hn & Hend).
        exists f. exact (run_impl f H0 Hn Hend).
Qed.

(* A first state with the PC at 0: no behaviour of `exec_static`. *)
Lemma not_exec src :
        ~ exec_static src (fun _ => ret_to 0 s0).
Proof.
        intros (_ & Hpc & _).
        change (_pc_addr (ret_to 0 s0) = 0x10000) in Hpc.
        rewrite (reg_pc 0 _ (ret_to_pc 0 s0) ltac:(lia)) in Hpc. discriminate Hpc.
Qed.

(* ========================================================================== *)
(* thm_2_non_trivial                                                          *)
(* ========================================================================== *)

Theorem thm_2_non_trivial_1 :
        non_trivial (exec_static main_1_s \land unsafe_libc e_static).
Proof.
        split.
        - exact main_1_run.
        - exists (fun _ => ret_to 0 s0). intros (Hmain & _).
          exact (not_exec main_1_s Hmain).
Qed.

Theorem thm_2_non_trivial_2 :
        non_trivial (exec_static main_2_s \land unsafe_libc e_static).
Proof.
        split.
        - (* by thm_2, from the behaviour of main_1 *)
          destruct main_1_run as (beh1 & H1).
          assert (Hr : (\rmap (rm e_static) (exec_static main_1_s \land unsafe_libc e_static))
                        (fun n => rm e_static (beh1 n))).
          { exists beh1. split; [apply stuttering_equivalent_refl | exact H1]. }
          destruct (thm_proof_x.thm_2 _ Hr) as (beh2 & _ & H2).
          exists beh2. exact H2.
        - exists (fun _ => ret_to 0 s0). intros (Hmain & _).
          exact (not_exec main_2_s Hmain).
Qed.

(* ========================================================================== *)
(* The exit                                                                   *)
(* ========================================================================== *)

(* At the exit, with what it expects: there for good. *)
Lemma exit_stays (sigma : behavior state) i d :
        unsafe_libc e_static sigma ->
        _pc_addr (sigma i) = e_static "exit"%string ->
        abi_precond (sigma i) ->
                sigma (i + d)%nat = sigma i.
Proof.
        intros (_ & He & _) Hpc Habi.
        induction d as [| d IH]; [rewrite Nat.add_0_r; reflexivity |].
        rewrite Nat.add_succ_r.
        destruct (next_at sigma _ He (i + d)%nat) as [Hn | Heq]; [| rewrite <- Heq; exact IH].
        rewrite <- IH in Hpc, Habi. rewrite (Hn Hpc Habi). exact IH.
Qed.

Lemma exit_ends (sigma : behavior state) i :
        unsafe_libc e_static sigma ->
        _pc_addr (sigma i) = e_static "exit"%string ->
        abi_precond (sigma i) ->
                (<>[] \lift1 pc_at_exit) sigma.
Proof.
        intros Hlibc Hpc Habi.
        exists i. intros d. unfold Lift1, util_suffix. rewrite Nat.add_0_r.
        rewrite (exit_stays sigma i d Hlibc Hpc Habi). exact Hpc.
Qed.

(* ========================================================================== *)
(* Every behaviour of main_1 reaches the exit                                 *)
(* ========================================================================== *)

(* Every stage is reached. *)
Lemma main_1_reach (sigma : behavior state) k :
        exec_static main_1_s sigma ->
        unsafe_libc e_static sigma ->
        (k <= 47)%nat ->
                exists i,
                main_1_stage k (sigma i).
Proof.
        intros Hmain Hlibc. induction k as [| k IH]; intros Hk.
        - exists 0%nat. exact (main_1_start sigma Hmain).
        - destruct (IH ltac:(lia)) as (i & Hi).
          destruct (main_1_progress sigma k Hmain Hlibc ltac:(lia) i Hi) as (j & _ & Hj).
          exists j. exact Hj.
Qed.

(* ========================================================================== *)
(* Every behaviour of main_2 reaches the exit                                 *)
(* ========================================================================== *)

(* A call keeps the code: it keeps the memory. *)
Lemma main_2_prog_kept s s' :
        abi_opt_stepcond_preserve_mem s s' ->
        abi_stepcond_preserve_conf s s' ->
        main_2_prog s ->
                main_2_prog s'.
Proof.
        intros Hm Hi (H0 & M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & Hf).
        unfold abi_opt_stepcond_preserve_mem in Hm.
        split; [exact (conf_keep s s' Hi H0) |].
        unfold mem_word in *. rewrite <- Hm.
        repeat (split; [assumption |]).
        exact (exec_init_src_1_mem _ _ s s' (eq_sym Hm) Hf).
Qed.

(* At the call: printf with what it expects, the return address after the call. *)
Lemma main_2_call_at s :
        main_2_stage 5 s ->
                _pc_addr s = e_static "printf"%string
                /\ _printf_precond s
                /\ abi_precond s
                /\ abi_ra s = 0x10014.
Proof.
        intros Hs. pose proof (main_2_stage_pc 5 s Hs) as Hpc.
        destruct Hs as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hf) & _ & Hx).
        cbn [main_2_regs] in Hx. destruct Hx as (X2 & _ & X10 & X1).
        split; [exact Hpc |].
        split; [apply (main_2_fmt s Hf); unfold abi_arg0, abi_a0; exact (reg_abi _ _ _ X10 ltac:(lia)) |].
        split; [unfold abi_precond, abi_sp; rewrite (reg_abi _ _ _ X2 ltac:(lia)); reflexivity |].
        unfold abi_ra. exact (reg_abi _ _ _ X1 ltac:(lia)).
Qed.

(* The return from the call: the stage after. *)
Lemma main_2_call_ret s s' :
        main_2_stage 5 s ->
        abi_stepcond s s'
                /\ abi_opt_stepcond_preserve_mem s s'
                /\ abi_opt_stepcond_return s s' ->
                main_2_stage 6 s'.
Proof.
        intros Hs ((Hregs & Hconf) & Hmem & Hret).
        destruct (main_2_call_at s Hs) as (_ & _ & _ & Hra).
        destruct Hs as (Hp & _ & Hx). cbn [main_2_regs] in Hx. destruct Hx as (X2 & _ & _ & _).
        split; [exact (main_2_prog_kept s s' Hmem Hconf Hp) |].
        unfold abi_opt_stepcond_return in Hret. rewrite Hra in Hret.
        split; [apply pc_reg; exact Hret |].
        cbn [main_2_regs]. exact (reg_preserved T.x2 _ s s' Hregs eq_refl X2).
Qed.

(* At the exit. *)
Lemma main_2_exit_at s :
        main_2_stage 9 s ->
                _pc_addr s = e_static "exit"%string
                /\ abi_precond s.
Proof.
        intros Hs. pose proof (main_2_stage_pc 9 s Hs) as Hpc.
        destruct Hs as (_ & _ & Hx). cbn [main_2_regs] in Hx. destruct Hx as (X2 & _ & _).
        split; [exact Hpc |].
        unfold abi_precond, abi_sp. rewrite (reg_abi _ _ _ X2 ltac:(lia)). reflexivity.
Qed.

(* From the call, the stage after: printf is fair. *)
Lemma main_2_call_leads (sigma : behavior state) i :
        unsafe_libc e_static sigma ->
        main_2_stage 5 (sigma i) ->
                exists j,
                main_2_stage 6 (sigma j).
Proof.
        intros ((Hp & Hwp) & _) Hi.
        destruct (leads_wf sigma _ (main_2_stage 5) (main_2_stage 6) Hwp) with (i := i)
                as (j & _ & Hj); [ | | | exact Hi | exists j; exact Hj ].
        - intros i' Hi'.
          destruct (next_at sigma _ Hp i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
          destruct (main_2_call_at _ Hi') as (Hpc & Hpre & Habi & _).
          right. exact (main_2_call_ret _ _ Hi' (Hn Hpc Hpre Habi)).
        - intros s Hs. destruct (main_2_call_at s Hs) as (Hpc & Hpre & Habi & _).
          exists (main_2_ret s). split.
          + exact (conj Hpc (conj Hpre (conj Habi (main_2_ret_abi s Hs)))).
          + unfold main_2_ret. apply ret_to_ne; [lia |]. rewrite Hpc. cbn. lia.
        - intros s s' Hs (_ & _ & _ & Ha). exact (main_2_call_ret s s' Hs Ha).
Qed.

(* Every stage is reached. *)
Lemma main_2_reach (sigma : behavior state) k :
        exec_static main_2_s sigma ->
        unsafe_libc e_static sigma ->
        (k <= 9)%nat ->
                exists i,
                main_2_stage k (sigma i).
Proof.
        intros Hmain Hlibc. induction k as [| k IH]; intros Hk.
        - exists 0%nat. exact (main_2_start sigma Hmain).
        - destruct (IH ltac:(lia)) as (i & Hi).
          destruct (Nat.eq_dec k 5) as [-> | Hc].
          + exact (main_2_call_leads sigma i Hlibc Hi).
          + exact (main_2_leads sigma k ltac:(lia) Hc Hmain i Hi).
Qed.

(* ========================================================================== *)
(* thm_2_termination                                                          *)
(* ========================================================================== *)

Theorem thm_2_termination_1 :
        valid (exec_static main_1_s \land unsafe_libc e_static
                \impl <>[] \lift1 pc_at_exit).
Proof.
        intros sigma (Hmain & Hlibc).
        destruct (main_1_reach sigma 47 Hmain Hlibc ltac:(lia)) as (i & Hi).
        destruct (main_1_exit_at _ Hi) as (Hpc & Habi).
        exact (exit_ends sigma i Hlibc Hpc Habi).
Qed.

Theorem thm_2_termination_2 :
        valid (exec_static main_2_s \land unsafe_libc e_static
                \impl <>[] \lift1 pc_at_exit).
Proof.
        intros sigma (Hmain & Hlibc).
        destruct (main_2_reach sigma 9 Hmain Hlibc ltac:(lia)) as (i & Hi).
        destruct (main_2_exit_at _ Hi) as (Hpc & Habi).
        exact (exit_ends sigma i Hlibc Hpc Habi).
Qed.

(* The statements of thm_2_non_trivial.v. *)
Definition thm_2_non_trivial_1_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.print32.thm_2_non_trivial.thm_2_non_trivial_1 in exact t) :=
        thm_2_non_trivial_1.

Definition thm_2_non_trivial_2_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.print32.thm_2_non_trivial.thm_2_non_trivial_2 in exact t) :=
        thm_2_non_trivial_2.

Definition thm_2_termination_1_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.print32.thm_2_non_trivial.thm_2_termination_1 in exact t) :=
        thm_2_termination_1.

Definition thm_2_termination_2_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.print32.thm_2_non_trivial.thm_2_termination_2 in exact t) :=
        thm_2_termination_2.

Print Assumptions thm_2_non_trivial_1.
Print Assumptions thm_2_non_trivial_2.
Print Assumptions thm_2_termination_1.
Print Assumptions thm_2_termination_2.
