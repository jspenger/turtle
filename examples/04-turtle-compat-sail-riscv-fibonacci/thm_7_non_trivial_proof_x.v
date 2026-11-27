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
Require Riscv.rv64d_types.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.notation.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.glu.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.gen.eval.
Require Import turtle.gen.frame.
Require Import turtle.gen.reg.
Require Import turtle.gen.step.
Require Import turtle.gen.tla.
Require Import turtle.gen.load.
Require Import turtle.gen.init.
Require Import turtle.gen.base.
Require Import turtle.compat.sail.riscv.examples.fib.conf_default.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.main.
Require Import turtle.compat.sail.riscv.examples.fib.spec.
Require turtle.compat.sail.riscv.examples.fib.spec_tla.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1_proof_x.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4.
Require Import turtle.compat.sail.riscv.examples.fib.thm_4_proof_x.
Require Import turtle.compat.sail.riscv.examples.fib.thm_7_non_trivial.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Module T := rv64d_types.

(* ========================================================================== *)
(* A first state                                                              *)
(* ========================================================================== *)

Definition main_bytes : list Z := Eval vm_compute in sec_bytes (main_sec e_static).
Definition fmt_bytes  : list Z := Eval vm_compute in sec_bytes _tl_fmt_sec.
Definition fib_bytes  : list Z := Eval vm_compute in sec_bytes (tl_fib_impl_sec e_static).

(* main, the format and tl_fib; zero elsewhere, the stack too. *)
Definition s0_mem : memory :=
        put_bytes 0x10000 main_bytes (
        put_bytes 0x100000 fmt_bytes (
        put_bytes 0x11000 fib_bytes
                zero_mem)).

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
        exec_init_src_1 (main_sec e_static) (e_static "main"%string) s0.
Proof.
        let l := eval vm_compute in (main_sec e_static) in
        change (main_sec e_static) with l.
        change (e_static "main"%string) with 0x10000.
        cbn [exec_init_src_1 _init_s_text].
        repeat match goal with |- _ /\ _ => split end.
        all: first [ exact I | instr_intro ].
Qed.

Lemma s0_fib :
        exec_init_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s0.
Proof.
        let l := eval vm_compute in (tl_fib_impl_sec e_static) in
        change (tl_fib_impl_sec e_static) with l.
        change (e_static "tl_fib"%string) with 0x11000.
        cbn [exec_init_src_1 _init_s_text].
        repeat match goal with |- _ /\ _ => split end.
        all: first [ exact I | instr_intro ].
Qed.

Lemma s0_fmt :
        exec_init_src_1 _tl_fmt_sec (e_static ".tl_fmt"%string) s0.
Proof.
        let l := eval vm_compute in _tl_fmt_sec in
        change _tl_fmt_sec with l.
        change (e_static ".tl_fmt"%string) with 0x100000.
        cbn [exec_init_src_1 _init_s_data].
        repeat match goal with |- _ /\ _ => split end.
        all: first [ exact I | closed_eq ].
Qed.

(* The first stage of main. *)
Lemma s0_stage :
        m_stage 0 s0.
Proof.
        split; [exact (conj s0_init (conj s0_main (conj s0_fmt s0_fib))) |].
        split; [exact (pc_reg _ _ s0_pc) | exact (reg_sp _ s0_sp)].
Qed.

(* ========================================================================== *)
(* The return from a call of the libc                                         *)
(* ========================================================================== *)

(* The return of getrandom to `a`, with the result 8 and the memory as it
        was. *)
Definition ret_8_to (a : Z) (s : state) : state :=
        set_reg (T.R_bitvector_64 T.x10) (definitions.Z_to_bv 64 8) (ret_to a s).

Lemma ret_8_to_pc a s :
        reg T.PC a (ret_8_to a s).
Proof.
        unfold reg, ret_8_to. rewrite lookup_set_other by reflexivity. apply ret_to_pc.
Qed.

(* A return to `ra` with the result 8: the step of getrandom, asked for 8
        bytes. *)
Lemma ret_8_to_abi a s :
        0 <= a < 2 ^ 64 ->
        abi_ra s = a ->
        abi_arg1 s = 8 ->
                _getrandom_stepcond s (ret_8_to a s)
                /\ abi_stepcond s (ret_8_to a s)
                /\ abi_opt_stepcond_return s (ret_8_to a s).
Proof.
        intros Ha Hra Hsz. split; [| split; [split |]].
        - unfold _getrandom_stepcond. cbv zeta. exists 8. rewrite Hsz.
          split; [lia |]. split; [| intros addr _; reflexivity].
          left. unfold abi_signed_res0, abi_signed_a0, _state_regs_to_signed_z, st_regs_read, _regs_read.
          unfold ret_8_to. rewrite lookup_set_same. reflexivity.
        - unfold abi_stepcond_preserve_regs, _state_regs_to_bv, st_regs_read, _regs_read, ret_8_to, ret_to.
          repeat split; rewrite !lookup_set_other by reflexivity; reflexivity.
        - apply (preserve_conf_only (T.R_bitvector_64 T.PC :: T.R_bitvector_64 T.x10 :: nil) s _ eq_refl).
          unfold ret_8_to, ret_to. only_tac.
        - unfold abi_opt_stepcond_return. rewrite Hra. exact (reg_pc a _ (ret_8_to_pc a s) Ha).
Qed.

(* A state at another address is another state. *)
Lemma pc_ne a s s' :
        reg T.PC a s' ->
        0 <= a < 2 ^ 64 ->
        _pc_addr s <> a ->
                s <> s'.
Proof.
        intros Hpc Ha Hne Heq. apply Hne. rewrite Heq. exact (reg_pc a s' Hpc Ha).
Qed.

(* getrandom can return. *)
Lemma m_getrandom_step s :
        reg T.PC (m_pc 32) s /\ m_regs 32 s ->
                exists s',
                s <> s'
                /\ _getrandom_stepcond s s'
                /\ abi_stepcond s s'
                /\ abi_opt_stepcond_return s s'.
Proof.
        intros (Hpc & Hx). cbn [m_pc m_regs] in Hpc, Hx.
        destruct Hx as (X2 & X10 & X11 & X12 & X1).
        exists (ret_8_to 0x10018 s). split.
        - apply (pc_ne 0x10018 _ _ (ret_8_to_pc _ s)); [lia |].
          rewrite (reg_pc _ _ Hpc ltac:(lia)). lia.
        - apply ret_8_to_abi; [lia | exact (reg_abi _ _ _ X1 ltac:(lia)) | exact (reg_abi _ _ _ X11 ltac:(lia))].
Qed.

(* printf can return, from the call of stage `k`. *)
Lemma m_printf_step k s :
        k = 33%nat \/ k = 34%nat ->
        reg T.PC (m_pc k) s /\ m_regs k s ->
                exists s',
                s <> s'
                /\ abi_stepcond s s'
                /\ abi_opt_stepcond_preserve_mem s s'
                /\ abi_opt_stepcond_return s s'.
Proof.
        intros Hk (Hpc & Hx).
        destruct Hk as [-> | ->]; cbn [m_pc m_regs] in Hpc, Hx; destruct Hx as (X2 & X10 & X1).
        - exists (ret_to 0x10054 s). split.
          + apply (pc_ne 0x10054 _ _ (ret_to_pc _ s)); [lia |].
            rewrite (reg_pc _ _ Hpc ltac:(lia)). lia.
          + apply ret_to_abi; [lia | exact (reg_abi _ _ _ X1 ltac:(lia))].
        - exists (ret_to 0x10068 s). split.
          + apply (pc_ne 0x10068 _ _ (ret_to_pc _ s)); [lia |].
            rewrite (reg_pc _ _ Hpc ltac:(lia)). lia.
          + apply ret_to_abi; [lia | exact (reg_abi _ _ _ X1 ltac:(lia))].
Qed.

(* ========================================================================== *)
(* A step of a run                                                            *)
(* ========================================================================== *)

(* A step that every section and every procedure of the libc allows. *)
Definition run_next (s s' : state) : Prop :=
        (exec_next_src_1 (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s s' \/ s = s')
        /\ (exec_next_src_1 (main_sec e_static) (e_static "main"%string) s s' \/ s = s')
        /\ (exec_next_src_1 _tl_fmt_sec (e_static ".tl_fmt"%string) s s' \/ s = s')
        /\ (printf_next s s' \/ s = s')
        /\ (exit_next s s' \/ s = s')
        /\ (getrandom_next s s' \/ s = s').

(* At the libc: in no section. *)
Lemma libc_out s :
        0x14000 <= _pc_addr s < 0x100000 ->
                ~ at_pc (tl_fib_impl_sec e_static) (e_static "tl_fib"%string) s
                /\ ~ at_pc (main_sec e_static) (e_static "main"%string) s
                /\ ~ at_pc _tl_fmt_sec (e_static ".tl_fmt"%string) s.
Proof.
        unfold at_pc.
        change (_section_size (tl_fib_impl_sec e_static)) with 60.
        change (_section_size (main_sec e_static)) with 128.
        change (_section_size _tl_fmt_sec) with 5.
        change (e_static "tl_fib"%string) with 0x11000.
        change (e_static "main"%string) with 0x10000.
        change (e_static ".tl_fmt"%string) with 0x100000.
        intros H. repeat split; lia.
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
        split; [left; intros _; left; exact H1 |].
        split; [left; intros Hx; lia |].
        split; [left; intros Hx; lia |].
        left; intros Hx; lia.
Qed.

(* A step at the libc: a step of its three procedures. *)
Lemma run_next_libc s s' :
        0x14000 <= _pc_addr s < 0x100000 ->
        printf_next s s' ->
        exit_next s s' ->
        getrandom_next s s' ->
                run_next s s'.
Proof.
        intros Hpc Hp He Hg. destruct (libc_out s Hpc) as (Nf & Nm & Nr).
        split; [left; intros Hx; contradiction |].
        split; [left; intros Hx; contradiction |].
        split; [left; intros Hx; contradiction |].
        split; [left; exact Hp |].
        split; [left; exact He | left; exact Hg].
Qed.

(* From a stage but the exit: a step of a run, to what is after the stage. *)
Lemma m_run_step k s :
        (k < 35)%nat ->
        m_stage k s ->
                exists s',
                run_next s s'
                /\ m_after k s'.
Proof.
        intros Hk Hst.
        destruct (Nat.lt_ge_cases k 32) as [Hk32 | Hk32].
        - (* an instruction *)
          destruct (main_step k s Hk32 Hst 0 true) as (s' & Ho & _ & Ha).
          exists s'. split; [| exact Ha].
          apply run_next_instr; [exact (step_1_of s s' Ho) |].
          pose proof (m_stage_at k s Hk32 Hst) as Hat. unfold at_pc in Hat.
          change (_section_size (main_sec e_static)) with 128 in Hat.
          change (e_static "main"%string) with 0x10000 in Hat. lia.
        - (* a call of the libc *)
          assert (Hl : k = 32%nat \/ k = 33%nat \/ k = 34%nat) by lia.
          pose proof (m_stage_pc k s ltac:(lia) Hst) as Hpc.
          destruct Hl as [-> | [-> | ->]]; cbn [m_pc] in Hpc.
          + (* getrandom *)
            destruct (m_getrandom_step s (proj2 Hst)) as (s' & _ & Hgs & Hs & Hret).
            exists s'. split.
            * apply run_next_libc; unfold printf_next, exit_next, getrandom_next; libc_addr;
                      [ lia
                      | intros Hx; lia
                      | intros Hx; lia
                      | intros _ _ _; exact (conj Hgs (conj Hs Hret)) ].
            * left. exists 6%nat. split; [lia |]. split; [cbn [m_left]; lia |].
              exact (m_getrandom_ret s s' Hst Hgs Hs Hret).
          + (* printf, first call *)
            destruct (m_printf_step 33 s (or_introl eq_refl) (proj2 Hst)) as (s' & _ & Hs & Hmem & Hret).
            exists s'. split.
            * apply run_next_libc; unfold printf_next, exit_next, getrandom_next; libc_addr;
                      [ lia
                      | intros _ _ _; exact (conj Hs (conj Hmem Hret))
                      | intros Hx; lia
                      | intros Hx; lia ].
            * left. exists 21%nat. split; [lia |]. split; [cbn [m_left]; lia |].
              exact (m_printf_ret 33 21 s s' (or_introl (conj eq_refl eq_refl)) Hst Hs Hmem Hret).
          + (* printf, second call *)
            destruct (m_printf_step 34 s (or_intror eq_refl) (proj2 Hst)) as (s' & _ & Hs & Hmem & Hret).
            exists s'. split.
            * apply run_next_libc; unfold printf_next, exit_next, getrandom_next; libc_addr;
                      [ lia
                      | intros _ _ _; exact (conj Hs (conj Hmem Hret))
                      | intros Hx; lia
                      | intros Hx; lia ].
            * left. exists 26%nat. split; [lia |]. split; [cbn [m_left]; lia |].
              exact (m_printf_ret 34 26 s s' (or_intror (conj eq_refl eq_refl)) Hst Hs Hmem Hret).
Qed.

(* From a point of the call of tl_fib: a step of a run, to a point with fewer
        instructions left, or to the stage of main after the call. *)
Lemma call_run_step N p s :
        in_call N p s ->
                exists s',
                run_next s s'
                /\ ((exists p', (mu N p' < mu N p)%nat /\ in_call N p' s')
                        \/ m_stage 15 s').
Proof.
        intros Hc. pose proof Hc as (Hp & Hf & _).
        destruct (call_step N p s Hf Hp 0 true) as (s' & Ho & _).
        pose proof (step_1_of s s' Ho) as H1.
        exists s'. split; [| exact (in_call_step N p s s' Hc H1)].
        apply run_next_instr; [exact H1 |].
        pose proof (call_pt_in N p s Hp) as Hin. unfold in_fib in Hin. lia.
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
                m_stage 35 (f N)
                /\ forall n, (N <= n)%nat -> f n = f N.

Lemma runs_exit s :
        m_stage 35 s ->
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

(* From a point of the call of tl_fib, by induction on the instructions that
        are left. *)
Lemma call_runs m :
        forall N p s,
        mu N p = m ->
        in_call N p s ->
        (forall s', m_stage 15 s' -> runs s') ->
                runs s.
Proof.
        induction m as [m IH] using lt_wf_ind. intros N p s Hm Hc H15.
        destruct (call_run_step N p s Hc) as (s' & Hn & [(p' & Hlt & Hc') | Hst']).
        - apply (runs_step s s' Hn).
          exact (IH (mu N p') ltac:(lia) N p' s' eq_refl Hc' H15).
        - exact (runs_step s s' Hn (H15 s' Hst')).
Qed.

(* From a stage of main, by induction on the steps that are left. *)
Lemma stage_runs r :
        forall k s,
        m_left k = r ->
        (k < 36)%nat ->
        m_stage k s ->
                runs s.
Proof.
        induction r as [r IH] using lt_wf_ind. intros k s Hr Hk Hst.
        destruct (Nat.eq_dec k 35) as [-> | Hne]; [exact (runs_exit s Hst) |].
        destruct (m_run_step k s ltac:(lia) Hst) as (s' & Hn & Ha).
        apply (runs_step s s' Hn).
        destruct Ha as [(k' & Hk' & Hlt & Hst') | (-> & Hc)].
        - exact (IH (m_left k') ltac:(lia) k' s' eq_refl Hk' Hst').
        - apply (call_runs _ _ _ s' eq_refl (enter_fib s' Hc)). intros s2 H15.
          exact (IH (m_left 15) ltac:(subst r; cbn [m_left]; lia) 15%nat s2 eq_refl ltac:(lia) H15).
Qed.

(* A run from the first state is a behaviour of the linked code. *)
Lemma run_impl (f : nat -> state) :
        f 0%nat = s0 ->
        (forall n, run_next (f n) (f (S n))) ->
        (exists N, m_stage 35 (f N) /\ forall n, (N <= n)%nat -> f n = f N) ->
                impl_linked f.
Proof.
        intros H0 Hn (N & HN & Hend).
        destruct (m_exit_at _ HN) as (Hx & _). libc_addr.
        destruct (libc_out (f N) ltac:(lia)) as (Nf & Nm & Nr).
        (* no fair action at the exit *)
        assert (Hwf : forall A : state -> state -> Prop,
                (forall s', ~ A (f N) s') ->
                        (\wf (\lift2 A) \sub exec_vars) f).
        { intros A HA. apply (wf_end f A N); [exact Hend |].
          intros s' Ha. exfalso. exact (HA s' Ha). }
        split; [| split].
        - (* tl_fib *)
          split; [unfold Lift1; rewrite H0; exact s0_init |].
          split; [unfold exec_init_pc, Lift1; rewrite H0; exact s0_pc |].
          split; [unfold exec_init_sp, Lift1; rewrite H0; exact s0_sp |].
          split; [split; [exact I | unfold Lift1; rewrite H0; exact s0_fib] |].
          split; [split; [exact I |] | split; [exact I |]].
          + apply next_intro. intros i. exact (proj1 (Hn i)).
          + apply Hwf. intros s' (Hat & _). exact (Nf Hat).
        - (* the libc *)
          split; [split | split; [| split]].
          + apply next_intro. intros i. exact (proj1 (proj2 (proj2 (proj2 (Hn i))))).
          + apply Hwf. intros s' (Hpc & _). libc_addr. lia.
          + apply next_intro. intros i. exact (proj1 (proj2 (proj2 (proj2 (proj2 (Hn i)))))).
          + apply next_intro. intros i. exact (proj2 (proj2 (proj2 (proj2 (proj2 (Hn i)))))).
          + apply Hwf. intros s' (Hpc & _). libc_addr. lia.
        - (* main *)
          split; [unfold Lift1; rewrite H0; exact s0_init |].
          split; [unfold exec_init_pc, Lift1; rewrite H0; exact s0_pc |].
          split; [unfold exec_init_sp, Lift1; rewrite H0; exact s0_sp |].
          split; [split; [split; [exact I |] |]; unfold Lift1; rewrite H0; [exact s0_main | exact s0_fmt] |].
          split; [split; [split; [exact I |] |] | split; [split; [exact I |] |]].
          + apply next_intro. intros i. exact (proj1 (proj2 (Hn i))).
          + apply next_intro. intros i. exact (proj1 (proj2 (proj2 (Hn i)))).
          + apply Hwf. intros s' (Hat & _). exact (Nm Hat).
          + apply Hwf. intros s' (Hat & _). exact (Nr Hat).
Qed.

(* ========================================================================== *)
(* thm_7_non_trivial                                                          *)
(* ========================================================================== *)

Theorem thm_7_non_trivial :
        non_trivial impl_linked.
Proof.
        split.
        - (* a run from the first state *)
          destruct (stage_runs _ 0%nat s0 eq_refl ltac:(lia) s0_stage) as (f & H0 & Hn & Hend).
          exists f. exact (run_impl f H0 Hn Hend).
        - (* a first state with the PC at 0 *)
          exists (fun _ => ret_to 0 s0). intros ((_ & Hpc & _) & _).
          change (_pc_addr (ret_to 0 s0) = 0x10000) in Hpc.
          rewrite (reg_pc 0 _ (ret_to_pc 0 s0) ltac:(lia)) in Hpc. discriminate Hpc.
Qed.

(* ========================================================================== *)
(* Every behaviour reaches the exit                                           *)
(* ========================================================================== *)

Section reach.

Variable sigma : behavior state.
Hypothesis Hfib : exec_static tl_fib_impl_s sigma.
Hypothesis Hlibc : unsafe_libc e_static sigma.
Hypothesis Hmain : exec_static main_s sigma.

(* From an instruction of main: its step is taken, main is fair. *)
Lemma reach_instr k i :
        (k < 32)%nat ->
        m_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ m_after k (sigma j).
Proof.
        intros Hk Hst.
        destruct Hmain as (_ & _ & _ & _ & ((_ & Hnm) & _) & ((_ & Hwm) & _)).
        apply (leads_wf sigma _ (m_stage k) (m_after k) Hwm); [ | | | exact Hst].
        - intros i' Hi'.
          destruct (next_at sigma _ Hnm i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
          destruct (Hn (m_stage_at k _ Hk Hi')) as [H1 | H2].
          + right. exact (proj2 (proj1 (step_tla _ _ (main_step k _ Hk Hi')) _ H1)).
          + left. exact (m_tick k _ _ Hi' (tick_tla _ _ H2)).
        - intros s Hs.
          destruct (proj2 (step_tla s _ (main_step k s Hk Hs))) as (s' & H1 & Hne & _).
          exists s'. split; [exact (conj (m_stage_at k s Hk Hs) H1) |].
          intros Heq. apply Hne. rewrite Heq. reflexivity.
        - intros s s' Hs (_ & H1).
          exact (proj2 (proj1 (step_tla s _ (main_step k s Hk Hs)) s' H1)).
Qed.

(* From a stage but the exit: an instruction as above, a call of the libc
        returns, the libc is fair. *)
Lemma reach_stage k i :
        (k < 35)%nat ->
        m_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ m_after k (sigma j).
Proof.
        intros Hk Hst.
        destruct (Nat.lt_ge_cases k 32) as [Hk32 | Hk32]; [exact (reach_instr k i Hk32 Hst) |].
        assert (Hl : k = 32%nat \/ k = 33%nat \/ k = 34%nat) by lia.
        destruct Hlibc as ((Hp & Hwp) & _ & (Hgr & Hwg)).
        destruct Hl as [-> | [-> | ->]].
        - (* getrandom *)
          destruct (leads_wf sigma _ (m_stage 32) (m_stage 6) Hwg) with (i := i)
                  as (j & Hij & Hj); [ | | | exact Hst | ].
          + intros i' Hi'.
            destruct (next_at sigma _ Hgr i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
            destruct (m_getrandom_at _ Hi') as (Hpc & Hpre & Habi).
            destruct (Hn Hpc Hpre Habi) as (Hgs & Hs & Hret).
            right. exact (m_getrandom_ret _ _ Hi' Hgs Hs Hret).
          + intros s Hs0.
            destruct (m_getrandom_at s Hs0) as (Hpc & Hpre & Habi).
            destruct (m_getrandom_step s (proj2 Hs0)) as (s' & Hne & Hgs & Hs & Hret).
            exists s'. split; [| exact Hne].
            exact (conj Hpc (conj Hpre (conj Habi (conj Hgs (conj Hs Hret))))).
          + intros s s' Hs0 (_ & _ & _ & Hgs & Hs & Hret).
            exact (m_getrandom_ret s s' Hs0 Hgs Hs Hret).
          + exists j. split; [exact Hij |].
            left. exists 6%nat. split; [lia |]. split; [cbn [m_left]; lia | exact Hj].
        - (* printf, first call *)
          destruct (leads_wf sigma _ (m_stage 33) (m_stage 21) Hwp) with (i := i)
                  as (j & Hij & Hj); [ | | | exact Hst | ].
          + intros i' Hi'.
            destruct (next_at sigma _ Hp i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
            destruct (m_printf_at 33 _ (or_introl eq_refl) Hi') as (Hpc & Hpre & Habi).
            destruct (Hn Hpc Hpre Habi) as (Hs & Hmem & Hret).
            right. exact (m_printf_ret 33 21 _ _ (or_introl (conj eq_refl eq_refl)) Hi' Hs Hmem Hret).
          + intros s Hs0.
            destruct (m_printf_at 33 s (or_introl eq_refl) Hs0) as (Hpc & Hpre & Habi).
            destruct (m_printf_step 33 s (or_introl eq_refl) (proj2 Hs0)) as (s' & Hne & Hs & Hmem & Hret).
            exists s'. split; [| exact Hne].
            exact (conj Hpc (conj Hpre (conj Habi (conj Hs (conj Hmem Hret))))).
          + intros s s' Hs0 (_ & _ & _ & Hs & Hmem & Hret).
            exact (m_printf_ret 33 21 s s' (or_introl (conj eq_refl eq_refl)) Hs0 Hs Hmem Hret).
          + exists j. split; [exact Hij |].
            left. exists 21%nat. split; [lia |]. split; [cbn [m_left]; lia | exact Hj].
        - (* printf, second call *)
          destruct (leads_wf sigma _ (m_stage 34) (m_stage 26) Hwp) with (i := i)
                  as (j & Hij & Hj); [ | | | exact Hst | ].
          + intros i' Hi'.
            destruct (next_at sigma _ Hp i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
            destruct (m_printf_at 34 _ (or_intror eq_refl) Hi') as (Hpc & Hpre & Habi).
            destruct (Hn Hpc Hpre Habi) as (Hs & Hmem & Hret).
            right. exact (m_printf_ret 34 26 _ _ (or_intror (conj eq_refl eq_refl)) Hi' Hs Hmem Hret).
          + intros s Hs0.
            destruct (m_printf_at 34 s (or_intror eq_refl) Hs0) as (Hpc & Hpre & Habi).
            destruct (m_printf_step 34 s (or_intror eq_refl) (proj2 Hs0)) as (s' & Hne & Hs & Hmem & Hret).
            exists s'. split; [| exact Hne].
            exact (conj Hpc (conj Hpre (conj Habi (conj Hs (conj Hmem Hret))))).
          + intros s s' Hs0 (_ & _ & _ & Hs & Hmem & Hret).
            exact (m_printf_ret 34 26 s s' (or_intror (conj eq_refl eq_refl)) Hs0 Hs Hmem Hret).
          + exists j. split; [exact Hij |].
            left. exists 26%nat. split; [lia |]. split; [cbn [m_left]; lia | exact Hj].
Qed.

(* From a point of the call of tl_fib, the stage of main after the call: by
        induction on the instructions that are left, tl_fib is fair. *)
Lemma reach_ret m :
        forall i N p,
        mu N p = m ->
        in_call N p (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ m_stage 15 (sigma j).
Proof.
        induction m as [m IH] using lt_wf_ind. intros i N p Hm Hc.
        destruct Hfib as (_ & _ & _ & _ & (_ & Hnf) & (_ & Hwf)).
        destruct (leads_wf sigma _ (in_call N p)
                (fun s => (exists p', (mu N p' < mu N p)%nat /\ in_call N p' s) \/ m_stage 15 s)
                Hwf) with (i := i) as (j & Hij & [(p' & Hlt & Hc') | H15]); [ | | | exact Hc | | ].
        - intros i' Hi'. pose proof Hi' as (Hp & _).
          destruct (next_at sigma _ Hnf i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
          destruct (Hn (proj2 (in_fib_at_pc _) (call_pt_in N p _ Hp))) as [H1 | H2].
          + right. exact (in_call_step N p _ _ Hi' H1).
          + left. exact (in_call_tick N p _ _ Hi' H2).
        - intros s Hs. pose proof Hs as (Hp & Hf & _).
          destruct (call_step_enabled N p s Hf Hp) as (s' & H1 & Hne).
          exists s'. split; [| exact Hne].
          exact (conj (proj2 (in_fib_at_pc s) (call_pt_in N p s Hp)) H1).
        - intros s s' Hs (_ & H1). exact (in_call_step N p s s' Hs H1).
        - destruct (IH (mu N p') ltac:(lia) j N p' eq_refl Hc') as (j' & Hj' & H).
          exists j'. split; [lia | exact H].
        - exists j. exact (conj Hij H15).
Qed.

(* From a stage of main, the exit: by induction on the steps that are left. *)
Lemma reach_exit r :
        forall k i,
        m_left k = r ->
        (k < 36)%nat ->
        m_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ m_stage 35 (sigma j).
Proof.
        induction r as [r IH] using lt_wf_ind. intros k i Hr Hk Hst.
        destruct (Nat.eq_dec k 35) as [-> | Hne]; [exists i; split; [lia | exact Hst] |].
        destruct (reach_stage k i ltac:(lia) Hst)
                as (j & Hij & [(k' & Hk' & Hlt & Hst') | (-> & Hc)]).
        - destruct (IH (m_left k') ltac:(lia) k' j eq_refl Hk' Hst') as (j' & Hj' & H).
          exists j'. split; [lia | exact H].
        - destruct (reach_ret _ j _ _ eq_refl (enter_fib _ Hc)) as (j1 & Hj1 & H15).
          destruct (IH (m_left 15) ltac:(subst r; cbn [m_left]; lia) 15%nat j1 eq_refl ltac:(lia) H15)
                  as (j' & Hj' & H).
          exists j'. split; [lia | exact H].
Qed.

(* At the exit: there for good. *)
Lemma exit_stays j d :
        m_stage 35 (sigma j) ->
                sigma (j + d)%nat = sigma j.
Proof.
        intros Hst. destruct Hlibc as (_ & He & _).
        induction d as [| d IH]; [rewrite Nat.add_0_r; reflexivity |].
        rewrite Nat.add_succ_r.
        destruct (next_at sigma _ He (j + d)%nat) as [Hn | Heq]; [| rewrite <- Heq; exact IH].
        rewrite <- IH in Hst. destruct (m_exit_at _ Hst) as (Hpc & Habi).
        rewrite (Hn Hpc Habi). exact IH.
Qed.

End reach.

(* ========================================================================== *)
(* thm_7_termination                                                          *)
(* ========================================================================== *)

Theorem thm_7_termination :
        valid (impl_linked
                \impl <>[] \lift1 pc_at_exit).
Proof.
        intros sigma (Hfib & Hlibc & Hmain).
        destruct (reach_exit sigma Hfib Hlibc Hmain _ 0%nat 0%nat eq_refl ltac:(lia)
                (linked_first sigma Hfib Hmain)) as (j & _ & Hj).
        exists j. intros d. unfold Lift1, util_suffix. rewrite Nat.add_0_r.
        rewrite (exit_stays sigma Hlibc j d Hj).
        exact (proj1 (m_exit_at _ Hj)).
Qed.

(* ========================================================================== *)
(* thm_7_non_trivial_2                                                        *)
(* ========================================================================== *)

Theorem thm_7_non_trivial_2 :
        non_trivial spec_linked.
Proof.
        split.
        - (* by thm_4, from a run of the linked code *)
          destruct (stage_runs _ 0%nat s0 eq_refl ltac:(lia) s0_stage) as (f & H0 & Hn & Hend).
          assert (Hr : (\rmap (rm e_static) impl_linked) (fun n => rm e_static (f n))).
          { exists f. split; [apply stuttering_equivalent_refl | exact (run_impl f H0 Hn Hend)]. }
          destruct (turtle.compat.sail.riscv.examples.fib.thm_4_proof_x.thm_4 _ Hr) as (beh & _ & H).
          exists beh. exact H.
        - (* a first state with the PC at 0 *)
          exists (fun _ => ret_to 0 s0). intros (_ & _ & (_ & Hpc & _)).
          change (_pc_addr (ret_to 0 s0) = 0x10000) in Hpc.
          rewrite (reg_pc 0 _ (ret_to_pc 0 s0) ltac:(lia)) in Hpc. discriminate Hpc.
Qed.

(* ========================================================================== *)
(* The stages of main in the linked spec: no code of tl_fib                   *)
(* ========================================================================== *)

Module NoCode <: CODE.

Definition code (s : state) : Prop :=
        True.

Lemma code_mem s s' :
        st_mem s' = st_mem s ->
        code s ->
                code s'.
Proof.
        intros _ _. exact I.
Qed.

Lemma code_kept s s' :
        mem_kept 0x3ffffffff0 0x3ffffffff8 s s' ->
        code s ->
                code s'.
Proof.
        intros _ _. exact I.
Qed.

End NoCode.

Module Stages_spec := Stages NoCode.

(* ========================================================================== *)
(* Steps and fairness, of a behaviour of any state                            *)
(* ========================================================================== *)

(* `next_at`, `wf_at` and `leads_wf` of tla.v, for the states of the spec of
        tl_fib. *)
(* ========================================================================== *)
(* The call of tl_fib in the linked spec                                      *)
(* ========================================================================== *)

(* A state of the spec of tl_fib in the call from main: at the label or
        internal, with what main needs after the call. *)
Definition sp_in (gs : state * spec_tla.state) : Prop :=
        at_label_eq e_static (fst gs) (snd gs)
        /\ (at_label_tla e_static (snd gs) \/ at_internal_tla (snd gs))
        /\ precond (fst gs)
        /\ Stages_spec.prog (fst gs)
        /\ reg T.x2 0x3ffffffff0 (fst gs)
        /\ abi_ra (fst gs) = 0x1003c.

(* The return of the spec, its fair step. *)
Definition sp_ret (gs gs' : state * spec_tla.state) : Prop :=
        (at_label_tla e_static (snd gs) \/ at_internal_tla (snd gs))
        /\ precond (fst gs)
        /\ spec_tla._internal (snd gs') = false
        /\ stepcond (fst gs) (fst gs')
        /\ res_eq (fst gs') (snd gs').

(* The call: a state of `sp_in`. *)
Lemma sp_in_call gs :
        Stages_spec.m_call (fst gs) ->
        at_label_eq e_static (fst gs) (snd gs) ->
                sp_in gs.
Proof.
        intros (Hp & Hpc & X2 & X1) Heq.
        split; [exact Heq |].
        split; [left; apply (proj1 Heq); unfold at_label_asm; rewrite (reg_pc _ _ Hpc ltac:(lia)); reflexivity |].
        split; [unfold precond, abi_precond, abi_sp; rewrite (reg_abi _ _ _ X2 ltac:(lia)); reflexivity |].
        split; [exact Hp |]. split; [exact X2 |].
        exact (reg_abi _ _ _ X1 ltac:(lia)).
Qed.

(* An internal step: still in the call. *)
Lemma sp_in_internal gs gs' :
        sp_in gs ->
        at_label_eq e_static (fst gs') (snd gs') ->
        spec_tla._internal (snd gs') = true ->
        stepcond_internal (fst gs) (fst gs') ->
                sp_in gs'.
Proof.
        intros (_ & _ & _ & Hp & X2 & Hra) Heq Hinner ((Hreg & Hconf) & Hmem & Hra').
        pose proof Hp as (Hi & _).
        assert (X2' : reg T.x2 0x3ffffffff0 (fst gs')) by exact (reg_preserved T.x2 _ _ _ Hreg eq_refl X2).
        split; [exact Heq |].
        split; [right; exact Hinner |].
        split; [unfold precond, abi_precond, abi_sp; rewrite (reg_abi _ _ _ X2' ltac:(lia)); reflexivity |].
        split; [exact (Stages_spec.prog_mem _ _ (eq_sym Hmem) (conf_keep _ _ Hconf Hi) Hp) |].
        split; [exact X2' |].
        rewrite Hra'. exact Hra.
Qed.

(* The return: the stage of main after the call. *)
Lemma sp_in_ret gs s' :
        sp_in gs ->
        stepcond (fst gs) s' ->
                Stages_spec.m_stage 15 s'.
Proof.
        intros (_ & _ & _ & Hp & X2 & Hra) ((Hreg & Hconf) & Hmem & Hret).
        pose proof Hp as (Hi & _).
        split; [exact (Stages_spec.prog_mem _ _ (eq_sym Hmem) (conf_keep _ _ Hconf Hi) Hp) |].
        split; [| exact (reg_preserved T.x2 _ _ _ Hreg eq_refl X2)].
        apply pc_reg. unfold abi_opt_stepcond_return in Hret. rewrite Hret, Hra. reflexivity.
Qed.

(* In the call, the return is enabled: to the return address, with any
        result. *)
Lemma sp_ret_enabled gs :
        sp_in gs ->
                exists gs',
                sp_ret gs gs'
                /\ gs <> gs'.
Proof.
        intros (Heq & Hat & Hpre & _ & _ & Hra).
        exists (ret_to 0x1003c (fst gs),
                spec_tla.Build_state false (spec_tla._op (snd gs)) (spec_tla.arg0 (snd gs))
                        (abi_res0 (ret_to 0x1003c (fst gs)))).
        split.
        - split; [exact Hat |]. split; [exact Hpre |]. split; [reflexivity |].
          split; [exact (ret_to_abi 0x1003c (fst gs) ltac:(lia) Hra) |].
          unfold res_eq. cbn [fst snd spec_tla.res0]. symmetry.
          apply definitions.bv_wrap_small. unfold abi_res0, abi_a0. exact (abi_range T.x10 _).
        - intros E.
          pose proof (f_equal (fun g : state * spec_tla.state => spec_tla._internal (snd g)) E) as Ei.
          pose proof (f_equal (fun g : state * spec_tla.state => _pc_addr (fst g)) E) as Ep.
          cbn [fst snd spec_tla._internal] in Ei, Ep.
          rewrite (reg_pc _ _ (ret_to_pc 0x1003c (fst gs)) ltac:(lia)) in Ep.
          destruct Hat as [Hl | Hi].
          + apply (proj2 Heq) in Hl. unfold at_label_asm in Hl. rewrite Ep in Hl.
            change (e_static "tl_fib"%string) with 0x11000 in Hl. lia.
          + unfold at_internal_tla in Hi. rewrite Ei in Hi. discriminate Hi.
Qed.

(* From the call of tl_fib, in a behaviour of its spec: the stage of main
        after the call, the spec is fair. *)
Lemma spec_returns sigma i :
        tl_fib_spec e_static sigma ->
        Stages_spec.m_call (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ Stages_spec.m_stage 15 (sigma j).
Proof.
        intros (tau & (f & g & Mf & Mg & Sf & Sg & Hfg) & _ & Hinv & Hnext & Hwf) Hc.
        assert (Hfst : forall n, fst (tau (f n)) = sigma (g n)) by exact Hfg.
        assert (Hlab : forall m, at_label_eq e_static (fst (tau m)) (snd (tau m))).
        { intros m. specialize (Hinv m). unfold Lift1, util_suffix in Hinv.
          rewrite Nat.add_0_r in Hinv. exact (proj1 Hinv). }
        destruct (Sg i) as (n0 & Hn0).
        destruct (leads_wf tau sp_ret sp_in (fun gs => Stages_spec.m_stage 15 (fst gs)) Hwf)
                with (i := f n0) as (m & Hm & Hst).
        - (* a step stays in the call, or returns *)
          intros m' Hin.
          destruct (next_at tau _ Hnext m') as [Hs | Heq]; [| left; rewrite <- Heq; exact Hin].
          pose proof Hin as (_ & Hat & Hpre & _).
          destruct (Hs Hat Hpre) as [(_ & Hsc & _) | (Hinner & Hsi)].
          + right. exact (sp_in_ret _ _ Hin Hsc).
          + left. exact (sp_in_internal _ _ Hin (Hlab (S m')) Hinner Hsi).
        - exact sp_ret_enabled.
        - intros gs gs' Hin (_ & _ & _ & Hsc & _). exact (sp_in_ret _ _ Hin Hsc).
        - apply sp_in_call; [rewrite Hfst, Hn0; exact Hc | exact (Hlab (f n0))].
        - (* to `sigma` again *)
          destruct (Sf m) as (n1 & Hn1).
          destruct (Nat.le_gt_cases n0 n1) as [Hle | Hlt].
          + exists (g n1). split; [rewrite <- Hn0; exact (util_monotone_le g Mg n0 n1 Hle) |].
            rewrite <- Hfst, Hn1. exact Hst.
          + exists i. split; [lia |].
            pose proof (util_monotone_le f Mf n1 n0 ltac:(lia)) as Hle.
            assert (E : m = f n0) by lia.
            rewrite <- Hn0, <- Hfst, <- E. exact Hst.
Qed.

(* ========================================================================== *)
(* Every behaviour of the linked spec reaches the exit                        *)
(* ========================================================================== *)

Section reach_spec.

Variable sigma : behavior state.
Hypothesis Hspec : tl_fib_spec e_static sigma.
Hypothesis Hlibc : unsafe_libc e_static sigma.
Hypothesis Hmain : exec_static main_s sigma.

Lemma spec_first :
        Stages_spec.m_stage 0 (sigma 0%nat).
Proof.
        destruct Hmain as (I1 & I2 & I4 & Is & _).
        destruct Is as ((_ & Ism) & Isf).
        split; [exact (conj I1 (conj Ism (conj Isf I))) |].
        split; [exact (pc_reg _ _ I2) | exact (reg_sp _ I4)].
Qed.

(* From an instruction of main: its step is taken, main is fair. *)
Lemma spec_instr k i :
        (k < 32)%nat ->
        Stages_spec.m_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ Stages_spec.m_after k (sigma j).
Proof.
        intros Hk Hst.
        destruct Hmain as (_ & _ & _ & _ & ((_ & Hnm) & _) & ((_ & Hwm) & _)).
        apply (leads_wf sigma _ (Stages_spec.m_stage k) (Stages_spec.m_after k) Hwm); [ | | | exact Hst].
        - intros i' Hi'.
          destruct (next_at sigma _ Hnm i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
          destruct (Hn (Stages_spec.m_stage_at k _ Hk Hi')) as [H1 | H2].
          + right. exact (proj2 (proj1 (step_tla _ _ (Stages_spec.main_step k _ Hk Hi')) _ H1)).
          + left. exact (Stages_spec.m_tick k _ _ Hi' (tick_tla _ _ H2)).
        - intros s Hs.
          destruct (proj2 (step_tla s _ (Stages_spec.main_step k s Hk Hs))) as (s' & H1 & Hne & _).
          exists s'. split; [exact (conj (Stages_spec.m_stage_at k s Hk Hs) H1) |].
          intros Heq. apply Hne. rewrite Heq. reflexivity.
        - intros s s' Hs (_ & H1).
          exact (proj2 (proj1 (step_tla s _ (Stages_spec.main_step k s Hk Hs)) s' H1)).
Qed.

(* From a stage but the exit: an instruction as above, a call of the libc
        returns, the libc is fair. *)
Lemma spec_stage k i :
        (k < 35)%nat ->
        Stages_spec.m_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ Stages_spec.m_after k (sigma j).
Proof.
        intros Hk Hst.
        destruct (Nat.lt_ge_cases k 32) as [Hk32 | Hk32]; [exact (spec_instr k i Hk32 Hst) |].
        assert (Hl : k = 32%nat \/ k = 33%nat \/ k = 34%nat) by lia.
        destruct Hlibc as ((Hp & Hwp) & _ & (Hgr & Hwg)).
        destruct Hl as [-> | [-> | ->]].
        - (* getrandom *)
          destruct (leads_wf sigma _ (Stages_spec.m_stage 32) (Stages_spec.m_stage 6) Hwg) with (i := i)
                  as (j & Hij & Hj); [ | | | exact Hst | ].
          + intros i' Hi'.
            destruct (next_at sigma _ Hgr i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
            destruct (Stages_spec.m_getrandom_at _ Hi') as (Hpc & Hpre & Habi).
            destruct (Hn Hpc Hpre Habi) as (Hgs & Hs & Hret).
            right. exact (Stages_spec.m_getrandom_ret _ _ Hi' Hgs Hs Hret).
          + intros s Hs0.
            destruct (Stages_spec.m_getrandom_at s Hs0) as (Hpc & Hpre & Habi).
            destruct (m_getrandom_step s (proj2 Hs0)) as (s' & Hne & Hgs & Hs & Hret).
            exists s'. split; [| exact Hne].
            exact (conj Hpc (conj Hpre (conj Habi (conj Hgs (conj Hs Hret))))).
          + intros s s' Hs0 (_ & _ & _ & Hgs & Hs & Hret).
            exact (Stages_spec.m_getrandom_ret s s' Hs0 Hgs Hs Hret).
          + exists j. split; [exact Hij |].
            left. exists 6%nat. split; [lia |]. split; [cbn [m_left]; lia | exact Hj].
        - (* printf, first call *)
          destruct (leads_wf sigma _ (Stages_spec.m_stage 33) (Stages_spec.m_stage 21) Hwp) with (i := i)
                  as (j & Hij & Hj); [ | | | exact Hst | ].
          + intros i' Hi'.
            destruct (next_at sigma _ Hp i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
            destruct (Stages_spec.m_printf_at 33 _ (or_introl eq_refl) Hi') as (Hpc & Hpre & Habi).
            destruct (Hn Hpc Hpre Habi) as (Hs & Hmem & Hret).
            right. exact (Stages_spec.m_printf_ret 33 21 _ _ (or_introl (conj eq_refl eq_refl)) Hi' Hs Hmem Hret).
          + intros s Hs0.
            destruct (Stages_spec.m_printf_at 33 s (or_introl eq_refl) Hs0) as (Hpc & Hpre & Habi).
            destruct (m_printf_step 33 s (or_introl eq_refl) (proj2 Hs0)) as (s' & Hne & Hs & Hmem & Hret).
            exists s'. split; [| exact Hne].
            exact (conj Hpc (conj Hpre (conj Habi (conj Hs (conj Hmem Hret))))).
          + intros s s' Hs0 (_ & _ & _ & Hs & Hmem & Hret).
            exact (Stages_spec.m_printf_ret 33 21 s s' (or_introl (conj eq_refl eq_refl)) Hs0 Hs Hmem Hret).
          + exists j. split; [exact Hij |].
            left. exists 21%nat. split; [lia |]. split; [cbn [m_left]; lia | exact Hj].
        - (* printf, second call *)
          destruct (leads_wf sigma _ (Stages_spec.m_stage 34) (Stages_spec.m_stage 26) Hwp) with (i := i)
                  as (j & Hij & Hj); [ | | | exact Hst | ].
          + intros i' Hi'.
            destruct (next_at sigma _ Hp i') as [Hn | Heq]; [| left; rewrite <- Heq; exact Hi'].
            destruct (Stages_spec.m_printf_at 34 _ (or_intror eq_refl) Hi') as (Hpc & Hpre & Habi).
            destruct (Hn Hpc Hpre Habi) as (Hs & Hmem & Hret).
            right. exact (Stages_spec.m_printf_ret 34 26 _ _ (or_intror (conj eq_refl eq_refl)) Hi' Hs Hmem Hret).
          + intros s Hs0.
            destruct (Stages_spec.m_printf_at 34 s (or_intror eq_refl) Hs0) as (Hpc & Hpre & Habi).
            destruct (m_printf_step 34 s (or_intror eq_refl) (proj2 Hs0)) as (s' & Hne & Hs & Hmem & Hret).
            exists s'. split; [| exact Hne].
            exact (conj Hpc (conj Hpre (conj Habi (conj Hs (conj Hmem Hret))))).
          + intros s s' Hs0 (_ & _ & _ & Hs & Hmem & Hret).
            exact (Stages_spec.m_printf_ret 34 26 s s' (or_intror (conj eq_refl eq_refl)) Hs0 Hs Hmem Hret).
          + exists j. split; [exact Hij |].
            left. exists 26%nat. split; [lia |]. split; [cbn [m_left]; lia | exact Hj].
Qed.

(* From a stage of main, the exit: by induction on the steps that are left,
        the call of tl_fib returns by its spec. *)
Lemma spec_exit r :
        forall k i,
        m_left k = r ->
        (k < 36)%nat ->
        Stages_spec.m_stage k (sigma i) ->
                exists j,
                (i <= j)%nat
                /\ Stages_spec.m_stage 35 (sigma j).
Proof.
        induction r as [r IH] using lt_wf_ind. intros k i Hr Hk Hst.
        destruct (Nat.eq_dec k 35) as [-> | Hne]; [exists i; split; [lia | exact Hst] |].
        destruct (spec_stage k i ltac:(lia) Hst)
                as (j & Hij & [(k' & Hk' & Hlt & Hst') | (-> & Hc)]).
        - destruct (IH (m_left k') ltac:(lia) k' j eq_refl Hk' Hst') as (j' & Hj' & H).
          exists j'. split; [lia | exact H].
        - destruct (spec_returns sigma j Hspec Hc) as (j1 & Hj1 & H15).
          destruct (IH (m_left 15) ltac:(subst r; cbn [m_left]; lia) 15%nat j1 eq_refl ltac:(lia) H15)
                  as (j' & Hj' & H).
          exists j'. split; [lia | exact H].
Qed.

(* At the exit: there for good. *)
Lemma spec_exit_stays j d :
        Stages_spec.m_stage 35 (sigma j) ->
                sigma (j + d)%nat = sigma j.
Proof.
        intros Hst. destruct Hlibc as (_ & He & _).
        induction d as [| d IH]; [rewrite Nat.add_0_r; reflexivity |].
        rewrite Nat.add_succ_r.
        destruct (next_at sigma _ He (j + d)%nat) as [Hn | Heq]; [| rewrite <- Heq; exact IH].
        rewrite <- IH in Hst. destruct (Stages_spec.m_exit_at _ Hst) as (Hpc & Habi).
        rewrite (Hn Hpc Habi). exact IH.
Qed.

End reach_spec.

(* ========================================================================== *)
(* thm_7_termination_2                                                        *)
(* ========================================================================== *)

Theorem thm_7_termination_2 :
        valid (spec_linked
                \impl <>[] \lift1 pc_at_exit).
Proof.
        intros sigma (Hspec & Hlibc & Hmain).
        destruct (spec_exit sigma Hspec Hlibc Hmain _ 0%nat 0%nat eq_refl ltac:(lia)
                (spec_first sigma Hmain)) as (j & _ & Hj).
        exists j. intros d. unfold Lift1, util_suffix. rewrite Nat.add_0_r.
        rewrite (spec_exit_stays sigma Hlibc j d Hj).
        exact (proj1 (Stages_spec.m_exit_at _ Hj)).
Qed.

(* The statements of thm_7_non_trivial.v. *)
Definition thm_7_non_trivial_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_7_non_trivial.thm_7_non_trivial in exact t) :=
        thm_7_non_trivial.

Definition thm_7_non_trivial_2_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_7_non_trivial.thm_7_non_trivial_2 in exact t) :=
        thm_7_non_trivial_2.

Definition thm_7_termination_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_7_non_trivial.thm_7_termination in exact t) :=
        thm_7_termination.

Definition thm_7_termination_2_check :
        ltac:(let t := type of turtle.compat.sail.riscv.examples.fib.thm_7_non_trivial.thm_7_termination_2 in exact t) :=
        thm_7_termination_2.

Print Assumptions thm_7_non_trivial.
Print Assumptions thm_7_non_trivial_2.
Print Assumptions thm_7_termination.
Print Assumptions thm_7_termination_2.
