(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* ev.v                                                                       *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require SailStdpp.Operators_mwords.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.gen.eval.
Require turtle.gen.bits.

#[local] Open Scope Z_scope.

(* ========================================================================== *)
(* Words                                                                      *)
(* ========================================================================== *)

Lemma and_vec_zero_r (x : Values.mword 64) :
        Operators_mwords.and_vec x (Values.mword_of_int 0) = Values.mword_of_int 0.
Proof.
        apply definitions.bv_eq.
        change (Operators_mwords.and_vec x (Values.mword_of_int 0))
                with (definitions.bv_and x (Values.mword_of_int (len := 64) 0)).
        rewrite definitions.bv_and_unsigned.
        change (definitions.bv_unsigned (Values.mword_of_int (len := 64) 0)) with 0.
        rewrite Z.land_0_r. reflexivity.
Qed.

Lemma and_vec_zero_l (x : Values.mword 64) :
        Operators_mwords.and_vec (Values.mword_of_int 0) x = Values.mword_of_int (len := 64) 0.
Proof.
        apply definitions.bv_eq.
        change (Operators_mwords.and_vec (Values.mword_of_int 0) x)
                with (definitions.bv_and (Values.mword_of_int (len := 64) 0) x).
        rewrite definitions.bv_and_unsigned.
        change (definitions.bv_unsigned (Values.mword_of_int (len := 64) 0)) with 0.
        rewrite Z.land_0_l. reflexivity.
Qed.

(* ========================================================================== *)
(* ev                                                                         *)
(* ========================================================================== *)

(* `ev` runs the computation of a goal `outcome m s ?r`: it follows the binds,
        takes the value of a register from a hypothesis
        `register_lookup r (st_regs s) = v` when there is one, decides a condition
        that has no unknown in it by evaluation, and unfolds the functions of
        the model. It stops where it cannot go on, and leaves that goal and
        the goals of the parts that wait for its result. *)

Ltac head_of t :=
        lazymatch t with
                | ?f _ => head_of f
                | _    => t
                end.

(* `c` mentions no hypothesis. *)
Ltac is_closed c :=
        let T := type of c in
        assert_succeeds (
                let H := fresh in
                assert (H : T)
                        by (repeat match goal with X : _ |- _ => clear X end; exact c)).

(* Called with a register that no hypothesis gives, with a condition of which
        both branches are run, and with every computation: to print them. *)
Ltac ev_trace_unknown r := idtac.
Ltac ev_trace_any c := idtac.
Ltac ev_trace m := idtac.

(* A state taken apart: a lookup through writes computes only when the state
        under them is the constructors. The proofs that use `ev` begin with
        it. *)
Ltac ev_base s :=
        let rs := fresh "rs" in
        destruct s as [rs ?]; destruct rs.

(* Called on a state that is not a write, with the register that is looked
        up: the caller's other states that a lookup passes. *)
Ltac ev_strip_other r s k := fail.

(* The state under the writes of `s` to other registers than `r`, given to `k`. *)
Ltac ev_strip r s k :=
        lazymatch s with
                | set_reg ?r' _ ?s' =>
                        tryif constr_eq r r' then k s else ev_strip r s' k
                | _ => first [ ev_strip_other r s k | k s ]
                end.

Lemma lookup_if_same r (c : bool) (a b : state) v :
        rv64d_types.register_lookup r (st_regs a) = v ->
        rv64d_types.register_lookup r (st_regs b) = v ->
                rv64d_types.register_lookup r (st_regs (if c then a else b)) = v.
Proof.
        intros Ha Hb. destruct c; assumption.
Qed.

Lemma lookup_if_vals r (c : bool) (a b : state) va vb :
        rv64d_types.register_lookup r (st_regs a) = va ->
        rv64d_types.register_lookup r (st_regs b) = vb ->
                rv64d_types.register_lookup r (st_regs (if c then a else b)) = if c then va else vb.
Proof.
        intros Ha Hb. destruct c; assumption.
Qed.

Lemma lookup_set_past r r' w (s : state) v :
        rv64d_types.register_beq r r' = false ->
        rv64d_types.register_lookup r (st_regs s) = v ->
                rv64d_types.register_lookup r (st_regs (set_reg r' w s)) = v.
Proof.
        intros H <-. apply lookup_set_other. exact H.
Qed.

Lemma mem_set_past r w (s : state) m :
        st_mem s = m ->
                st_mem (set_reg r w s) = m.
Proof.
        intros <-. reflexivity.
Qed.

Lemma mem_if_same (c : bool) (a b : state) m :
        st_mem a = m ->
        st_mem b = m ->
                st_mem (if c then a else b) = m.
Proof.
        intros Ha Hb. destruct c; assumption.
Qed.

(* The writes of `s` are over a condition: a lookup there does not compute. *)
Ltac state_has_if s :=
        lazymatch s with
                | set_reg _ _ ?s' => state_has_if s'
                | if _ then _ else _ => idtac
                | _ => fail
                end.

(* The value of a register in the state of the goal: the value of the last
        write to it, or what a hypothesis says of the state under the writes,
        or the lookup there. Where the writes are over a condition: by the
        lemmas of the writes and of the condition. Otherwise the equation holds
        by computation; the kernel checks it at `Qed`. *)
Ltac ev_lookup :=
        lazymatch goal with
                | |- rv64d_types.register_lookup ?r (st_regs ?s) = ?e =>
                        tryif state_has_if s then ev_lookup_slow else ev_lookup_fast r s e
                end
with ev_lookup_slow :=
        lazymatch goal with
                | |- rv64d_types.register_lookup ?r (st_regs (set_reg ?r' ?v ?s)) = _ =>
                        tryif constr_eq r r'
                        then apply (lookup_set_same r v s)
                        else (apply lookup_set_past; [ reflexivity | ev_lookup ])
                | |- rv64d_types.register_lookup ?r (st_regs (if ?c then ?a else ?b)) = _ =>
                        first
                                [ eapply lookup_if_same; [ ev_lookup | ev_lookup ]
                                | eapply lookup_if_vals; [ ev_lookup | ev_lookup ] ]
                end
with ev_lookup_fast r s e :=
        ev_strip r s ltac:(fun s' =>
                lazymatch s' with
                        | set_reg _ ?v _ =>
                                let T := type of v in
                                unify e v;
                                exact_no_check (eq_refl (A := T) v)
                        | _ =>
                                first
                                        [ lazymatch goal with
                                                | H : rv64d_types.register_lookup r (st_regs s') = ?c |- _ =>
                                                        unify e c;
                                                        exact_no_check H
                                                end
                                        | ev_trace_unknown r;
                                          let v := constr:(rv64d_types.register_lookup r (st_regs s')) in
                                          let T := type of v in
                                          unify e v;
                                          exact_no_check (eq_refl (A := T) v) ]
                        end).

(* The memory of a state: that of the state under its writes and conditions. *)
Ltac ev_mem_of :=
        lazymatch goal with
                | |- st_mem (set_reg _ _ _) = _ =>
                        apply mem_set_past; ev_mem_of
                | |- st_mem (if ?c then ?a else ?b) = _ =>
                        eapply mem_if_same; [ ev_mem_of | ev_mem_of ]
                | |- _ =>
                        reflexivity
                end.

(* The functions `ev` does not unfold: the caller's lemmas. *)
Ltac ev_special := fail.

(* Called where a condition with an unknown in it does not compute: the
        alignment checks, unfolded to their `Z.rem`. A caller adds its own
        steps with `::=`. *)
Ltac ev_extra :=
        progress (try unfold rv64d.is_aligned_paddr; try unfold rv64d.is_aligned_vaddr);
        cbv beta iota.

(* `H : t = v`: `t` becomes `v` where it occurs in the goal as it is, found by
        syntax, not by unification. *)
Ltac ev_replace H :=
        lazymatch type of H with
                | ?t = ?v =>
                        let T := type of t in
                        lazymatch goal with
                                | |- context C [t] =>
                                        let f := constr:(fun x : T =>
                                                ltac:(let g := context C [x] in exact g)) in
                                        refine (eq_ind v f _ t (eq_sym H));
                                        cbv beta
                                end
                end.

(* A boolean `if` on an unknown whose two branches are known and equal: the
        value of the branches. *)
Ltac ev_if_same :=
        match goal with
                | |- context C [if ?c then ?a else ?b] =>
                        lazymatch type of a with bool => idtac end;
                        is_closed a; is_closed b;
                        let va := eval vm_compute in a in
                        let vb := eval vm_compute in b in
                        constr_eq va vb;
                        let t := constr:(if c then a else b) in
                        let E := fresh "E" in
                        assert (E : t = va) by (destruct c; vm_compute; reflexivity);
                        let f := constr:(fun x : bool =>
                                ltac:(let g := context C [x] in exact g)) in
                        refine (eq_ind va f _ t (eq_sym E));
                        cbv beta; clear E
                end.

(* Called where a condition has an unknown in it: the facts of the conf
        (no interrupt is enabled, SXLEN and UXLEN, no translation, PMP entry
        0), then `ev_if_same`. A caller adds its own rewrites with `::=`. *)
Ltac ev_stuck :=
        match goal with
                | H : rv64d._get_Mstatus_SXL _ = _ |- _ =>
                        ev_replace H
                | H : rv64d._get_Mstatus_MPRV _ = _ |- _ =>
                        ev_replace H
                | |- context [rv64d._get_SEnvcfg_PMM (rv64d._update_SEnvcfg_SSE ?v ?x)] =>
                        ev_replace (bits.senvcfg_pmm_update_sse v x)
                | H : rv64d._get_SEnvcfg_PMM _ = _ |- _ =>
                        ev_replace H
                | H : rv64d._get_Mstatus_UXL _ = _ |- _ =>
                        ev_replace H
                | |- context [rv64d.Mk_Satp64 _] =>
                        unfold rv64d.Mk_Satp64
                | H : rv64d._get_Satp64_Mode _ = _ |- _ =>
                        ev_replace H
                | H : Values.vec_access_dec _ 0 = _ |- _ =>
                        ev_replace H
                | |- context [Operators_mwords.and_vec ?x (Values.mword_of_int 0)] =>
                        ev_replace (and_vec_zero_r x)
                | |- context [Operators_mwords.and_vec (Values.mword_of_int 0) ?x] =>
                        ev_replace (and_vec_zero_l x)
                | |- _ =>
                        ev_if_same
                end.

(* A computation that has no unknown in it and does not look at the state:
        evaluated at once. *)
Ltac ev_pure :=
        lazymatch goal with
                | |- outcome ?m _ _ =>
                        is_closed m;
                        let v := eval vm_compute in m in
                        lazymatch v with
                                | I.Ret ?a =>
                                        (replace m with (I.Ret a) by (vm_compute; reflexivity));
                                        apply outcome_ret
                                end
                end.

(* The bytes of memory that the state of the goal has, from a hypothesis
        `_mem_read (st_mem s) b n = w` at the same address, of a state with the
        same memory. *)
Ltac ev_mem :=
        match goal with
                | |- _mem_read (st_mem ?st) _ _ = _ =>
                        state_has_if st;
                        let Hm := fresh "Hm" in
                        eassert (Hm : st_mem st = _) by ev_mem_of;
                        rewrite Hm; clear Hm; ev_mem
                | |- _mem_read ?m ?a ?n = _ =>
                        let a' := eval vm_compute in (definitions.bv_unsigned a) in
                        let n' := eval vm_compute in n in
                        match goal with
                                | H : _mem_read _ ?b ?n2 = _ |- _ =>
                                        let n2' := eval vm_compute in n2 in
                                        constr_eq n' n2';
                                        let b' := eval vm_compute in (definitions.bv_unsigned b) in
                                        constr_eq a' b';
                                        (replace a with b by (vm_compute; reflexivity));
                                        (replace n with n2 by (vm_compute; reflexivity));
                                        exact H
                                end
                end.

(* `c = true` or `c = false`, by evaluation. *)
Ltac ev_decide :=
        lazymatch goal with
                | |- ?c = _ =>
                        first
                                [ is_closed c; vm_compute; reflexivity
                                | reflexivity ]
                end.

(* Two results of the branches of a condition, as one. *)
Ltac if_simpl c a b :=
        match goal with
                | _ =>
                        let _ := match goal with _ => constr_eq a b end in
                        constr:(a)
                | _ =>
                        let _ := match goal with _ => unify a b end in
                        constr:(a)
                | _ =>
                        constr:(if c then a else b)
                end.

Ltac res_join :=
        lazymatch goal with
                | |- ?l = _ =>
                        lazymatch l with
                                | if ?c then res_val ?a1 ?s1 else res_val ?a2 ?s2 =>
                                        let a := if_simpl c a1 a2 in
                                        let s := if_simpl c s1 s2 in
                                        let T := type of l in
                                        transitivity (res_val a s : T);
                                                [ destruct c; reflexivity | reflexivity ]
                                | if ?c then ?x else ?x =>
                                        apply if_same
                                | _ =>
                                        reflexivity
                                end
                end.

Ltac ev :=
        lazymatch goal with
                (* a part that waits for the result of the one before *)
                | |- match ?r with res_val _ _ => _ | res_exn _ _ => _ | res_stop => _ end =>
                        tryif is_evar r then idtac
                        else (cbv beta iota delta [lift_res catch_res];
                                lazymatch goal with
                                        | |- _ = _ => reflexivity
                                        | |- outcome _ _ _ => ev
                                        | _ => idtac
                                        end)
                | |- outcome ?m _ _ => ev_out m
                | _ => idtac
                end
with ev_out m :=
        ev_trace m;
        lazymatch m with
                (* a memory access with its continuation, which ignores the tag
                        or the answer of the access *)
                | D.bind (D.sail_mem_read _) _ =>
                        let m' := eval hnf in m in
                        change m with m'; ev
                | D.bind (D.sail_mem_write _) _ =>
                        let m' := eval hnf in m in
                        change m with m'; ev
                | D.bind _ _ =>
                        eapply outcome_bind; [ ev | ev ]
                | I.iMon_bind _ _ =>
                        eapply outcome_bind; [ ev | ev ]
                | D.bind0 _ _ =>
                        unfold D.bind0 at 1; ev
                | D.and_boolM _ _ =>
                        unfold D.and_boolM at 1; ev
                | D.or_boolM _ _ =>
                        unfold D.or_boolM at 1; ev
                | D.returnm _ =>
                        apply outcome_ret
                | rv64d_types.returnM _ =>
                        apply outcome_ret
                | rv64d_types.returnR _ _ =>
                        apply outcome_ret
                | I.Ret _ =>
                        apply outcome_ret
                | D.read_reg ?r =>
                        eapply (outcome_read_reg r); ev_lookup
                | I.Next (I.RegRead ?r ?o) ?k =>
                        eapply (outcome_next_read r o k); [ ev_lookup | cbv beta; ev ]
                | I.Next (I.RegWrite ?r ?o ?v) ?k =>
                        apply (outcome_next_write r o v k); cbv beta; ev
                | I.Next (I.MemRead ?n ?rr) ?k =>
                        first
                                [ eapply (outcome_mem_read n rr k); [ ev_mem | intros ?; cbv beta; ev ]
                                | idtac ]
                | I.Next (I.MemWrite ?n ?wr) ?k =>
                        apply (outcome_mem_write n wr k); intros ?; cbv beta; ev
                | I.Next (I.Choose ?ty) ?k =>
                        apply (outcome_choose ty k)
                | D.write_reg ?r ?v =>
                        apply (outcome_write_reg r v)
                | D.liftR _ =>
                        eapply outcome_liftR; ev
                | D.catch_early_return _ =>
                        eapply outcome_catch_early_return; ev
                | D.early_return _ =>
                        apply outcome_early_return
                | D.throw _ =>
                        apply outcome_throw
                | D.fail _ =>
                        apply outcome_fail
                | D.exit _ =>
                        apply outcome_fail
                | D.assert_exp ?c _ =>
                        first
                                [ apply outcome_assert_true; ev_decide
                                | idtac ]
                | D.assert_exp' _ _ =>
                        first
                                [ apply outcome_assert_exp'
                                | idtac ]
                | D.untilMT ?vars ?measure ?cond ?body =>
                        let H := fresh in
                        destruct (untilMT_round vars measure cond body
                                ltac:(vm_compute; discriminate)) as [? H];
                        rewrite H; clear H; cbv beta; ev
                | D.foreach_ZM_up _ _ _ _ _ =>
                        unfold D.foreach_ZM_up at 1; ev
                | D.foreach_ZM_up' ?from ?to _ ?n _ _ =>
                        let c := eval vm_compute in (from <=? to) in
                        lazymatch c with
                                | true =>
                                        let n' := eval vm_compute in n in
                                        (replace n with n' by (vm_compute; reflexivity));
                                        rewrite foreach_ZM_up'_round by (vm_compute; reflexivity);
                                        ev
                                | false =>
                                        rewrite foreach_ZM_up'_end by (vm_compute; reflexivity);
                                        ev
                                end
                (* long tables of names *)
                | rv64d.csr_name_map_backwards _ =>
                        first [ ev_pure | ev_unfold m ]
                | rv64d.csr_name_map_forwards _ =>
                        first [ ev_pure | ev_unfold m ]
                | rv64d.reg_name_forwards _ =>
                        first [ ev_pure | ev_unfold m ]
                (* recursions on `Acc`: `cbn` reduces them, in the computation
                        alone: the states of the goal stay as they are *)
                | rv64d.currentlyEnabled _ =>
                        let m' := eval cbn in m in
                        change m with m'; ev
                | rv64d.hartSupports _ =>
                        let m' := eval cbn in m in
                        change m with m'; ev
                | (if ?c then _ else _) =>
                        ev_if c
                | (match ?x with _ => _ end) =>
                        ev_match x
                | (let _ := _ in _) =>
                        cbv zeta; ev
                | _ =>
                        first
                                [ ev_special
                                | ev_unfold m ]
                end
with ev_if c :=
        let T := type of c in
        lazymatch T with
                | bool =>
                        let v := match goal with
                                | _ =>
                                        let _ := match goal with _ => is_closed c end in
                                        eval vm_compute in c
                                | _ => eval hnf in c
                                end in
                        lazymatch v with
                                | true  => eapply outcome_if_true; [ ev_decide | ev ]
                                | false => eapply outcome_if_false; [ ev_decide | ev ]
                                | _     =>
                                        first
                                                [ progress ev_extra; ev
                                                | progress ev_stuck; ev
                                                | ev_trace_any c;
                                                  eapply outcome_conv;
                                                        [ eapply outcome_if_any; [ solve [ ev ] | solve [ ev ] ]
                                                        | res_join ]
                                                | idtac ]
                                end
                | _ => ev_match c
                end
with ev_match x :=
        let h := head_of x in
        tryif is_constructor h then (cbv beta iota; ev)
        else tryif is_closed x then (
                let v := eval vm_compute in x in
                let hv := head_of v in
                tryif is_constructor hv then (
                        (replace x with v by (vm_compute; reflexivity));
                        cbv beta iota; ev)
                else first [ progress ev_extra; ev | idtac ])
        else first
                [ progress ev_stuck; ev
                | let v := eval hnf in x in
                  let hv := head_of v in
                  tryif is_constructor hv then (
                        (replace x with v by reflexivity);
                        cbv beta iota; ev)
                  else idtac ]
with ev_unfold m :=
        let h := head_of m in
        tryif is_const h then (unfold h at 1; cbv beta iota zeta; ev)
        else idtac.

(* ========================================================================== *)
(* The conf                                                                   *)
(* ========================================================================== *)

(* The facts of a conf `H`, a conjunction of facts of registers with the conf
        and its values unfolded, as the hypotheses `ev` reads: lookups, and the
        two PMP entries with the default value of Sail's model, which
        `vec_access_dec` does not look at. *)
Ltac ev_init H :=
        unfold st_regs_read, _regs_read in H;
        repeat lazymatch type of H with
                | _ /\ _ => let H1 := fresh "Hinit" in destruct H as [H1 H]
                end;
        repeat match goal with
                | H2 : Values.vec_access_dec ?v ?i = ?w |- _ =>
                        lazymatch type of H2 with
                                | Values.vec_access_dec _ _ (Inhabited0 := Values.dummy_mword) = _ => fail
                                | _ =>
                                        change (Values.vec_access_dec v i (Inhabited0 := Values.dummy_mword) = w) in H2
                                end
                end.

(* The hypotheses of the conf of an example, by `ev_init`. An example sets it
        with `::=`: it unfolds its conf and the values of it. *)
Ltac conf_intro := idtac.
