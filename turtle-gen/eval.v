(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* eval.v                                                                     *)
(* -------------------------------------------------------------------------- *)
(* ========================================================================== *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require SailStdpp.Values.
Require Riscv.rv64d_types.

Require Import turtle.compat.sail.riscv.exec.

#[local] Open Scope Z_scope.

Module D := rv64d_types.Defs.

(* ========================================================================== *)
(* Results                                                                    *)
(* ========================================================================== *)

(* The end of a run: a value, an exception that was thrown, or a stop. A run
        stops where `eval_step` gives `None` for another reason than an
        exception; the model's early returns are exceptions that it catches
        again. *)
Inductive res (E A : Type) : Type :=
        | res_val (a : A) (s : state)
        | res_exn (e : E) (s : state)
        | res_stop.

Arguments res_val {E A}.
Arguments res_exn {E A}.
Arguments res_stop {E A}.

Definition to_option {E A : Type} (r : res E A) : option (A * state) :=
        match r with
                | res_val a s => Some (a, s)
                | _           => None
                end.

(* `eval_step`, with the exceptions. *)
Fixpoint evalx
                {E A : Type}
                (m : D.monad E A)
                (s : state) {struct m} : res E A :=
        match m with
                | I.Ret a =>
                        res_val a s
                | I.Next (I.RegRead r _) k =>
                        evalx (k (st_regs_read s r)) s
                | I.Next (I.RegWrite r _ v) k =>
                        evalx (k tt) (st_regs_write s r v)
                | I.Next (I.MemRead n rr) k =>
                        evalx (k (inl (st_mem_read s (I.ReadReq.pa rr) n, None))) s
                | I.Next (I.MemWrite n wr) k =>
                        evalx (k (inl None))
                                (st_mem_write s (I.WriteReq.pa wr) n (I.WriteReq.value wr))
                | I.Next (I.ExtraOutcome e) _ =>
                        res_exn e s
                | I.Next (I.GenericFail _) _ =>
                        res_stop
                | I.Next I.CycleCount k =>
                        evalx (k tt) s
                | I.Next I.GetCycleCount _ =>
                        res_stop
                | I.Next (I.Choose _) _ =>
                        res_stop
                | I.Next I.Discard _ =>
                        res_stop
                | I.Next (I.Message _) k
                | I.Next (I.InstrAnnounce _) k
                | I.Next (I.BranchAnnounce _ _) k
                | I.Next (I.Barrier _) k
                | I.Next (I.CacheOp _) k
                | I.Next (I.TlbOp _) k
                | I.Next (I.TakeException _) k
                | I.Next (I.ReturnException _) k
                | I.Next (I.TranslationStart _) k
                | I.Next (I.TranslationEnd _) k =>
                        evalx (k tt) s
                end.

Lemma eval_step_evalx
                {A : Type}
                (m : rv64d_types.M A) :
        forall s,
                eval_step m s = to_option (evalx m s).
Proof.
        induction m as [a | T oc k IH]; intros s.
        - reflexivity.
        - destruct oc; cbn [eval_step evalx]; first [ apply IH | reflexivity ].
Qed.

(* ========================================================================== *)
(* bind, try_catch                                                            *)
(* ========================================================================== *)

Lemma evalx_bind
                {E A B : Type}
                (m : D.monad E A)
                (f : A -> D.monad E B) :
        forall s,
                evalx (D.bind m f) s
                        = match evalx m s with
                                | res_val a s1 => evalx (f a) s1
                                | res_exn e s1 => res_exn e s1
                                | res_stop     => res_stop
                                end.
Proof.
        unfold D.bind.
        induction m as [a | T oc k IH]; intros s.
        - reflexivity.
        - destruct oc; cbn [I.iMon_bind evalx]; first [ apply IH | reflexivity ].
Qed.

Lemma evalx_try_catch
                {E1 E2 A : Type}
                (m : D.monad E1 A)
                (h : E1 -> D.monad E2 A) :
        forall s,
                evalx (D.try_catch m h) s
                        = match evalx m s with
                                | res_val a s1 => res_val a s1
                                | res_exn e s1 => evalx (h e) s1
                                | res_stop     => res_stop
                                end.
Proof.
        induction m as [a | T oc k IH]; intros s.
        - reflexivity.
        - destruct oc; cbn [D.try_catch evalx]; first [ apply IH | reflexivity ].
Qed.

(* ========================================================================== *)
(* One result                                                                 *)
(* ========================================================================== *)

(* The run of `m` from `s` ends in `r`. *)
Definition outcome
                {E A : Type}
                (m : D.monad E A)
                (s : state)
                (r : res E A) : Prop :=
        evalx m s = r.

Lemma outcome_eval_step
                {A : Type}
                (m : rv64d_types.M A)
                s r :
        outcome m s r ->
                eval_step m s = to_option r.
Proof.
        intros H. rewrite eval_step_evalx. f_equal. exact H.
Qed.

Lemma outcome_ret
                {E A : Type}
                (a : A)
                s :
        outcome (I.Ret a : D.monad E A) s (res_val a s).
Proof.
        reflexivity.
Qed.

Lemma outcome_bind
                {E A B : Type}
                (m : D.monad E A)
                (f : A -> D.monad E B)
                s r1 r :
        outcome m s r1 ->
        match r1 with
                | res_val a s1 => outcome (f a) s1 r
                | res_exn e s1 => r = res_exn e s1
                | res_stop     => r = res_stop
                end ->
                outcome (D.bind m f) s r.
Proof.
        intros H1 H2. unfold outcome. rewrite evalx_bind, H1.
        destruct r1 as [a s1 | e s1 | ].
        - exact H2.
        - symmetry. exact H2.
        - symmetry. exact H2.
Qed.

Definition lift_res
                {R E A : Type}
                (r : res E A) : res (R + E) A :=
        match r with
                | res_val a s => res_val a s
                | res_exn e s => res_exn (inr e) s
                | res_stop    => res_stop
                end.

Lemma outcome_liftR
                {E R A : Type}
                (m : D.monad E A)
                s r :
        outcome m s r ->
                outcome (D.liftR (R := R) m) s (lift_res r).
Proof.
        intros H. unfold outcome, D.liftR. rewrite evalx_try_catch, H.
        destruct r; reflexivity.
Qed.

Definition catch_res
                {E A : Type}
                (r : res (A + E) A) : res E A :=
        match r with
                | res_val a s       => res_val a s
                | res_exn (inl a) s => res_val a s
                | res_exn (inr e) s => res_exn e s
                | res_stop          => res_stop
                end.

Lemma outcome_catch_early_return
                {E A : Type}
                (m : D.monadR A E A)
                s r :
        outcome m s r ->
                outcome (D.catch_early_return m) s (catch_res r).
Proof.
        intros H. unfold outcome, D.catch_early_return. rewrite evalx_try_catch, H.
        destruct r as [a s1 | [a | e] s1 | ]; reflexivity.
Qed.

Lemma outcome_early_return
                {A R E : Type}
                (v : R)
                s :
        outcome (D.early_return v : D.monadR R E A) s (res_exn (inl v) s).
Proof.
        reflexivity.
Qed.

Lemma outcome_throw
                {E A : Type}
                (e : E)
                s :
        outcome (D.throw e : D.monad E A) s (res_exn e s).
Proof.
        reflexivity.
Qed.

Lemma outcome_fail
                {E A : Type}
                (msg : string)
                s :
        outcome (D.fail msg : D.monad E A) s res_stop.
Proof.
        reflexivity.
Qed.

Lemma outcome_conv
                {E A : Type}
                (m : D.monad E A)
                s r r0 :
        outcome m s r ->
        r = r0 ->
                outcome m s r0.
Proof.
        intros H <-. exact H.
Qed.

(* ========================================================================== *)
(* Registers                                                                  *)
(* ========================================================================== *)

Definition set_reg
                (r : rv64d_types.register)
                (v : rv64d_types.type_of_register r)
                (s : state) : state :=
        st_regs_write s r v.

Lemma outcome_read_reg
                {E : Type}
                (r : rv64d_types.register)
                s v :
        rv64d_types.register_lookup r (st_regs s) = v ->
                outcome (D.read_reg r : D.monad E _) s (res_val v s).
Proof.
        intros <-. reflexivity.
Qed.

Lemma outcome_next_read
                {E A : Type}
                (r : rv64d_types.register)
                o
                (k : _ -> D.monad E A)
                s v res :
        rv64d_types.register_lookup r (st_regs s) = v ->
        outcome (k v) s res ->
                outcome (I.Next (I.RegRead r o) k) s res.
Proof.
        intros <- H. exact H.
Qed.

Lemma outcome_write_reg
                {E : Type}
                (r : rv64d_types.register)
                (v : rv64d_types.type_of_register r)
                s :
        outcome (D.write_reg r v : D.monad E unit) s (res_val tt (set_reg r v s)).
Proof.
        reflexivity.
Qed.

Lemma outcome_next_write
                {E A : Type}
                (r : rv64d_types.register)
                o
                (v : rv64d_types.type_of_register r)
                (k : unit -> D.monad E A)
                s res :
        outcome (k tt) (set_reg r v s) res ->
                outcome (I.Next (I.RegWrite r o v) k) s res.
Proof.
        intros H. exact H.
Qed.

Lemma mem_set_reg r v s :
        st_mem (set_reg r v s) = st_mem s.
Proof.
        reflexivity.
Qed.

Lemma lookup_set_same r v s :
        rv64d_types.register_lookup r (st_regs (set_reg r v s)) = v.
Proof.
        apply rv64d_types.register_lookup_set.
Qed.

Lemma lookup_set_other r r' v s :
        rv64d_types.register_beq r r' = false ->
                rv64d_types.register_lookup r (st_regs (set_reg r' v s))
                        = rv64d_types.register_lookup r (st_regs s).
Proof.
        apply rv64d_types.irrelevant_register_set.
Qed.

(* ========================================================================== *)
(* Memory                                                                     *)
(* ========================================================================== *)

(* The tag that a read gives does not change the result. *)
Lemma outcome_mem_read
                {E A : Type}
                (n : N)
                (rr : I.ReadReq.t n)
                (k : _ -> D.monad E A)
                s w res :
        _mem_read (st_mem s) (I.ReadReq.pa rr) n = w ->
        (forall t, outcome (k (inl (w, t))) s res) ->
                outcome (I.Next (I.MemRead n rr) k) s res.
Proof.
        intros <- H. exact (H None).
Qed.

(* The answer that a write gives does not change the result. *)
Lemma outcome_mem_write
                {E A : Type}
                (n : N)
                (wr : I.WriteReq.t n)
                (k : _ -> D.monad E A)
                s res :
        (forall ob, outcome (k (inl ob))
                (Build_state
                        (st_regs s)
                        (_mem_write (st_mem s) (I.WriteReq.pa wr) n (I.WriteReq.value wr)))
                res) ->
                outcome (I.Next (I.MemWrite n wr) k) s res.
Proof.
        intros H. exact (H None).
Qed.

(* ========================================================================== *)
(* Choices                                                                    *)
(* ========================================================================== *)

(* A choice stops the run. *)
Lemma outcome_choose
                {E A : Type}
                ty
                (k : _ -> D.monad E A)
                s :
        outcome (I.Next (I.Choose ty) k) s res_stop.
Proof.
        reflexivity.
Qed.

(* ========================================================================== *)
(* Conditions                                                                 *)
(* ========================================================================== *)

Lemma outcome_if_true
                {E A : Type}
                (c : bool)
                (a b : D.monad E A)
                s r :
        c = true ->
        outcome a s r ->
                outcome (if c then a else b) s r.
Proof.
        intros ->. exact (fun H => H).
Qed.

Lemma outcome_if_false
                {E A : Type}
                (c : bool)
                (a b : D.monad E A)
                s r :
        c = false ->
        outcome b s r ->
                outcome (if c then a else b) s r.
Proof.
        intros ->. exact (fun H => H).
Qed.

(* A condition with an unknown in it: both branches. *)
Lemma outcome_if_any
                {E A : Type}
                (c : bool)
                (a b : D.monad E A)
                s ra rb :
        outcome a s ra ->
        outcome b s rb ->
                outcome (if c then a else b) s (if c then ra else rb).
Proof.
        destruct c; intros Ha Hb; assumption.
Qed.

Lemma if_same {A : Type} (c : bool) (x : A) :
        (if c then x else x) = x.
Proof.
        destruct c; reflexivity.
Qed.

Lemma outcome_assert_true
                {E : Type}
                (c : bool)
                (msg : string)
                s :
        c = true ->
                outcome (D.assert_exp c msg : D.monad E unit) s (res_val tt s).
Proof.
        intros ->. reflexivity.
Qed.

Lemma outcome_assert_exp'
                {E : Type}
                (msg : string)
                s :
        outcome (D.assert_exp' true msg : D.monad E (true = true)) s (res_val eq_refl s).
Proof.
        reflexivity.
Qed.

(* ========================================================================== *)
(* Loops                                                                      *)
(* ========================================================================== *)

(* One round of `untilMT`. *)
Lemma untilMT_round
                {E Vars : Type}
                (vars : Vars)
                (measure : Vars -> Z)
                (cond : Vars -> D.monad E bool)
                (body : Vars -> D.monad E Vars) :
        0 <= measure vars ->
                exists rest : Vars -> D.monad E Vars,
                D.untilMT vars measure cond body
                        = D.bind (body vars) (fun vars0 =>
                          D.bind (cond vars0) (fun c =>
                          if c then D.returnm vars0 else rest vars0)).
Proof.
        intros Hm. unfold D.untilMT. cbv zeta.
        destruct (D.Zwf_guarded (measure vars)) as [a].
        cbn [D.untilMT'].
        destruct (Z_ge_dec (measure vars) 0) as [Hge | Hlt].
        - eexists. reflexivity.
        - exfalso. apply Hlt. apply Z.le_ge. exact Hm.
Qed.

Lemma foreach_ZM_up'_end
                {E Vars : Type}
                (from to step : Z)
                (n : nat)
                (vars : Vars)
                (body : Z -> Vars -> D.monad E Vars) :
        (from <=? to) = false ->
                D.foreach_ZM_up' from to step n vars body = D.returnm vars.
Proof.
        intros H. destruct n; cbn [D.foreach_ZM_up']; rewrite H; reflexivity.
Qed.

Lemma foreach_ZM_up'_round
                {E Vars : Type}
                (from to step : Z)
                (n : nat)
                (vars : Vars)
                (body : Z -> Vars -> D.monad E Vars) :
        (from <=? to) = true ->
                D.foreach_ZM_up' from to step (S n) vars body
                        = D.bind (body from vars) (fun vars0 =>
                          D.foreach_ZM_up' (from + step) to step n vars0 body).
Proof.
        intros H. cbn [D.foreach_ZM_up']. rewrite H. reflexivity.
Qed.
