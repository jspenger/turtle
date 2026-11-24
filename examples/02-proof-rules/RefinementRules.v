Require Import turtle.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State1 State2 : Type}.

(* TODO: Keep only the useful rules... *)

(* ========================================================================== *)
(* Utility definitions                                                        *)
(* ========================================================================== *)

(* Not from refs *)
Definition util_inverse (r : State1 -> State2) (s2 : State2) (s1 : State1) : Prop :=
    r s1 = s2.

(* Not from refs *)
Definition util_inverse0 (r : State1 -> State2 -> Prop) (s2 : State2) (s1 : State1) : Prop :=
    r s1 s2.

(* Not from refs *)
Definition util_reflexive (f : State1 -> State1) : Prop :=
    forall s1, f s1 = s1.

(* Not from refs *)
Definition util_reflexive0 (r: State1 -> State1 -> Prop) : Prop :=
    forall s1, r s1 s1.

(* Not from refs *)
Definition util_symmetric (f : State1 -> State1) : Prop :=
    forall s1, f (f s1) = s1.

(* Not from refs *)
Definition util_symmetric0 (r : State1 -> State1 -> Prop) : Prop :=
    forall s1 s2, r s1 s2 -> r s2 s1.

(* Not from refs *)
Definition util_partial_function0 (r : State1 -> State2 -> Prop) : Prop :=
    forall s1 s2 s3, r s1 s2 -> r s1 s3 -> s2 = s3.

(* Not from refs *)
(* The refinement mapping operator `ExistentialRefinementMapping` but __not__
   stuttering closed *)
Definition util_with2 {S1 S2 : Type} (f : S1 -> S2) (F : property S1) : property S2 :=
    fun beh2 =>
        exists beh1 : behavior S1,
            (forall n : nat, f (beh1 n) = beh2 n)
            /\ F beh1.

(* Not from refs *)
(* The refinement mapping operator `UniversalRefinementMapping` but __not__
   stuttering closed *)
Definition util_co_with2 {S1 S2 : Type} (f : S1 -> S2) (F : property S1) : property S2 :=
    fun beh2 =>
        forall beh1 : behavior S1,
            (forall n : nat, f (beh1 n) = beh2 n)
            -> F beh1.

(* Not from refs *)
(* The refinement mapping operator `ExistentialRefinementRelation` but __not__
   stuttering closed *)
Definition util_with02 {S1 S2 : Type} (r : S1 -> S2 -> Prop) (F : property S1) : property S2 :=
    fun beh2 =>
        exists beh1 : behavior S1,
            (forall n : nat, r (beh1 n) (beh2 n))
            /\ F beh1.

(* Not from refs *)
(* The refinement mapping operator `UniversalRefinementRelation` but __not__
   stuttering closed *)
Definition util_co_with02 {S1 S2 : Type} (r : S1 -> S2 -> Prop) (F : property S1) : property S2 :=
    fun beh2 =>
        forall beh1 : behavior S1,
            (forall n : nat, r (beh1 n) (beh2 n))
            -> F beh1.

(* ========================================================================== *)
(* Utility lemmas                                                             *)
(* ========================================================================== *)

(* Not from refs *)
Lemma AUX1 (Op : property State1 -> property State2) (F G : property State1) :
    (forall F G : property State1, valid (F \impl G) -> valid ((Op F) \impl (Op G))) ->
        valid (Op (F \land G)
            \impl (Op F) \land (Op G)).
Proof.
(* TODO *) Admitted. 

(* Not from refs *)
Lemma AUX2 (Op : property State1 -> property State2) (F_ : nat -> property State1) :
    (forall F G : property State1, valid (F \impl G) -> valid ((Op F) \impl (Op G))) ->
        valid (Op (\A i \st F_ i)
            \impl \A i \st Op (F_ i)).
Proof.
(* TODO *) Admitted.

(* ========================================================================== *)
(* Refinement Mapping / 0                                                     *)
(* ========================================================================== *)

(* Note: not from references *)
(* Refinement version of EE1 *)
Lemma RM1 (f : State1 -> State1) (F : property State1) :
    util_reflexive f ->
        valid (F \impl (\rmap f F)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE1 *)
Lemma R0M1 (r : State1 -> State1 -> Prop) (F : property State1) :
    util_reflexive0 r ->
        valid (F \impl (\rrel r F)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE2 *)
Lemma RM2 (f: State1 -> State1) (F G : property State1) :
    valid (\rmap f G \impl G) (* cf. "x not free in G" with "x" as f in EE2 *)
        -> valid (F \impl G)
            -> valid (\rmap f F \impl G).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE2 *)
Lemma R0M2 (r: State1 -> State1 -> Prop) (F G : property State1) :
    valid (\rrel r G \impl G) (* cf. "x not free in G" with "x" as f in EE2 *)
        -> valid (F \impl G)
            -> valid (\rrel r F \impl G).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE3 *)
Lemma RM3 (f : State1 -> State2) (F G : property State1) :
    valid (F \impl G)
        -> valid ((\rmap f F) \impl (\rmap f G)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE3 *)
Lemma R0M3 (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (F \impl G)
        -> valid ((\rrel r F) \impl (\rrel r G)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
Lemma RM4 (f : State1 -> State2) (F G : property State1) :
    util_injective f ->
        util_stuttering_closed G ->
            valid ((\rmap f F) \impl (\rmap f G)) ->
                valid (F \impl G).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM5a (f : State1 -> State2) (F G : property State1) :
    valid ((\rmap f (F \land G))
        \impl ((\rmap f F) \land (\rmap f G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM5b (f : State1 -> State2) (F_ : nat -> property State1) :
    valid ((\rmap f (\A i \st F_ i))
        \impl (\A i \st (\rmap f (F_ i)))).
Proof.
(* TODO *) Admitted.

Lemma RM5c (f : State1 -> State2) (F G : property State1) :
    valid (((\rmap f F) \land (\univ_rmap f G))
        \impl (\rmap f (F \land G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M5a (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid ((\rrel r (F \land G))
        \impl ((\rrel r F) \land (\rrel r G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M5b (r : State1 -> State2 -> Prop) (F_ : nat -> property State1) :
    valid ((\rrel r (\A i \st F_ i))
        \impl (\A i \st (\rrel r (F_ i)))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M5c (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (((\rrel r F) \land (\univ_rrel r G))
        \impl (\rrel r (F \land G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM6a (r : State1 -> State2) (F : property State2) (G : property State1) :
    util_stuttering_closed F ->
        valid ((\rmap r ((\rrel (util_inverse r) F) \land G))
            \impl (F \land (\rmap r G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M6a (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    util_partial_function0 f ->
        util_stuttering_closed F ->
            valid ((\rrel f ((\rrel (util_inverse0 f) F) \land G))
                \impl (F \land (\rrel f G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM6b (r : State1 -> State2) (F : property State2) (G : property State1) :
    valid ((F \land (\rmap r G))
        \impl (\rmap r ((\rrel (util_inverse r) F) \land G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M6b (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    valid ((F \land (\rrel f G))
        \impl (\rrel f ((\rrel (util_inverse0 f) F) \land G))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM7 (f : State1 -> State2) (F : property State1) (G : property State2) :
    valid (\rmap f F \impl G) <->
        valid (F \impl (\univ_rrel (util_inverse f) G)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M7 (f : State1 -> State2 -> Prop) (F : property State1) (G : property State2) :
    valid (\rrel f F \impl G) <->
        valid (F \impl (\univ_rrel (util_inverse0 f) G)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM8 (f : State1 -> State2) (F : property State2) (G : property State1) :
    valid (\rrel (util_inverse f) F \impl G) <->
        valid (F \impl (\univ_rmap f G)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M8 (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    valid (\rrel (util_inverse0 f) F \impl G) <->
        valid (F \impl (\univ_rrel f G)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM9 (f : State1 -> State1) (G : property State1) :
    util_symmetric f ->
        valid ((\rmap f G) \impl G) ->
            valid (G \impl (\univ_rmap f G)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M9 (r : State1 -> State1 -> Prop) (G : property State1) :
    util_symmetric0 r ->
        valid ((\rrel r G) \impl G) ->
            valid (G \impl (\univ_rrel r G)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM10a (f : State1 -> State2) (F : property State1) :
    valid ((util_with2 f F) \impl (\rmap f F)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM10b (f : State1 -> State2) (F : property State1) :
    valid ((\univ_rmap f F) \impl (util_co_with2 f F)).
Proof.
(* TODO *) Admitted.

Lemma RM11a (f : State1 -> State2) (F : property State2) :
    util_stuttering_closed F ->
        valid ((\rrel (util_inverse f) F)
            \impl (util_with02 (util_inverse f) F)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM11b (f : State1 -> State2) (F : property State2) :
    util_stuttering_closed F ->
        valid ((util_co_with02 (util_inverse f) F)
            \impl (\univ_rrel (util_inverse f) F)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM12 (f : State1 -> State2) (Bl : property State1) (A B : property State2) :
    util_stuttering_closed A ->
        util_stuttering_closed B ->
            valid (((util_with02 (util_inverse f) A) \land Bl)
                \impl (util_co_with02 (util_inverse f) B)) ->
                    valid ((A \land (\rmap f Bl)) \impl B).
Proof.
(* TODO *) Admitted.

End rules.
