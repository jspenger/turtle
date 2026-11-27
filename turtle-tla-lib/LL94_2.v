(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

Require Import turtle.tla.TLA.
Require Import turtle.gen.base.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated `Not from ref`):         *)
(* [1]                                                                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Temporal Quantification                                                    *)
(* ========================================================================== *)

(* The type of `State` is a function type from parametric variable-id type
   `Id` to a parametric value type `Var`. We do so as "quantification" rules
   that quantify over "variables" require us to define the state type such that
   we can express the meaning of two states agreeing on every variable except
   `x` (see `equal_up_to_x` below). In contrast, the other proof-rule files
   leave `State` undefined. *)
#[local] Definition State (Id Var : Type) : Type := Id -> Var.

(* The name `equal_up_to_x` is from Abadi and Merz's "On TLA as a Logic". It is
   referred to as `=_x` in [1]. *)
Definition equal_up_to_x {Id Var : Type} (x : Id) (s t : State Id Var) : Prop :=
    forall y, y <> x -> s y = t y.

Lemma equal_up_to_x_refl {Id Var : Type} (x : Id) (s : State Id Var) :
    equal_up_to_x x s s.
Proof. intros y _. reflexivity. Qed.

(* \EE `x`: `F` *)
Definition EExists {Id Var : Type} (x : Id) (F : property (State Id Var)) : property (State Id Var) :=
    ExistentialRefinementRelation (equal_up_to_x x) F.

(* \AA `x`: `F` *)
Definition FForall {Id Var : Type} (x : Id) (F : property (State Id Var)) : property (State Id Var) :=
    UniversalRefinementRelation (equal_up_to_x x) F.

(* Use `\st` standing for "such that" instead of `:`. This avoids confusion
   with Coq's token `:` standing for "type of". *)
Notation "'\EE' x \st F" :=
    (EExists x F)
    (at level 100, x at level 0, F at level 100) : tla_scope.

Notation "'\AA' x \st F" :=
    (FForall x F)
    (at level 100, x at level 0, F at level 100) : tla_scope.

(* E1 from [1] *)
Lemma EE1 {Id Var : Type} (x : Id) (F : property (State Id Var)) :
    valid (F \impl (\EE x \st F)).
Proof.
    intros beh HF. exists beh.
    split; [| exact HF].
    apply stuttering_equivalent0_pointwise. intros n. apply equal_up_to_x_refl.
Qed.

(* E2 from [1] *)
Lemma EE2 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid ((\EE x \st G) \impl G) -> (* x not free in G *)
        valid (F \impl G) ->
            valid ((\EE x \st F) \impl G).
Proof.
    intros Hfree HFG beh [beh1 [Hse HF]].
    apply Hfree. exists beh1. split; [exact Hse | exact (HFG beh1 HF)].
Qed.

(* Not from refs *)
Lemma EE3 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid (F \impl G)
        -> valid ((\EE x \st F) \impl (\EE x \st G)).
Proof.
    intros HFG beh [beh1 [Hse HF]].
    exists beh1. split; [exact Hse | exact (HFG beh1 HF)].
Qed.

(* Not from refs *)
Lemma EE4 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid ((\EE x \st F) \impl F) -> (* x not free in F *)
        valid ((\EE x \st (F \land G))
            \equiv (F \land (\EE x \st G))).
Proof.
    intros Hfree beh. split.
    - intros [beh1 [Hse [HF HG]]]. split.
        + apply Hfree. exists beh1. split; [exact Hse | exact HF].
        + exists beh1. split; [exact Hse | exact HG].
    - intros [HF [beh1 [Hse HG]]]. exists beh1. split; [exact Hse |].
        split; [| exact HG]. apply Hfree. exists beh.
        split; [| exact HF].
        apply stuttering_equivalent0_sym; [| exact Hse].
        intros s t Hst y Hy. exact (eq_sym (Hst y Hy)).
Qed.

(* E1 from [1] adapted to \AA *)
Lemma FF1 {Id Var : Type} (x : Id) (F : property (State Id Var)) :
    valid ((\AA x \st F) \impl F).
Proof.
    intros beh HA. apply (HA beh).
    apply stuttering_equivalent0_pointwise. intros n. apply equal_up_to_x_refl.
Qed.

(* E2 from [1] adapted to \AA *)
Lemma FF2 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid (G \impl (\AA x \st G)) -> (* x not free in G *)
        valid (G \impl F) ->
            valid (G \impl (\AA x \st F)).
Proof.
    intros Hfree HGF beh HG beh1 Hse. exact (HGF beh1 (Hfree beh HG beh1 Hse)).
Qed.

(* Not from refs *)
Lemma FF3 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid (F \impl G)
        -> valid ((\AA x \st F) \impl (\AA x \st G)).
Proof.
    intros HFG beh HA beh1 Hse. exact (HFG beh1 (HA beh1 Hse)).
Qed.
