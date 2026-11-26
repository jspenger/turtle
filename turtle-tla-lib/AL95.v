(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

Require Import turtle.tla.TLA.
Require Import turtle.tla.TLA_2.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* [1]                                                                        *)
(* > Leslie Lamport. 2026. A Science of Concurrent Programs. Cambridge        *)
(* > University Press.                                                        *)
(* > https://doi.org/10.1017/9781009719841                                    *)
(*                                                                            *)
(* Other references:                                                          *)
(* [2]                                                                        *)
(* > Martin Abadi and Leslie Lamport. 1995. Conjoining Specifications. ACM    *)
(* > Trans. Program. Lang. Syst. 17, 3 (May 1995), 507-535.                   *)
(* > https://doi.org/10.1145/203095.201069                                    *)
(*                                                                            *)
(* The file is named after AL95 [2] which was the (first, to my knowledge)    *)
(* presentation of the decomposition and composition theorems. I don't        *)
(* remember for certain if there was a difference between [1] and [2].        *)
(* However, I seem to have favored some of the writing / definitions from     *)
(* [1] as evident in my comments.                                             *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Composition                                                                *)
(* ========================================================================== *)

Section al95.

Context {State : Type}.
#[local] Notation prop := (property State).

(* Ref: SCP Theorem 8.7 (Decomposition Theorem) *)
Theorem Decomposition {V : Type} (v : State -> V) (E Ml M : nat -> prop) :
    (forall i : nat,
            util_stuttering_closed (Ml i))  ->
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st (util_closure (M j)))
                \impl (E i))) ->
    (* 2. (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E i)) v) \land (util_closure (Ml i)))
                \impl (util_closure (M i)))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i)
        \impl (\A i \st M i)).
Proof.
(* TODO *) Admitted.

(* Ref: SCP Theorem 8.8 (Composition Theorem) *)
Theorem Composition {V : Type} (v : State -> V) (E M : prop) (E_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall j : nat,
            util_stuttering_closed (M_ j))  ->
    (* If... *)
    (* 1. *)
    valid (\A i \st (((util_closure E) \land (\A j \st (util_closure (M_ j))))
        \impl (E_ i))) ->
    (* 2. (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j \st (util_closure (M_ j))))
        \impl (util_closure M)) ->
    (* 2. (b) *)
    valid ((E \land (\A j \st M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j \st (util_plus_arrow (E_ j) (M_ j)))
        \impl (util_plus_arrow E M)).
Proof.
(* TODO *) Admitted.

(* Ref: "Conjoining Specifications" Corollary 1 *)
Corollary CompositionCor1 {V : Type} (v : State -> V) (E Ml M : prop) :
    util_stuttering_closed E ->
    util_stuttering_closed Ml ->
    (* If... *)
    valid ((util_closure E)
        \impl E)  ->
    (* (a) *)
    valid (((util_plus_operator E v) \land (util_closure Ml))
        \impl (util_closure M)) ->
    (* (b) *)
    valid ((E \land Ml)
        \impl M) ->
    (* ...then *)
    valid ((util_plus_arrow E Ml)
        \impl (util_plus_arrow E M)).
Proof.
(* TODO *) Admitted.

(* Ref: "Conjoining Specifications" Theorem 2 (General Decomposition Theorem) *)
(* The hypothesis "v is a tuple of variables including all the free variables of
   Mi" ("Conjoining Specifications", Theorem 2) is omitted. Instead, as
   suggested in SCP, "The theorem does not [need to] make any assumption about
   v". *)
(* The definition adds `(\A j \st ((\lift0 (j < i)) \impl (M_ j)))` to hypothesis
   (2) b as is done in `Decomposition` (SCP, Theorem 8.7) but missing from
   Theorem 2. *)
Theorem GeneralDecomposition {V : Type} (v : State -> V) (E : prop) (E_ Ml_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall i : nat,
            util_stuttering_closed (Ml_ i))  ->
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid (((util_closure E) \land (\A j \st (util_closure (M_ j))))
                \impl (E_ i))) ->
    (* (2) (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E_ i)) v) \land (util_closure (Ml_ i)))
                \impl (util_closure (M_ i)))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j \st (util_closure (Ml_ j))))
        \impl (\A j \st (util_closure (M_ j))))
    (* (b) *)
    /\ valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
(* TODO *) Admitted.

End al95.
