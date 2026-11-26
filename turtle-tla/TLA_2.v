(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

(* ========================================================================== *)
(* This file contains advanced TLA operators and definitions. These are not   *)
(* necessary for writing standard TLA formulas. This file does not provide    *)
(* any convenient Coq notation for the operators and definitions in order to  *)
(* maintain their advanced status.                                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* References:                                                                *)
(* [1]                                                                        *)
(* > Leslie Lamport. 2026. A Science of Concurrent Programs. Cambridge        *)
(* > University Press.                                                        *)
(* > https://doi.org/10.1017/9781009719841                                    *)
(* [2]                                                                        *)
(* > Martin Abadi and Leslie Lamport. 1995. Conjoining Specifications. ACM    *)
(* > Trans. Program. Lang. Syst. 17, 3 (May 1995), 507-535.                   *)
(* > https://doi.org/10.1145/203095.201069                                    *)
(* ========================================================================== *)

Require Import turtle.tla.TLA.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* Advanced utility definitions                                               *)
(* ========================================================================== *)

(* Ref: SCP Section 8.2.1.2 [1] *)
(* "F is true of the finite behavior \sigma(0) -> ... -> \sigma(k-1)" *)
(* "For a safety property, true through state k means true if all states i with
   i > k equal state k" *)
(* Note: we define the tts operator by excluding the k'th state unlike SCP that
   includes the k'th state *)
Definition util_tts {State : Type} (P : property State) (beh : behavior State) (k : nat) : Prop :=
    k = 0
    \/ (exists beh' : behavior State,
            P beh'
            /\ (forall n : nat, n < k -> beh' n = beh n)).

(* Ref: "Conjoining Specifications", section 3.4 [2] *)
(* The closure of F `C(F)` is defined "such that a behavior \sigma satisfies
   C(F) iff every prefix of \sigma satisfies F". *)
(* `\C(F)` *)
Definition util_closure {State : Type} (F : property State) : property State :=
    fun beh => forall n : nat, util_tts F beh n.

(* Ref: "Conjoining Specifications", section 3.5 [2] *)
(* The "+ operator" is defined such that "a behavior \sigma satisfies E+v iff
   either \sigma satisfies E, or there is some n such that (1) E holds for the
   first n states of \sigma and (2) v never changes from the (n + 1)st state
   on" *)
(* `F_{+v}` *)
Definition util_plus_operator {State V : Type} (F : property State) (v : State -> V) : property State :=
    fun beh =>
        F beh
        \/ (exists k : nat,
                (forall n : nat, k <= n -> v (beh n) = v (beh (S n)))
                /\ util_tts F beh k).

(* Ref: "Conjoining Specifications", section 3.5 [2] *)
(* The "-+-> operator" is defined such that "E -+-> M is true of a behavior
   \sigma iff E => M is true of \sigma and, for every n >= 0, if E holds for the
   first n states of \sigma, then M holds for the first n + 1 states of
   \sigma." *)
(* `E -+-> F` *)
Definition util_plus_arrow {State : Type} (E F : property State) : property State :=
    fun beh =>
        (E beh -> F beh)
        /\ (forall n : nat,
                util_tts E beh n -> util_tts F beh (S n)).

(* Ref: "Conjoining Specifications", section 3.4 [2] *)
(* "(P, L) is called machine closed iff C(P /\ L) equals P" *)
(* Note: This definition is only satisfied when F is a safety property. One may
   instead define machine closed as `util_closure(F \land L) \equiv
   util_closure(F)` to express that L does not introduce any new safety
   properties beyond what is implied by F. *)
Definition util_machine_closed {State : Type} (F L : property State) : Prop :=
    valid (util_closure(F \land L) \equiv F).

(* ========================================================================== *)
(* Other utility definitions                                                  *)
(* ========================================================================== *)

(* Not from refs: *)

(* Note: the case k=0 corresponds to satisfiability of `P`, i.e., if some
   behavior exists that satisfies `P`. In contrast, `util_tts` considers
   the case k=0 as True. *)
Definition util_extends_from_state {State : Type} (P : property State) (beh : behavior State) (k : nat) : Prop :=
    exists beh' : behavior State,
        P beh'
        /\ (forall n : nat, n < k -> beh' n = beh n).

Definition util_prop_is_safety {State : Type} (F : property State) : Prop :=
    valid (util_closure F \impl F).

Definition util_prop_is_liveness {State : Type} (F : property State) : Prop :=
    valid (util_closure F).

(* Extraction of the safety property of a property. Alias of `util_closure`. *)
Definition util_prop_to_safety {State : Type} (F : property State) : property State :=
    util_closure F.

(* Extraction of the liveness property of a property. Alias of `util_closure F
   \impl F`. *)
Definition util_prop_to_liveness {State : Type} (F : property State) : property State :=
    util_closure F \impl F.
