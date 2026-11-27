(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.

#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.
#[local] Open Scope tla_scope.

Fixpoint fib (n : nat) : Z :=
        match n with
                | O    => 0
                | S n' => match n' with
                        | O     => 1
                        | S n'' => fib n' + fib n''
                        end
                end.

Record state := Build_state {
        (* If `_internal` is `true` then the last step was an "internal" step.
                Internal steps and states are to be ignored. This is achieved
                by stepping in the "asm" spec when `_internal` is set to
                true. As is done in the "glu" of `spec.v`. *)
        _internal : bool ;
        _op  : option string ;
        arg0 : Z ;
        res0 : Z ;
        }.

Definition vars (s : state) : state :=
        s.

Definition init : property state := \lift1 (fun s =>
        _internal s = false).

(* other steps (not "tl_fib") *)
Definition next_0 : property state := \lift2 (fun s s' =>
        ~ (_op s = Some "tl_fib" \/ _internal s = true)
                /\ _internal s' = false).

(* "tl_fib" step *)
Definition next_1 : property state := \lift2 (fun s s' =>
        (_op s = Some "tl_fib" \/ _internal s = true)
                /\ _internal s' = false
                /\ res0 s' = fib (Z.to_nat (arg0 s))).

(* internal step *)
Definition next_2 : property state := \lift2 (fun s s' =>
        (_op s = Some "tl_fib" \/ _internal s = true)
                /\ _internal s' = true
                /\ arg0 s' = arg0 s).

Definition next : property state :=
        next_0 \lor next_1 \lor next_2.

Definition F : property state :=
        \wf next_1 \sub vars. (* fairness applies only to the "tl_fib" step *)

Definition spec : property state :=
        init \land [][next]_vars \land F.
