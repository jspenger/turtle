(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.prelude_all.

Require turtle.compat.sail.riscv.examples.fib.spec_tla.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Definition at_label_asm (e : env) (sl : state) : Prop :=
        _pc_addr sl =
                e "tl_fib".

Definition at_label_tla (e : env) (sr : spec_tla.state) : Prop :=
        spec_tla._op sr =
                Some "tl_fib".

Definition at_internal_tla (sr : spec_tla.state) : Prop :=
        spec_tla._internal sr =
                true.

Definition at_label_eq (e : env) (sl : state) (sr : spec_tla.state) : Prop :=
        at_label_asm e sl <->
                at_label_tla e sr.

Definition arg_eq (sl : state) (sr : spec_tla.state) : Prop :=
        abi_arg0 sl =
                spec_tla.arg0 sr.

Definition res_eq (sl : state) (sr : spec_tla.state) : Prop :=
        abi_res0 sl =
                definitions.bv_wrap 64 (spec_tla.res0 sr).

Definition precond (s : state) : Prop :=
        abi_precond s.

Definition stepcond (s s' : state) : Prop :=
        abi_stepcond s s'
                /\ abi_opt_stepcond_preserve_mem s s'
                /\ abi_opt_stepcond_return s s'.

(* Internal steps on the spec preserve the abi conditions, memory, and return
        address. If used with a refinement mapping that hides the state of
        internal steps, then an implementation is not inhibited from
        temporarily modifying the registers or memory.
        *)
Definition stepcond_internal (s s' : state) : Prop :=
        abi_stepcond s s'
                /\ abi_opt_stepcond_preserve_mem s s'
                /\ abi_ra s' = abi_ra s.

(* tl_fib.h - tl_fib
        - C prototype:
                ```C
                uint64_t tl_fib(uint64_t n);
                ```
        - args#0: `a0` n
        - return: `a0` nth Fibonacci number (mod 2^64)
        - System V ABI compatible
        *)
Definition tl_fib_spec (e : env) : property state :=
        \rmap _glu_asm_lower (
                (\rrel _glu_tla_lift spec_tla.spec)
                (* If labels are equal then args are equal
                        *)
                \land [] \lift1 (fun s =>
                        let sl := _glu_asm_lower s in
                        let sr := _glu_tla_lower s in
                        at_label_eq e sl sr
                        /\ (at_label_asm e sl ->
                                precond sl ->
                                        arg_eq sl sr))
                (* If at (label or internal) and precond then (stepcond and
                        res equal) or internal step
                        *)
                \land [][\lift2 (fun s s' =>
                        let sl  := _glu_asm_lower s in
                        let sr  := _glu_tla_lower s in
                        let sl' := _glu_asm_lower s' in
                        let sr' := _glu_tla_lower s' in
                        (at_label_tla e sr
                                \/ at_internal_tla sr) ->
                                precond sl ->
                                        (spec_tla._internal sr' = false
                                                /\ stepcond sl sl'
                                                /\ res_eq sl' sr')
                                        \/ (spec_tla._internal sr' = true
                                                /\ stepcond_internal sl sl'))]_ (fun s => s)
                (* Fairness if enabled: (at_label_tla or internal), precond,
                        stepcond, res equal.
                        *)
                \land \wf (\lift2 (fun s s' =>
                        let sl  := _glu_asm_lower s in
                        let sr  := _glu_tla_lower s in
                        let sl' := _glu_asm_lower s' in
                        let sr' := _glu_tla_lower s' in
                        (at_label_tla e sr \/ at_internal_tla sr)
                                /\ precond sl
                                /\ spec_tla._internal sr' = false
                                /\ stepcond sl sl'
                                /\ res_eq sl' sr')) \sub (fun s => s)).
