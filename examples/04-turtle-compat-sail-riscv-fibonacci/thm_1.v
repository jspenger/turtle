(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.conf_default.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.spec.

#[local] Open Scope bool_scope.
#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Definition e_static : env := fun name =>
        if String.eqb name "main"           then 0x10000
        else if String.eqb name "tl_fib"    then 0x11000
        else if String.eqb name ".tl_fmt"   then 0x100000
        else if String.eqb name "printf"    then 0x14000
        else if String.eqb name "exit"      then 0x14100
        else if String.eqb name "getrandom" then 0x14200
        else -1.

Definition exec_static : source -> property state :=
        exec
                conf_default
                e_static (Some "main")
                (Some (conf_stack_addr + conf_stack_size)).

(* PC is internal in tl_fib, i.e., not at label but within the boundary
        of the tl_fib source.
        *)
Definition pc_internal (e : env) (s : state) : bool :=
        ((e "tl_fib") <? _pc_addr s)
                && (_pc_addr s <? e "tl_fib" + _section_size (tl_fib_impl_sec e)).

Definition rm (e : env) (s : state) : option state :=
        (* We need some evidence in the produced state that the function is
                called, for this reason we still include the state when pc
                is at the label tl_fib.
                *)
        if pc_internal e s
                then None
                else Some s.

(* Environment assumptions... *)
Definition E (e : env) : property state :=
        [] \lift2 (fun s s' =>
                (* tl_fib always entered at label *)
                (rm e s <> None ->
                        rm e s' = None ->
                                _pc_addr s = e "tl_fib")
                (* preconditions satisfied upon tl_fib entered at label *)
                /\ (rm e s <> None ->
                        _pc_addr s <> e "tl_fib" ->
                                _pc_addr s' = e "tl_fib" ->
                                        abi_precond s'
                                        (* config is OK *)
                                        /\ conf_default s'
                                        (* RISC-V convention, only necessary
                                                because we don't have access
                                                to caller's code *) 
                                        /\ abi_ra s' mod 2 = 0 
                                        (* return address `ra` is not into
                                                tl_fib *)
                                        /\ ((abi_ra s' < e "tl_fib")
                                                \/ (e "tl_fib" + _section_size (tl_fib_impl_sec e) <= abi_ra s'))
                                        (* the source code is loaded in
                                                memory *)
                                        /\ exec_init_src_1 (tl_fib_impl_sec e) (e "tl_fib") s')).

Theorem thm_1 :
        valid ((\rmap (rm e_static)
                        (E e_static \land exec_static tl_fib_impl_s))
                \impl (\rmap (rm e_static)
                        (tl_fib_spec e_static))).
        Proof.
        (* TODO *) Admitted.
