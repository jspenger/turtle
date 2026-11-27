(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.compat.sail.riscv.examples.print32.conf_default.
Require Import turtle.compat.sail.riscv.examples.print32.main_1.
Require Import turtle.compat.sail.riscv.examples.print32.main_2.

#[local] Open Scope bool_scope.
#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Definition prints (e : env) (n : Z) (s : state) : bool :=
        (_pc_addr s =? e "printf")
                && (abi_arg1 s =? n).

Definition e_static : env := fun name =>
        if String.eqb name "main"           then 0x10000
        else if String.eqb name ".tl_fmt"   then 0x100000
        else if String.eqb name "printf"    then 0x14000
        else if String.eqb name "exit"      then 0x14100
        else if String.eqb name "getrandom" then 0x14200
        else -1.

Definition exec_static : source -> property state :=
        exec
                conf_default
                e_static
                (Some "main")
                (Some (conf_stack_addr + conf_stack_size)).

(* Theorem 1:
        The execution of `main_2` linked with the `unsafe_libc` library under
        static linking environment `e_static` "eventually" (i.e., `<>`)
        invokes procedure "printf" to print `32`.
        *)
Theorem thm_1 :
        valid ((exec_static main_2_s \land unsafe_libc e_static)
                \impl <>\lift1 (fun s => Is_true (prints e_static 32 s))).
        Proof.
        (* TODO *) Admitted.

(* Refinement relation `rm`:
        If the `pc` is at label "printf" and `32` is passed as the second
        argument then "produce" state `Some 32` else `None`.
                Here, "produce" should be thought of as establishing the
        relation between the "concrete" state of type `state` of the
        execution with the abstract state of type `option Z` on the
        abstract level. 
        *)
Definition rm (e : env) (s : state) : option Z :=
        if prints e 32 s
                then Some 32
                else None.

(* Theorem 2:
        The execution of `main_1` linked with the `unsafe_libc` library under
        static linking environment `e_static` under the refinement relation
        `rm` "implements" (i.e., `\impl`) the execution of `main_2` linked
        with the `unsafe_libc` library under static linking environment
        `e_static` under the refinement relation `rm`.
        *)
Theorem thm_2 :
        valid ((\rmap (rm e_static)
                        (exec_static main_1_s \land unsafe_libc e_static))
                \impl (\rmap (rm e_static)
                        (exec_static main_2_s \land unsafe_libc e_static))).
        Proof.
        (* TODO *) Admitted.
