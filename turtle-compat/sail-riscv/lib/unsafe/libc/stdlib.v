(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* exit                                                                       *)
(* ========================================================================== *)

(* libc - stdlib.h - exit
        - C prototype:
                `void exit(int status);`
        - name: `exit`
        - args#0: `a0` exit status (type `uint8_t`)
        - return: no return
        - description: exit with status code `status`
        - System V ABI compatible
        *)
Definition _exit (addr : Z) : property state :=
        [][\lift2 (fun s s' =>
                _pc_addr s = addr ->
                        abi_precond s ->
                                (* behavior stuck at exit as `s' = s` *)
                                s' = s)]_ exec_vars.

(* ========================================================================== *)
(* stdlib                                                                     *)
(* ========================================================================== *)

Definition unsafe_libc_stdlib (en : env) : property state :=
        _exit (en "exit"%string).
