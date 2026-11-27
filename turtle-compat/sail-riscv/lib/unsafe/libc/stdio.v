(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.ascii.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.stdint.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* printf                                                                     *)
(* ========================================================================== *)

Definition _printf_precond (s : state) : Prop :=
        let addr := abi_arg0 s in
        let cell i := st_mem_read s (definitions.Z_to_bv 64 (addr + i)) 1 in
                   cell 0 = uint8_t_cell ascii_perc (* % *)
                /\ cell 1 = uint8_t_cell ascii_l    (* l *)
                /\ cell 2 = uint8_t_cell ascii_u    (* u *)
                /\ cell 3 = uint8_t_cell ascii_nl   (* newline *)
                /\ cell 4 = uint8_t_cell ascii_nul. (* NUL *)

(* libc - stdio.h - printf
        - C prototype:
                ```C
                int printf(const char *format, ...);
                ```
        - name: `printf`
        - args#0: `a0` pointer to format string
        - args#1: `a1` uint64_t to be printed
        - return: `a0` unspecified
        - description: prints uint64_t to stdout
        - assumptions (modeled):
                - `format` is "%lu\n\0" 
        - System V ABI compatible
        *)
Definition _printf (addr : Z) : property state :=
        [][\lift2 (
                fun s s' => _pc_addr s = addr ->
                        _printf_precond s ->
                                abi_precond s ->
                                        abi_stepcond s s'
                                        /\ abi_opt_stepcond_preserve_mem s s'
                                        /\ abi_opt_stepcond_return s s')]_ exec_vars
                \land \wf (\lift2 (
                        fun s s' =>
                                _pc_addr s = addr
                                        /\ _printf_precond s
                                        /\ abi_precond s
                                        /\ abi_stepcond s s'
                                        /\ abi_opt_stepcond_preserve_mem s s'
                                        /\ abi_opt_stepcond_return s s')) \sub exec_vars.

(* ========================================================================== *)
(* stdio                                                                      *)
(* ========================================================================== *)

Definition unsafe_libc_stdio (en : env) : property state :=
        _printf (en "printf"%string).
