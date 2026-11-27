(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.unsafe.extern.abi.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* getrandom                                                                  *)
(* ========================================================================== *)

Definition _getrandom_precond (s : state) : Prop :=
        let size  := abi_arg1 s in
        let flags := abi_arg2 s in
        0 < size < 257
                /\ flags = 0.

Definition _getrandom_stepcond (s s' : state) : Prop :=
        let buf  := abi_arg0 s in
        let size := abi_arg1 s in
        let res  := abi_signed_res0 s' in
        exists n_bytes_written,
                (-1 < n_bytes_written < size + 1)
                /\ (res = n_bytes_written
                        \/ res = -1)
                /\ forall addr,
                        let addr_z := definitions.bv_unsigned addr in
                        (addr_z < buf \/ buf + n_bytes_written - 1 < addr_z) ->
                                st_mem s' addr = st_mem s addr.

(* libc - sys/random.h - getrandom
        - C prototype:
                `ssize_t getrandom(void *buf, size_t size, unsigned int flags);`
        - name: `getrandom`
        - args#0: `a0` pointer to buffer (type `ptr`)
        - args#1: `a1` size of buffer (type `Z`)
        - args#2: `a2` flags (type `Z`)
        - return: `a0` number of random bytes written, or -1 on error (type `Z`)
        - description: fill buffer `buf` with up to `size` random bytes
        - assumptions (modeled):
                - `size` is more than 0 and at most 256
                - `flags` is 0
        - System V ABI compatible
        *)
Definition _getrandom (addr : Z) : property state :=
        [][\lift2 (
                fun s s' => _pc_addr s = addr ->
                        _getrandom_precond s ->
                                abi_precond s ->
                                        _getrandom_stepcond s s'
                                        /\ abi_stepcond s s'
                                        /\ abi_opt_stepcond_return s s')]_ exec_vars
                \land \wf (\lift2 (fun s s' =>
                        _pc_addr s = addr
                                /\ _getrandom_precond s
                                /\ abi_precond s
                                /\ _getrandom_stepcond s s'
                                /\ abi_stepcond s s'
                                /\ abi_opt_stepcond_return s s')) \sub exec_vars.

(* ========================================================================== *)
(* sys_random                                                                 *)
(* ========================================================================== *)

Definition unsafe_libc_sys_random (en : env) : property state :=
        _getrandom (en "getrandom"%string).
