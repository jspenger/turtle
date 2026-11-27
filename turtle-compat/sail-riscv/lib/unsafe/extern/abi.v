(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.

Require stdpp.bitvector.definitions.
Require Riscv.rv64d_types.

Require Import turtle.compat.sail.riscv.exec.
Require Import turtle.compat.sail.riscv.lib.conf.preserve_conf.

#[local] Open Scope Z_scope.

(* Reference: *)
(* > RISC-V ABIs Specification, Document Version November 04, 2026-draft, *)
(* > Editors Kito Cheng and Jessica Clarke, RISC-V International, *)
(* > November 2026. *)
(* > https://riscv-non-isa.github.io/riscv-elf-psabi-doc/ *)
(* > https://github.com/riscv-non-isa/riscv-elf-psabi-doc *)

Definition _state_regs_to_z
                (s : state)
                (r : rv64d_types.register_bitvector_64) : Z :=
        definitions.bv_unsigned (
                st_regs_read s (rv64d_types.R_bitvector_64 r)).

Definition _state_regs_to_signed_z
                (s : state)
                (r : rv64d_types.register_bitvector_64) : Z :=
        definitions.bv_signed (
                st_regs_read s (rv64d_types.R_bitvector_64 r)).

Definition _state_regs_to_bv
                (s : state)
                (r : rv64d_types.register_bitvector_64) : definitions.bv 64 :=
        st_regs_read s (rv64d_types.R_bitvector_64 r).

Definition abi_ra (s : state) : Z := _state_regs_to_z s rv64d_types.x1.

Definition abi_sp (s : state) : Z := _state_regs_to_z s rv64d_types.x2.

Definition abi_a0 (s : state) : Z := _state_regs_to_z s rv64d_types.x10.
Definition abi_a1 (s : state) : Z := _state_regs_to_z s rv64d_types.x11.
Definition abi_a2 (s : state) : Z := _state_regs_to_z s rv64d_types.x12.
Definition abi_a3 (s : state) : Z := _state_regs_to_z s rv64d_types.x13.
Definition abi_a4 (s : state) : Z := _state_regs_to_z s rv64d_types.x14.
Definition abi_a5 (s : state) : Z := _state_regs_to_z s rv64d_types.x15.
Definition abi_a6 (s : state) : Z := _state_regs_to_z s rv64d_types.x16.
Definition abi_a7 (s : state) : Z := _state_regs_to_z s rv64d_types.x17.

Definition abi_signed_a0 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x10.
Definition abi_signed_a1 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x11.
Definition abi_signed_a2 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x12.
Definition abi_signed_a3 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x13.
Definition abi_signed_a4 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x14.
Definition abi_signed_a5 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x15.
Definition abi_signed_a6 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x16.
Definition abi_signed_a7 (s : state) : Z := _state_regs_to_signed_z s rv64d_types.x17.

(* Args...: *)

Definition abi_arg0 (s : state) : Z := abi_a0 s.
Definition abi_arg1 (s : state) : Z := abi_a1 s.
Definition abi_arg2 (s : state) : Z := abi_a2 s.
Definition abi_arg3 (s : state) : Z := abi_a3 s.
Definition abi_arg4 (s : state) : Z := abi_a4 s.
Definition abi_arg5 (s : state) : Z := abi_a5 s.
Definition abi_arg6 (s : state) : Z := abi_a6 s.
Definition abi_arg7 (s : state) : Z := abi_a7 s.

Definition abi_signed_arg0 (s : state) : Z := abi_signed_a0 s.
Definition abi_signed_arg1 (s : state) : Z := abi_signed_a1 s.
Definition abi_signed_arg2 (s : state) : Z := abi_signed_a2 s.
Definition abi_signed_arg3 (s : state) : Z := abi_signed_a3 s.
Definition abi_signed_arg4 (s : state) : Z := abi_signed_a4 s.
Definition abi_signed_arg5 (s : state) : Z := abi_signed_a5 s.
Definition abi_signed_arg6 (s : state) : Z := abi_signed_a6 s.
Definition abi_signed_arg7 (s : state) : Z := abi_signed_a7 s.

(* Res...: *)

Definition abi_res0 (s : state) : Z := abi_a0 s.
Definition abi_res1 (s : state) : Z := abi_a1 s.

Definition abi_signed_res0 (s : state) : Z := abi_signed_a0 s.
Definition abi_signed_res1 (s : state) : Z := abi_signed_a1 s.

(* Caller...: *)

(* ABI precond: Stack pointer aligned to 128-bit on procedure entry  *)
Definition abi_precond (s : state) : Prop :=
        abi_sp s mod 16 = 0.

(* Callee...: *)

(* Preserve callee-preserved registers *)
Definition abi_stepcond_preserve_regs (s s' : state) : Prop :=
        (_state_regs_to_bv s rv64d_types.x2 =
                                        _state_regs_to_bv s' rv64d_types.x2)
                (* x3 (gp) and x4 (tp) are "unallocatable" for this reason
                        they are also to be "preserved" *)
                /\ (_state_regs_to_bv s rv64d_types.x3  =
                                        _state_regs_to_bv s' rv64d_types.x3)
                /\ (_state_regs_to_bv s rv64d_types.x4  =
                                        _state_regs_to_bv s' rv64d_types.x4)
                /\ (_state_regs_to_bv s rv64d_types.x8  =
                                        _state_regs_to_bv s' rv64d_types.x8)
                /\ (_state_regs_to_bv s rv64d_types.x9  =
                                        _state_regs_to_bv s' rv64d_types.x9)
                /\ (_state_regs_to_bv s rv64d_types.x18 =
                                        _state_regs_to_bv s' rv64d_types.x18)
                /\ (_state_regs_to_bv s rv64d_types.x19 =
                                        _state_regs_to_bv s' rv64d_types.x19)
                /\ (_state_regs_to_bv s rv64d_types.x20 =
                                        _state_regs_to_bv s' rv64d_types.x20)
                /\ (_state_regs_to_bv s rv64d_types.x21 =
                                        _state_regs_to_bv s' rv64d_types.x21)
                /\ (_state_regs_to_bv s rv64d_types.x22 =
                                        _state_regs_to_bv s' rv64d_types.x22)
                /\ (_state_regs_to_bv s rv64d_types.x23 =
                                        _state_regs_to_bv s' rv64d_types.x23)
                /\ (_state_regs_to_bv s rv64d_types.x24 =
                                        _state_regs_to_bv s' rv64d_types.x24)
                /\ (_state_regs_to_bv s rv64d_types.x25 =
                                        _state_regs_to_bv s' rv64d_types.x25)
                /\ (_state_regs_to_bv s rv64d_types.x26 =
                                        _state_regs_to_bv s' rv64d_types.x26)
                /\ (_state_regs_to_bv s rv64d_types.x27 =
                                        _state_regs_to_bv s' rv64d_types.x27).

(* Useful but not necessary for ABI: Preserve conf *)
Definition abi_stepcond_preserve_conf (s s' : state) : Prop :=
        preserve_conf s s'.

(* ABI stepcond: Preserve callee-preserved regs *)
Definition abi_stepcond (s s' : state) : Prop :=
        abi_stepcond_preserve_regs s s'
                /\ abi_stepcond_preserve_conf s s'.

(* Optional step conditions that can be mixed in when writing specifications
        of external procedures... *)

(* Optional ABI stepcond: Preserve all memory including stack *)
Definition abi_opt_stepcond_preserve_mem (s s' : state) : Prop :=
        st_mem s =
                st_mem s'.

(* Optional ABI stepcond: Return from call *)
Definition abi_opt_stepcond_return (s s' : state) : Prop :=
        _pc_addr s' =
                abi_ra s.
