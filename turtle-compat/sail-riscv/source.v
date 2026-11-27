(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import String.
Require Import ZArith.
Require stdpp.bitvector.definitions.
Require Riscv.rv64d_types.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.

Inductive source_instr : Type :=
        | s_instr (instr : rv64d_types.instruction)
        .

Inductive source_data : Type :=
        | s_byte (byte : definitions.bv 8)
        .

Inductive source_section : Type :=
        | s_text (stmnts : list source_instr)
        | s_data (stmnts : list source_data)
        .

Definition symbol : Type :=
        string.

Definition env : Type :=
        symbol -> Z.

Definition source : Type :=
        env -> list (symbol * source_section).
