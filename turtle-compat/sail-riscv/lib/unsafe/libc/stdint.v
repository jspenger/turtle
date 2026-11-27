(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.

Require stdpp.bitvector.definitions.

Definition uint8_t (z : Z)  : definitions.bv 8  := definitions.Z_to_bv 8 z.
Definition uint16_t (z : Z) : definitions.bv 16 := definitions.Z_to_bv 16 z.
Definition uint32_t (z : Z) : definitions.bv 32 := definitions.Z_to_bv 32 z.
Definition uint64_t (z : Z) : definitions.bv 64 := definitions.Z_to_bv 64 z.

Definition uint8_t_cell   (z : Z) : definitions.bv 8        := definitions.Z_to_bv 8 z.
Definition uint8_t_cells  (z : Z) : list (definitions.bv 8) := uint8_t_cell z :: nil.
Definition uint16_t_cells (z : Z) : list (definitions.bv 8) := definitions.bv_to_little_endian 2 8 z.
Definition uint32_t_cells (z : Z) : list (definitions.bv 8) := definitions.bv_to_little_endian 4 8 z.
Definition uint64_t_cells (z : Z) : list (definitions.bv 8) := definitions.bv_to_little_endian 8 8 z.
