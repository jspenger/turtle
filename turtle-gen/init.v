(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

(* ========================================================================== *)
(* init.v                                                                     *)
(* -------------------------------------------------------------------------- *)
(* A first state: memory with the bytes of sections.                          *)
(* ========================================================================== *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Require stdpp.bitvector.definitions.

Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.exec.

#[local] Open Scope Z_scope.

(* The bytes of a section. *)
Definition sec_bytes (sec : source_section) : list Z :=
        match sec with
                | s_text l =>
                        flat_map
                                (fun i => match i with s_instr ins =>
                                        let w := definitions.bv_unsigned (_instr_to_bv ins) in
                                        (w mod 256)
                                                :: (w / 256 mod 256)
                                                :: (w / 65536 mod 256)
                                                :: (w / 16777216)
                                                :: nil
                                        end)
                                l
                | s_data l =>
                        map (fun d => match d with s_byte b => definitions.bv_unsigned b end) l
                end.

(* The memory `m`, with the bytes `l` at `base`. *)
Definition put_bytes (base : Z) (l : list Z) (m : memory) : memory := fun a =>
        let i := definitions.bv_unsigned a - base in
        if (0 <=? i) && (i <? Z.of_nat (List.length l))
                then definitions.Z_to_bv 8 (nth (Z.to_nat i) l 0)
                else m a.

Definition zero_mem : memory := fun _ =>
        definitions.Z_to_bv 8 0.

(* An equation of closed words. *)
Ltac closed_eq :=
        first
                [ vm_compute; reflexivity
                | apply definitions.bv_eq; vm_compute; reflexivity ].
