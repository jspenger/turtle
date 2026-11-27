(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import turtle.compat.sail.riscv.source.

(* Stub for an __unsafe extern__ procedure *)
Definition unsafe_extern (name : symbol) : (symbol * source_section) :=
        (name, s_text nil).
