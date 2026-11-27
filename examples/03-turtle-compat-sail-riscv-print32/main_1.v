(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require Import turtle.compat.sail.riscv.prelude.
Require Import turtle.compat.sail.riscv.lib.ascii.

#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.
#[local] Open Scope asm_scope.

Definition _tl_fmt_sec : source_section :=
        s_data (
                .asciz  ("%lu" ++ ascii_str_nl)
        ).

Definition main_sec (e : env) : source_section :=
        let printf := e "printf" in
        let exit   := e "exit" in
        let main     := e "main" in
        let _tl_fmt  := e ".tl_fmt" in
        let _tl_loop := main + 8 in (* local in main *)
        s_text (
        (* main: *)
                addi    s1 , zero , 2           ::
                addi    s2 , zero , 4           ::
        (* .tl_loop: *)
                add     s1 , s1 , s1            ::
                addi    a1 , s1 , 0             ::
                lui     a0 , %hi( _tl_fmt )     ::
                addi    a0 , a0 , %lo( _tl_fmt ) ::
                lui     ra , %hi( printf )      ::
                jalr    ra , ra , %lo( printf ) ::
                addi    s2 , s2 , (-1)          ::
                beq     s2 , zero , 12          ::
                lui     t0 , %hi( _tl_loop )    ::
                jalr    zero , t0 , %lo( _tl_loop )::
                addi    a0 , zero , 0           ::
                lui     ra , %hi( exit )        ::
                jalr    ra , ra , %lo( exit )   ::
        nil).

Definition main_1_s : source :=
        fun en =>
                (".tl_fmt", _tl_fmt_sec) ::
                ("main", main_sec en) ::
                nil.
