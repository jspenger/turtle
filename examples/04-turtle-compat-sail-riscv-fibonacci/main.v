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
        let getrandom := e "getrandom" in
        let printf    := e "printf" in
        let exit      := e "exit" in
        let tl_fib  := e "tl_fib" in
        let main    := e "main" in
        let _tl_fmt := e ".tl_fmt" in
        let _tl_err := main + 116 in (* local in main *)
        s_text (
        (* main: *)
                addi    sp , sp , (-16)             ::
                addi    a0 , sp , 0                 ::
                addi    a1 , zero , 8               ::
                addi    a2 , zero , 0               ::
                lui     ra , %hi( getrandom )       ::
                jalr    ra , ra , %lo( getrandom )  ::
                addi    t0 , zero , 8               ::
                beq     a0 , t0 , 12                ::
                lui     t0 , %hi( _tl_err )         ::
                jalr    zero , t0 , %lo( _tl_err )  ::
                lw      a0 , 0 ( sp )               ::
                andi    a0 , a0 , 31                ::
                addi    s1 , a0 , 0                 ::
                lui     ra , %hi( tl_fib )          ::
                jalr    ra , ra , %lo( tl_fib )     ::
                addi    s2 , a0 , 0                 ::
                addi    a1 , s1 , 0                 ::
                lui     a0 , %hi( _tl_fmt )         ::
                addi    a0 , a0 , %lo( _tl_fmt )    ::
                lui     ra , %hi( printf )          ::
                jalr    ra , ra , %lo( printf )     ::
                addi    a1 , s2 , 0                 ::
                lui     a0 , %hi( _tl_fmt )         ::
                addi    a0 , a0 , %lo( _tl_fmt )    ::
                lui     ra , %hi( printf )          ::
                jalr    ra , ra , %lo( printf )     ::
                addi    a0 , zero , 0               ::
                lui     ra , %hi( exit )            ::
                jalr    ra , ra , %lo( exit )       ::
        (* .tl_err: *)
                addi    a0 , zero , 1               ::
                lui     ra , %hi( exit )            ::
                jalr    ra , ra , %lo( exit )       ::
        nil).

Definition main_s : source :=
        fun e =>
                (".tl_fmt", _tl_fmt_sec) ::
                ("main", main_sec e) ::
                nil.
