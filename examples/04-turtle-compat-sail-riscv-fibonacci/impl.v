(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require Import turtle.compat.sail.riscv.prelude_all.

#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.
#[local] Open Scope asm_scope.

Definition tl_fib_impl_sec (e : env) : source_section :=
        s_text (
        (* tl_fib: *)
                addi    a1 , zero , 0               ::
                addi    a2 , zero , 1               ::
                addi    a3 , a0 , 0                 ::
                beq     a3 , zero , 8               ::
                jal     zero , 12                   ::
                addi    a0 , a1 , 0                 ::
                jalr    zero , ra , 0               ::
        (* .tl_loop: *)
                add     a4 , a1 , a2                ::
                addi    a1 , a2 , 0                 ::
                addi    a2 , a4 , 0                 ::
                addi    a3 , a3 , (-1)              ::
                beq     a3 , zero , 8               ::
                jal     zero , (-20)                ::
                addi    a0 , a1 , 0                 ::
                jalr    zero , ra , 0               ::
        nil).

Definition tl_fib_impl_s : source :=
        fun e =>
                ("tl_fib", tl_fib_impl_sec e) ::
                nil.
