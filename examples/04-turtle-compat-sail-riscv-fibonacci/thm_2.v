(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.main.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.

#[local] Open Scope tla_scope.

Theorem thm_2_1 :
        valid ((\rmap (rm e_static) (E e_static \land unsafe_libc e_static))
                        \impl (\univ_rmap (rm e_static) (unsafe_libc e_static))).
        Proof.
        (* TODO *) Admitted.

Theorem thm_2_2 :
        valid ((\rmap (rm e_static) (E e_static \land exec_static main_s))
                        \impl (\univ_rmap (rm e_static) (exec_static main_s))).
        Proof.
        (* TODO *) Admitted.
