(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import turtle.tla.TLA.
Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.lib.unsafe.libc.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.main.
Require Import turtle.compat.sail.riscv.examples.fib.spec.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.

#[local] Open Scope tla_scope.

Theorem thm_3 :
        valid ((\rmap (rm e_static)
                        (E e_static
                        \land exec_static tl_fib_impl_s
                        \land unsafe_libc e_static
                        \land exec_static main_s))
                \impl (\rmap (rm e_static)
                                (tl_fib_spec e_static
                                \land unsafe_libc e_static
                                \land exec_static main_s))).
        Proof.
        (* TODO *) Admitted.
