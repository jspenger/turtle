(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import turtle.compat.sail.riscv.exec.

(* Lift / lower *)

Definition _glu_asm_lift {S2 : Type}
                         (s : state)
                         (lifted : state * S2) : Prop :=
        s = fst lifted.

Definition _glu_tla_lift {S2 : Type}
                         (s : S2)
                         (lifted : state * S2) : Prop :=
        s = snd lifted.

Definition _glu_asm_lower {S2 : Type}
                          (lifted : state * S2) : state :=
        fst lifted.

Definition _glu_tla_lower {S2 : Type}
                          (lifted : state * S2) : S2 :=
        snd lifted.

(* Glu *)

Definition _glu_precond_impl_stepcond (precond : state -> Prop)
                                      (stepcond : state -> state -> Prop)
                                      (s s' : state) : Prop :=
        precond s -> stepcond s s'.
