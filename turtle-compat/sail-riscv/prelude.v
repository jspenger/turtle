(* SPDX-License-Identifier: NoAssertionLicense *)

Require turtle.compat.sail.riscv.source.
Require turtle.compat.sail.riscv.exec.

Require Export turtle.compat.sail.riscv.notation.

Notation source_instr :=
        turtle.compat.sail.riscv.source.source_instr
        (only parsing).

Notation s_instr :=
        turtle.compat.sail.riscv.source.s_instr
        (only parsing).

Notation source_data :=
        turtle.compat.sail.riscv.source.source_data
        (only parsing).

Notation s_byte :=
        turtle.compat.sail.riscv.source.s_byte
        (only parsing).

Notation source_section :=
        turtle.compat.sail.riscv.source.source_section
        (only parsing).

Notation s_text :=
        turtle.compat.sail.riscv.source.s_text
        (only parsing).

Notation s_data :=
        turtle.compat.sail.riscv.source.s_data
        (only parsing).

Notation symbol :=
        turtle.compat.sail.riscv.source.symbol
        (only parsing).

Notation env :=
        turtle.compat.sail.riscv.source.env
        (only parsing).

Notation source :=
        turtle.compat.sail.riscv.source.source
        (only parsing).

Notation state :=
        turtle.compat.sail.riscv.exec.state
        (only parsing).

Notation conf :=
        turtle.compat.sail.riscv.exec.conf
        (only parsing).

Notation exec :=
        turtle.compat.sail.riscv.exec.exec
        (only parsing).
