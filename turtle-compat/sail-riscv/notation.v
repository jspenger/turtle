(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require Riscv.rv64d_types.

Require Import turtle.compat.sail.riscv.source.

#[local] Open Scope Z_scope.

Declare Scope asm_scope.
Delimit Scope asm_scope with asm.

#[local] Set Warnings "-notation-for-abbreviation".

Definition _notation_reg
                (n : Z) : rv64d_types.regidx :=
        rv64d_types.Regidx (definitions.Z_to_bv 5 n).

Notation x0   := (_notation_reg 0).
Notation x1   := (_notation_reg 1).
Notation x2   := (_notation_reg 2).
Notation x3   := (_notation_reg 3).
Notation x4   := (_notation_reg 4).
Notation x5   := (_notation_reg 5).
Notation x6   := (_notation_reg 6).
Notation x7   := (_notation_reg 7).
Notation x8   := (_notation_reg 8).
Notation x9   := (_notation_reg 9).
Notation x10  := (_notation_reg 10).
Notation x11  := (_notation_reg 11).
Notation x12  := (_notation_reg 12).
Notation x13  := (_notation_reg 13).
Notation x14  := (_notation_reg 14).
Notation x15  := (_notation_reg 15).
Notation x16  := (_notation_reg 16).
Notation x17  := (_notation_reg 17).
Notation x18  := (_notation_reg 18).
Notation x19  := (_notation_reg 19).
Notation x20  := (_notation_reg 20).
Notation x21  := (_notation_reg 21).
Notation x22  := (_notation_reg 22).
Notation x23  := (_notation_reg 23).
Notation x24  := (_notation_reg 24).
Notation x25  := (_notation_reg 25).
Notation x26  := (_notation_reg 26).
Notation x27  := (_notation_reg 27).
Notation x28  := (_notation_reg 28).
Notation x29  := (_notation_reg 29).
Notation x30  := (_notation_reg 30).
Notation x31  := (_notation_reg 31).

Notation zero := x0.
Notation ra   := x1.
Notation sp   := x2.
Notation gp   := x3.
Notation tp   := x4.
Notation t0   := x5.
Notation t1   := x6.
Notation t2   := x7.
Notation s0   := x8.
Notation s1   := x9.
Notation a0   := x10.
Notation a1   := x11.
Notation a2   := x12.
Notation a3   := x13.
Notation a4   := x14.
Notation a5   := x15.
Notation a6   := x16.
Notation a7   := x17.
Notation s2   := x18.
Notation s3   := x19.
Notation s4   := x20.
Notation s5   := x21.
Notation s6   := x22.
Notation s7   := x23.
Notation s8   := x24.
Notation s9   := x25.
Notation s10  := x26.
Notation s11  := x27.
Notation t3   := x28.
Notation t4   := x29.
Notation t5   := x30.
Notation t6   := x31.

Definition _notation_utype
                (op : rv64d_types.uop)
                (rd : rv64d_types.regidx)
                (imm : Z) : source_instr :=
        s_instr (rv64d_types.UTYPE (definitions.Z_to_bv 20 imm, rd, op)).

Notation "'lui' rd , imm" :=
        (_notation_utype rv64d_types.LUI rd imm)
        (at level 40, rd, imm at level 0) : asm_scope.

Notation "'auipc' rd , imm" :=
        (_notation_utype rv64d_types.AUIPC rd imm)
        (at level 40, rd, imm at level 0) : asm_scope.

Definition _notation_jal
                (rd : rv64d_types.regidx)
                (imm : Z) : source_instr :=
        s_instr (rv64d_types.JAL (definitions.Z_to_bv 21 imm, rd)).

Notation "'jal' rd , imm" :=
        (_notation_jal rd imm)
        (at level 40, rd, imm at level 0) : asm_scope.

Definition _notation_jalr
                (rd rs1 : rv64d_types.regidx)
                (imm : Z) : source_instr :=
        s_instr (rv64d_types.JALR (definitions.Z_to_bv 12 imm, rs1, rd)).

Notation "'jalr' rd , rs1 , imm" :=
        (_notation_jalr rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.

Definition _notation_btype
                (op : rv64d_types.bop)
                (rs1 rs2 : rv64d_types.regidx)
                (imm : Z) : source_instr :=
        s_instr (rv64d_types.BTYPE (definitions.Z_to_bv 13 imm, rs2, rs1, op)).

(* In assembly: `beq rs1, rs2, . + imm` or `beq rs1, rs2, . - imm` *)
Notation "'beq' rs1 , rs2 , imm" :=
        (_notation_btype rv64d_types.BEQ rs1 rs2 imm)
        (at level 40, rs1, rs2, imm at level 0) : asm_scope.
Notation "'bne' rs1 , rs2 , imm" :=
        (_notation_btype rv64d_types.BNE rs1 rs2 imm)
        (at level 40, rs1, rs2, imm at level 0) : asm_scope.
Notation "'blt' rs1 , rs2 , imm" :=
        (_notation_btype rv64d_types.BLT rs1 rs2 imm)
        (at level 40, rs1, rs2, imm at level 0) : asm_scope.
Notation "'bge' rs1 , rs2 , imm" :=
        (_notation_btype rv64d_types.BGE rs1 rs2 imm)
        (at level 40, rs1, rs2, imm at level 0) : asm_scope.
Notation "'bltu' rs1 , rs2 , imm" :=
        (_notation_btype rv64d_types.BLTU rs1 rs2 imm)
        (at level 40, rs1, rs2, imm at level 0) : asm_scope.
Notation "'bgeu' rs1 , rs2 , imm" :=
        (_notation_btype rv64d_types.BGEU rs1 rs2 imm)
        (at level 40, rs1, rs2, imm at level 0) : asm_scope.

Definition _notation_load
                (unsigned : bool)
                (width : Z)
                (rd : rv64d_types.regidx)
                (imm : Z)
                (rs1 : rv64d_types.regidx) : source_instr :=
        s_instr (rv64d_types.LOAD (definitions.Z_to_bv 12 imm, rs1, rd, unsigned, width)).

Notation "'lb' rd , imm ( rs1 )" :=
        (_notation_load false 1 rd imm rs1)
        (at level 0, rd, imm, rs1 at level 0) : asm_scope.
Notation "'lh' rd , imm ( rs1 )" :=
        (_notation_load false 2 rd imm rs1)
        (at level 0, rd, imm, rs1 at level 0) : asm_scope.
Notation "'lw' rd , imm ( rs1 )" :=
        (_notation_load false 4 rd imm rs1)
        (at level 0, rd, imm, rs1 at level 0) : asm_scope.
Notation "'lbu' rd , imm ( rs1 )" :=
        (_notation_load true 1 rd imm rs1)
        (at level 0, rd, imm, rs1 at level 0) : asm_scope.
Notation "'lhu' rd , imm ( rs1 )" :=
        (_notation_load true 2 rd imm rs1)
        (at level 0, rd, imm, rs1 at level 0) : asm_scope.

Definition _notation_store
                (width : Z)
                (rs2 : rv64d_types.regidx)
                (imm : Z)
                (rs1 : rv64d_types.regidx) : source_instr :=
        s_instr (rv64d_types.STORE (definitions.Z_to_bv 12 imm, rs2, rs1, width)).

Notation "'sb' rs2 , imm ( rs1 )" :=
        (_notation_store 1 rs2 imm rs1)
        (at level 0, rs2, imm, rs1 at level 0) : asm_scope.
Notation "'sh' rs2 , imm ( rs1 )" :=
        (_notation_store 2 rs2 imm rs1)
        (at level 0, rs2, imm, rs1 at level 0) : asm_scope.
Notation "'sw' rs2 , imm ( rs1 )" :=
        (_notation_store 4 rs2 imm rs1)
        (at level 0, rs2, imm, rs1 at level 0) : asm_scope.

Definition _notation_itype
                (op : rv64d_types.iop)
                (rd rs1 : rv64d_types.regidx)
                (imm : Z) : source_instr :=
        s_instr (rv64d_types.ITYPE (definitions.Z_to_bv 12 imm, rs1, rd, op)).

Notation "'addi' rd , rs1 , imm" :=
        (_notation_itype rv64d_types.ADDI rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.
Notation "'slti' rd , rs1 , imm" :=
        (_notation_itype rv64d_types.SLTI rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.
Notation "'sltiu' rd , rs1 , imm" :=
        (_notation_itype rv64d_types.SLTIU rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.
Notation "'xori' rd , rs1 , imm" :=
        (_notation_itype rv64d_types.XORI rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.
Notation "'ori' rd , rs1 , imm" :=
        (_notation_itype rv64d_types.ORI rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.
Notation "'andi' rd , rs1 , imm" :=
        (_notation_itype rv64d_types.ANDI rd rs1 imm)
        (at level 40, rd, rs1, imm at level 0) : asm_scope.

Definition _notation_shiftiop
                (op : rv64d_types.sop)
                (rd rs1 : rv64d_types.regidx)
                (shamt : Z) : source_instr :=
        s_instr (rv64d_types.SHIFTIOP (definitions.Z_to_bv 6 shamt, rs1, rd, op)).

Notation "'slli' rd , rs1 , shamt" :=
        (_notation_shiftiop rv64d_types.SLLI rd rs1 shamt)
        (at level 40, rd, rs1, shamt at level 0) : asm_scope.
Notation "'srli' rd , rs1 , shamt" :=
        (_notation_shiftiop rv64d_types.SRLI rd rs1 shamt)
        (at level 40, rd, rs1, shamt at level 0) : asm_scope.
Notation "'srai' rd , rs1 , shamt" :=
        (_notation_shiftiop rv64d_types.SRAI rd rs1 shamt)
        (at level 40, rd, rs1, shamt at level 0) : asm_scope.

Definition _notation_rtype
                (op : rv64d_types.rop)
                (rd rs1 rs2 : rv64d_types.regidx) : source_instr :=
        s_instr (rv64d_types.RTYPE (rs2, rs1, rd, op)).

Notation "'add' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.ADD rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'sub' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.SUB rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'sll' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.SLL rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'slt' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.SLT rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'sltu' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.SLTU rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'xor' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.XOR rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'srl' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.SRL rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'sra' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.SRA rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'or' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.OR rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.
Notation "'and' rd , rs1 , rs2" :=
        (_notation_rtype rv64d_types.AND rd rs1 rs2)
        (at level 40, rd, rs1, rs2 at level 0) : asm_scope.

Definition _notation_fence : source_instr :=
        s_instr (rv64d_types.FENCE (definitions.Z_to_bv 4 0, definitions.Z_to_bv 4 15, definitions.Z_to_bv 4 15, x0, x0)).

Definition _notation_fencei : source_instr :=
        s_instr (rv64d_types.FENCEI (definitions.Z_to_bv 12 0, x0, x0)).

Notation "'fence'" :=
        _notation_fence : asm_scope.
Notation "'fence.i'" :=
        _notation_fencei : asm_scope.

Definition _notation_ecall : source_instr :=
        s_instr (rv64d_types.ECALL tt).
Definition _notation_ebreak : source_instr :=
        s_instr (rv64d_types.EBREAK tt).

Notation "'ecall'" :=
        _notation_ecall : asm_scope.
Notation "'ebreak'" :=
        _notation_ebreak : asm_scope.

Definition _notation_csrreg
                (op : rv64d_types.csrop)
                (rd : rv64d_types.regidx)
                (csr : Z)
                (rs1 : rv64d_types.regidx) : source_instr :=
        s_instr (rv64d_types.CSRReg (definitions.Z_to_bv 12 csr, rs1, rd, op)).

Definition _notation_csrimm
                (op : rv64d_types.csrop)
                (rd : rv64d_types.regidx)
                (csr uimm : Z) : source_instr :=
        s_instr (rv64d_types.CSRImm (definitions.Z_to_bv 12 csr, definitions.Z_to_bv 5 uimm, rd, op)).

Notation "'csrrw' rd , csr , rs1" :=
        (_notation_csrreg rv64d_types.CSRRW rd csr rs1)
        (at level 40, rd, csr, rs1 at level 0) : asm_scope.
Notation "'csrrs' rd , csr , rs1" :=
        (_notation_csrreg rv64d_types.CSRRS rd csr rs1)
        (at level 40, rd, csr, rs1 at level 0) : asm_scope.
Notation "'csrrc' rd , csr , rs1" :=
        (_notation_csrreg rv64d_types.CSRRC rd csr rs1)
        (at level 40, rd, csr, rs1 at level 0) : asm_scope.
Notation "'csrrwi' rd , csr , uimm" :=
        (_notation_csrimm rv64d_types.CSRRW rd csr uimm)
        (at level 40, rd, csr, uimm at level 0) : asm_scope.
Notation "'csrrsi' rd , csr , uimm" :=
        (_notation_csrimm rv64d_types.CSRRS rd csr uimm)
        (at level 40, rd, csr, uimm at level 0) : asm_scope.
Notation "'csrrci' rd , csr , uimm" :=
        (_notation_csrimm rv64d_types.CSRRC rd csr uimm)
        (at level 40, rd, csr, uimm at level 0) : asm_scope.

Definition _notation_byte
                (n : Z) : source_data :=
        s_byte (definitions.Z_to_bv 8 n).

Definition _notation_asciz
                (s : string) : list source_data :=
        map
                _notation_byte
                (map 
                        (fun c => Z.of_nat (nat_of_ascii c))
                        (list_ascii_of_string s) ++ 0 :: nil).

Notation ".asciz s" :=
        (_notation_asciz s)
        (at level 40, s at level 0) : asm_scope.

Definition _notation_space
                (n : Z) : list source_data :=
        repeat (_notation_byte 0) (Z.to_nat n).

Notation ".space n" :=
        (_notation_space n)
        (at level 40, n at level 0) : asm_scope.

Definition _notation_hi
                (a : Z) : Z :=
        (a + 2048) / 4096.

Definition _notation_lo
                (a : Z) : Z :=
        a - 4096 * _notation_hi a.

Notation "'%hi(' a ')'" :=
        (_notation_hi a)
        (at level 0) : asm_scope.

Notation "'%lo(' a ')'" :=
        (_notation_lo a)
        (at level 0) : asm_scope.

Definition _notation_pcrel_hi
                (a : Z) : Z :=
        (a + 2048) / 4096.

Definition _notation_pcrel_lo
                (a : Z) : Z :=
        a - 4096 * _notation_pcrel_hi a.

Notation "'%pcrel_hi(' a ')'" :=
        (_notation_pcrel_hi a)
        (at level 0) : asm_scope.

Notation "'%pcrel_lo(' a ')'" :=
        (_notation_pcrel_lo a)
        (at level 0) : asm_scope.
