(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require Riscv.rv64d_types.

Require Import turtle.compat.sail.riscv.prelude_all.
Require Import turtle.compat.sail.riscv.examples.fib.impl.
Require Import turtle.compat.sail.riscv.examples.fib.thm_1.

#[local] Open Scope bool_scope.
#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.

Definition _reg_eqb
                (r1 r2 : rv64d_types.regidx) : bool :=
        match r1 with
                | rv64d_types.Regidx r1 => 
                        match r2 with
                                | rv64d_types.Regidx r2 =>
                                        definitions.bv_unsigned r1 =?
                                        definitions.bv_unsigned r2
                                end
                end.

Definition _instr_ok
                (i : rv64d_types.instruction) : bool :=
        match i with
                | rv64d_types.UTYPE _
                | rv64d_types.ITYPE _
                | rv64d_types.SHIFTIOP _
                | rv64d_types.RTYPE _
                | rv64d_types.BTYPE _
                | rv64d_types.JAL _
                | rv64d_types.JALR _ => true
                (* all others are disallowed...
                        - ... *)
                | _ => false
                end.

(* Jumps (BTYPE, JAL, JALR) are only allowed if to whitelisted addr or if
        internal in the source. JALR is only allowed to the return address.
        No instruction is allowed to modify `ra`. This checks the source
        against unwanted jumps. *)

Definition _addr_whitelist : list Z :=
        e_static "printf" ::
                e_static "exit" ::
                e_static "getrandom" ::
                nil.

Definition _addr_ok
                (lo hi addr: Z) : bool :=
        ((lo - 1 <? addr)
                && (addr <? hi)
                && ((addr - lo) mod 4 =? 0))
                || existsb (Z.eqb addr) _addr_whitelist.

(* jmp instr ok if jmp to addr in the source or to whitelisted addr *)
Definition _jmp_instr_ok
                (lo hi pc : Z)
                (i : rv64d_types.instruction) : bool :=
        match i with
                | rv64d_types.BTYPE (imm, _, _, _) =>
                        _addr_ok lo hi (pc + definitions.bv_signed imm)
                | rv64d_types.JAL (imm, _) =>
                        _addr_ok lo hi (pc + definitions.bv_signed imm)
                | rv64d_types.JALR (imm, rs, rd) =>
                        (* only `ret` is OK *)
                        _reg_eqb rd zero
                                && _reg_eqb rs ra
                                && (definitions.bv_signed imm =? 0)
                | _ => true
                end.

(* instr ok if ra not modified *)
Definition _instr_ok_ra
                (i : rv64d_types.instruction) : bool :=
        match i with
                | rv64d_types.UTYPE (_, rd, _)
                | rv64d_types.ITYPE (_, _, rd, _)
                | rv64d_types.SHIFTIOP (_, _, rd, _)
                | rv64d_types.RTYPE (_, _, rd, _)
                | rv64d_types.JAL (_, rd)
                | rv64d_types.JALR (_, _, rd) => negb (_reg_eqb rd ra)
                | _ => true
                end.

Fixpoint _source_instrs_ok_0
                (stmnts : list source_instr) : bool :=
        match stmnts with
                | s_instr i :: stmnts' =>
                        _instr_ok i
                                && _instr_ok_ra i
                                && _source_instrs_ok_0 stmnts'
                | nil => true
                end.

Fixpoint _source_instrs_ok_1
                (lo hi pc : Z)
                (stmnts : list source_instr) : bool :=
        match stmnts with
                | s_instr i :: stmnts' =>
                        _jmp_instr_ok lo hi pc i
                                && _source_instrs_ok_1 lo hi (pc + 4) stmnts'
                | nil => true
                end.

(* last instr is `jal zero` or `jalr zero` *)
Fixpoint _source_instrs_ok_2
                (stmnts : list source_instr) : bool :=
        match stmnts with
                | s_instr (rv64d_types.JAL (_, rd)) :: nil
                | s_instr (rv64d_types.JALR (_, _, rd)) :: nil => _reg_eqb rd zero
                | _ :: stmnts' => _source_instrs_ok_2 stmnts'
                | nil => false
                end.

Definition _sym_label_ok
                (sym : symbol) : bool :=
        (* "main", "tl_", ".tl_" no conflict with libc*)
        String.eqb sym "main"
                || String.prefix "tl_" sym 
                || String.prefix ".tl_" sym.

Definition _source_section_ok
                (sym : symbol)
                (sec : source_section) : bool :=
        let lo := e_static sym in
        let hi := e_static sym + _section_size sec in
        match sec with
                | s_text stmnts => 
                        _source_instrs_ok_0 stmnts
                                && _source_instrs_ok_1 lo hi lo stmnts
                                && _source_instrs_ok_2 stmnts
                | s_data _ => true
                end.

Definition _source_ok
                (src : source) : bool :=
        forallb
                (fun '(sym, sec) =>
                        _sym_label_ok sym
                                && _source_section_ok sym sec)
                (src e_static).

Definition _sources_ok
                (srcs : list source) : Prop :=
        List.Forall
                (fun src => _source_ok src = true)
                srcs.

Theorem thm_5_source_ok :
        _sources_ok (tl_fib_impl_s :: nil).
Proof.
(* TODO *) Admitted.
