(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.

Require stdpp.bitvector.definitions.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.tla.TLA.

Require Import turtle.compat.sail.riscv.source.
Require Import turtle.compat.sail.riscv.notation.

#[local] Open Scope Z_scope.
#[local] Open Scope tla_scope.

Definition memory : Type :=
        rv64d_types.Arch.pa -> definitions.bv 8.

Record state : Type := Build_state {
        st_regs : rv64d_types.regstate;
        st_mem  : memory;
        }.

Definition conf : Type :=
        state -> Prop.

Definition _regs_read
                (regs : rv64d_types.regstate)
                (r : rv64d_types.register) : rv64d_types.type_of_register r :=
        rv64d_types.register_lookup r regs.

Definition _regs_write
                (regs : rv64d_types.regstate)
                (r : rv64d_types.register)
                (v : rv64d_types.type_of_register r) : rv64d_types.regstate :=
        rv64d_types.register_set r v regs.

Definition _mem_read
                (m : memory)
                (a : rv64d_types.Arch.pa)
                (n : N) : definitions.bv (8 * n) :=
        let addr_seq := definitions.bv_seq a (Z.of_N n) in
        let byte_seq := map m addr_seq in
        let z := definitions.little_endian_to_bv 8 byte_seq in 
        definitions.Z_to_bv (8 * n) z.

Definition _mem_write
                (m : memory)
                (a : rv64d_types.Arch.pa)
                (n : N)
                (v : definitions.bv (8 * n)) : memory :=
        let ith_byte := fun i => definitions.bv_extract (8 * i) 8 v in
        let diff := fun a' => Z.to_N (definitions.bv_unsigned (definitions.bv_sub a' a)) in
        fun a' =>
                if N.ltb (diff a') n
                then ith_byte (diff a')
                else m a'.

Definition st_regs_read
                (s : state)
                (r : rv64d_types.register) : rv64d_types.type_of_register r :=
        _regs_read (st_regs s) r.

Definition st_regs_write
                (s : state)
                (r : rv64d_types.register)
                (v : rv64d_types.type_of_register r) : state :=
        Build_state
                (_regs_write (st_regs s) r v)
                (st_mem s).

Definition st_mem_read
                (s : state)
                (a : rv64d_types.Arch.pa)
                (n : N) : definitions.bv (8 * n) :=
        _mem_read (st_mem s) a n.

Definition st_mem_write
                (s : state)
                (a : rv64d_types.Arch.pa)
                (n : N)
                (v : definitions.bv (8 * n)) : state :=
        Build_state
                (st_regs s)
                (_mem_write (st_mem s) a n v).

Module I := rv64d_types.Interface.

(* __Sequential__ evaluation step. Returns `Some (A * state)` on success,
        returns `None` on failure or unsupported operations. `None` shall be
        treated as __undefined behavior__. *)
Fixpoint eval_step
                {A : Type}
                (m : rv64d_types.M A) (* Sail's RISC-V monad *)
                (s : state)
                : option (A * state) :=
        match m with
                (* Done *)
                | I.Ret a                     => Some (a, s)

                (* Read/write registers *)
                | I.Next (I.RegRead r _)    k => eval_step (k (st_regs_read s r)) s
                | I.Next (I.RegWrite r _ v) k => eval_step (k tt) (st_regs_write s r v)

                (* Read/write mem. Always succeeds (`inl`) with tag `None`.
                        FIXME: Check OK to set tag to `None` *)
                | I.Next (I.MemRead n rr)   k =>
                        let v := st_mem_read s (I.ReadReq.pa rr) n in
                        eval_step (k (inl (v, None))) s
                | I.Next (I.MemWrite n wr)  k =>
                        let s' := st_mem_write s (I.WriteReq.pa wr) n (I.WriteReq.value wr) in
                        eval_step (k (inl None)) s'

                (* Ignore not necessary operations (or, not necessary for 
                        sequential evaluation) *)
                (* Ignore debug *)
                | I.Next (I.Message _)          k => eval_step (k tt) s
                (* Ignore *)
                | I.Next  I.CycleCount          k => eval_step (k tt) s
                (* Not relevant to sequential *)
                | I.Next (I.InstrAnnounce _)    k => eval_step (k tt) s
                | I.Next (I.BranchAnnounce _ _) k => eval_step (k tt) s
                | I.Next (I.Barrier _)          k => eval_step (k tt) s
                | I.Next (I.CacheOp _)          k => eval_step (k tt) s
                | I.Next (I.TlbOp _)            k => eval_step (k tt) s
                | I.Next (I.TakeException _)    k => eval_step (k tt) s
                | I.Next (I.ReturnException _)  k => eval_step (k tt) s
                | I.Next (I.TranslationStart _) k => eval_step (k tt) s
                | I.Next (I.TranslationEnd _)   k => eval_step (k tt) s

                (* Fail on unsupported operations *)
                | I.Next  I.GetCycleCount _       => None
                | I.Next (I.Choose _) _           => None
                | I.Next (I.ExtraOutcome _) _     => None
                | I.Next (I.GenericFail _) _      => None
                | I.Next  I.Discard _             => None
                end.

Definition exec_eval_step_1 (s s' : state) : Prop :=
        let m := rv64d.try_step 0 true in
        match eval_step m s with
                | Some (_, s'') => s' = s''
                | None          => True
                end.

(* TODO: See if this step can be removed *)
Definition exec_eval_step_2 (s s' : state) : Prop :=
        let m := rv64d.tick_clock tt in
        match eval_step m s with
                | Some (_, s'') => s' = s''
                | None          => True
                end.

Definition _pc_addr (s : state) : Z :=
        definitions.bv_unsigned
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.PC)).

Definition exec_init_pc_1 (start_offset : Z) (s : state) : Prop :=
        _pc_addr s
                = start_offset.

Definition exec_init_sp_1 (start_sp : Z) (s : state) : Prop :=
        (definitions.bv_unsigned
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.x2)))
                = start_sp.

Definition _instr_to_bv (instr : rv64d_types.instruction) : definitions.bv 32 :=
        match rv64d.encdec_forwards instr with
                | I.Ret w => w
                | _       => definitions.Z_to_bv 32 0 (* 0 is illegal instr by RISC-V convention *)
                end.

Fixpoint _init_s_text (stmnts : list source_instr) (addr : Z) (s : state) : Prop :=
        match stmnts with
                | (s_instr instr) :: t =>
                        _init_s_text t (addr + 4) s (* instr always size 4 *)
                                /\ (st_mem_read s (definitions.Z_to_bv 64 addr) 4
                                        = _instr_to_bv instr)
                | nil => True
                end.

Fixpoint _init_s_data (stmnts : list source_data) (addr : Z) (s : state) : Prop :=
        match stmnts with
                | (s_byte byte) :: t =>
                        _init_s_data t (addr + 1) s
                                /\ (st_mem_read s (definitions.Z_to_bv 64 addr) 1
                                        = byte)
                | nil => True
                end.

Definition exec_init_src_1 (sec : source_section) (addr : Z) (s : state) : Prop :=
        match sec with
                | s_text stmnts => _init_s_text stmnts addr s
                | s_data stmnts => _init_s_data stmnts addr s
                end.

Definition _section_size (sec : source_section) : Z :=
        match sec with
                | s_text stmnts => Z.of_nat (List.length stmnts) * 4
                | s_data stmnts => Z.of_nat (List.length stmnts)
                end.

Definition exec_next_src_1 (sec : source_section) (addr : Z) (s s' : state) : Prop :=
        let lo := addr in
        let hi := addr + _section_size sec in
        (addr - 1 < _pc_addr s < (addr + _section_size sec)) ->
                exec_eval_step_1 s s' \/ exec_eval_step_2 s s'.

Definition exec_fair_src_1 (sec : source_section) (addr : Z) (s s' : state) : Prop :=
        (addr - 1 < _pc_addr s < (addr + _section_size sec))
                /\ exec_eval_step_1 s s'.

(* ========================================================================== *)
(* TLA formulas                                                               *)
(* ========================================================================== *)

Definition exec_vars := fun s : state => s.

Definition _true_1 : property state := \lift1 (fun _ => True).

Definition exec_init_sp
                (start_sp : option Z) : property state :=
        match start_sp with
                | Some z => \lift1 (exec_init_sp_1 z)
                | None   => _true_1
                end.

Definition exec_init_pc
                (e : env)
                (start : option symbol) : property state :=
        match start with
                | Some sym => \lift1 (exec_init_pc_1 (e sym))
                | None     => _true_1
                end.

Fixpoint exec_init_src
                (e : env)
                (secs : list (symbol * source_section)) : property state :=
        match secs with
                | (sym, sec) :: t => (exec_init_src e t)
                                        \land \lift1
                                              (exec_init_src_1 sec (e sym))
                | nil => _true_1
                end.

Fixpoint exec_next_src
                (e : env)
                (secs : list (symbol * source_section)) : property state :=
        match secs with
                | (sym, sec) :: t => (exec_next_src e t)
                                                \land [][\lift2
                                                        (exec_next_src_1 sec (e sym))
                                                        ]_exec_vars
                | nil => _true_1
                end.

Fixpoint exec_fair_src
                (e : env)
                (secs : list (symbol * source_section)) : property state :=
        match secs with
                | (sym, sec) :: t => (exec_fair_src e t)
                                                \land \wf (\lift2
                                                          (exec_fair_src_1 sec (e sym)))
                                                          \sub exec_vars
                | nil => _true_1
                end.

Definition exec
                (c : conf)
                (e : env)
                (start : option symbol)
                (start_sp : option Z)
                (src : source) : property state :=
        \lift1 (fun s => c s)                   (* init config *)
                \land (exec_init_pc e start)    (* init pc to start *)
                \land (exec_init_sp start_sp)   (* init sp to start_sp *)
                \land (exec_init_src e (src e)) (* init source *)
                \land (exec_next_src e (src e)) (* step *)
                \land (exec_fair_src e (src e)) (* fairness *)
                .
