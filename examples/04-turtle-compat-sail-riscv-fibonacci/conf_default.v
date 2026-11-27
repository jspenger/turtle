(* SPDX-License-Identifier: NoAssertionLicense *)
(* GENERATED_BY_AI: CLAUDE_FABLE_5_2 OR OPUS_5_5 *)

Require Import Stdlib.ZArith.ZArith.

Require SailStdpp.Values.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.compat.sail.riscv.exec.

#[local] Open Scope Z_scope.

Definition conf_code_addr   : Z := 0x10000.
Definition conf_code_size   : Z := 0xf0000.
Definition conf_memory_addr : Z := 0x100000.
Definition conf_memory_size : Z := 0x100000.
Definition conf_stack_addr  : Z := 0x3ffffff000.
Definition conf_stack_size  : Z := 4096.

Definition conf_pma_x : rv64d_types.PMA :=
        {|
        rv64d_types.PMA_mem_type := rv64d_types.MainMemory;
        rv64d_types.PMA_cacheable := true;
        rv64d_types.PMA_coherent := true;
        rv64d_types.PMA_executable := true;
        rv64d_types.PMA_readable := false;
        rv64d_types.PMA_writable := false;
        rv64d_types.PMA_read_idempotent := true;
        rv64d_types.PMA_write_idempotent := true;
        rv64d_types.PMA_misaligned_exceptions :=
                {|
                rv64d_types.PMAMisalignedExceptions_load_store := None;
                rv64d_types.PMAMisalignedExceptions_vector := None;
                rv64d_types.PMAMisalignedExceptions_amo := rv64d_types.AccessFault;
                rv64d_types.PMAMisalignedExceptions_lrsc := rv64d_types.AccessFault
                |};
        rv64d_types.PMA_atomic_support := rv64d_types.AMOCASQ;
        rv64d_types.PMA_reservability := rv64d_types.RsrvEventual;
        rv64d_types.PMA_supports_cbo_zero := true;
        rv64d_types.PMA_supports_pte_read := true;
        rv64d_types.PMA_supports_pte_write := true;
        rv64d_types.PMA_misaligned_atomicity_granule_size_exp := 4;
        rv64d_types.PMA_vector_misaligned_atomicity_granule_size_exp := 4
        |}.

Definition conf_pma_rw : rv64d_types.PMA :=
        {|
        rv64d_types.PMA_mem_type := rv64d_types.MainMemory;
        rv64d_types.PMA_cacheable := true;
        rv64d_types.PMA_coherent := true;
        rv64d_types.PMA_executable := false;
        rv64d_types.PMA_readable := true;
        rv64d_types.PMA_writable := true;
        rv64d_types.PMA_read_idempotent := true;
        rv64d_types.PMA_write_idempotent := true;
        rv64d_types.PMA_misaligned_exceptions :=
                {|
                rv64d_types.PMAMisalignedExceptions_load_store := None;
                rv64d_types.PMAMisalignedExceptions_vector := None;
                rv64d_types.PMAMisalignedExceptions_amo := rv64d_types.AccessFault;
                rv64d_types.PMAMisalignedExceptions_lrsc := rv64d_types.AccessFault
                |};
        rv64d_types.PMA_atomic_support := rv64d_types.AMOCASQ;
        rv64d_types.PMA_reservability := rv64d_types.RsrvEventual;
        rv64d_types.PMA_supports_cbo_zero := true;
        rv64d_types.PMA_supports_pte_read := true;
        rv64d_types.PMA_supports_pte_write := true;
        rv64d_types.PMA_misaligned_atomicity_granule_size_exp := 4;
        rv64d_types.PMA_vector_misaligned_atomicity_granule_size_exp := 4
        |}.

Definition conf_pma_region_code : rv64d_types.PMA_Region :=
        {|
        rv64d_types.PMA_Region_base := Values.mword_of_int conf_code_addr;
        rv64d_types.PMA_Region_size := Values.mword_of_int conf_code_size;
        rv64d_types.PMA_Region_attributes := conf_pma_x;
        rv64d_types.PMA_Region_include_in_device_tree := true
        |}.

Definition conf_pma_region_memory : rv64d_types.PMA_Region :=
        {|
        rv64d_types.PMA_Region_base := Values.mword_of_int conf_memory_addr;
        rv64d_types.PMA_Region_size := Values.mword_of_int conf_memory_size;
        rv64d_types.PMA_Region_attributes := conf_pma_rw;
        rv64d_types.PMA_Region_include_in_device_tree := true
        |}.

Definition conf_pma_region_stack : rv64d_types.PMA_Region :=
        {|
        rv64d_types.PMA_Region_base := Values.mword_of_int conf_stack_addr;
        rv64d_types.PMA_Region_size := Values.mword_of_int conf_stack_size;
        rv64d_types.PMA_Region_attributes := conf_pma_rw;
        rv64d_types.PMA_Region_include_in_device_tree := true
        |}.

Definition conf_pma_regions : list rv64d_types.PMA_Region :=
        conf_pma_region_code
                :: conf_pma_region_memory
                :: conf_pma_region_stack
                :: nil.

Definition conf_cur_privilege    : rv64d_types.Privilege    := rv64d_types.User.
Definition conf_misa             : Values.mword 64          := Values.mword_of_int 0x8000000000141104.
Definition conf_mstatus_sxl      : Values.mword 2           := Values.mword_of_int 0x2.
Definition conf_mstatus_uxl      : Values.mword 2           := Values.mword_of_int 0x2.
Definition conf_mstatus_mprv     : Values.mword 1           := Values.mword_of_int 0x0.
Definition conf_mie              : Values.mword 64          := Values.mword_of_int 0x0.
Definition conf_satp64_mode      : Values.mword 4           := Values.mword_of_int 0x0.
Definition conf_senvcfg_pmm      : Values.mword 2           := Values.mword_of_int 0x0.
Definition conf_senvcfg_lpe      : Values.mword 1           := Values.mword_of_int 0x0.
Definition conf_pmpcfg0          : Values.mword 8           := Values.mword_of_int 0xf.
Definition conf_pmpaddr0         : Values.mword 64          := Values.mword_of_int 0x1000000000.
Definition conf_elp              : Values.mword 1           := Values.mword_of_int 0x0.
Definition conf_hart_state       : rv64d_types.HartState    := rv64d_types.HART_ACTIVE tt.
Definition conf_htif_tohost_base : option (Values.mword 64) := None.

Definition conf_default (s : state) : Prop :=
        st_regs_read s
                (rv64d_types.R_Privilege rv64d_types.cur_privilege)
                        = conf_cur_privilege
        /\ st_regs_read s
                (rv64d_types.R_bitvector_64 rv64d_types.misa)
                        = conf_misa
        /\ rv64d._get_Mstatus_SXL
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
                        = conf_mstatus_sxl
        /\ rv64d._get_Mstatus_UXL
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
                        = conf_mstatus_uxl
        /\ rv64d._get_Mstatus_MPRV
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
                        = conf_mstatus_mprv
        /\ st_regs_read s
                (rv64d_types.R_bitvector_64 rv64d_types.mie)
                        = conf_mie
        /\ rv64d._get_Satp64_Mode
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.satp))
                        = conf_satp64_mode
        /\ rv64d._get_SEnvcfg_PMM
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.senvcfg))
                        = conf_senvcfg_pmm
        /\ rv64d._get_SEnvcfg_LPE
                (st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.senvcfg))
                        = conf_senvcfg_lpe
        /\ Values.vec_access_dec
                (st_regs_read s (rv64d_types.R_vector_64_bitvector_8 rv64d_types.pmpcfg_n)) 0
                        = conf_pmpcfg0
        /\ Values.vec_access_dec
                (st_regs_read s (rv64d_types.R_vector_64_bitvector_64 rv64d_types.pmpaddr_n)) 0
                        = conf_pmpaddr0
        /\ st_regs_read s
                (rv64d_types.R_bitvector_1 rv64d_types.elp)
                        = conf_elp
        /\ st_regs_read s
                (rv64d_types.R_HartState rv64d_types.hart_state)
                        = conf_hart_state
        /\ st_regs_read s
                (rv64d_types.R_list_PMA_Region rv64d_types.pma_regions)
                        = conf_pma_regions
        /\ st_regs_read s
                (rv64d_types.R_option_bitvector_64 rv64d_types.htif_tohost_base)
                        = conf_htif_tohost_base.
