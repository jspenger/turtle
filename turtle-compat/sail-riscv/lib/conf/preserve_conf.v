(* SPDX-License-Identifier: NoAssertionLicense *)

Require Import Stdlib.ZArith.ZArith.

Require SailStdpp.Values.
Require Riscv.rv64d_types.
Require Riscv.rv64d.

Require Import turtle.compat.sail.riscv.exec.

#[local] Open Scope Z_scope.

Definition preserve_conf (s s' : state) : Prop :=
        st_regs_read    s  (rv64d_types.R_Privilege rv64d_types.cur_privilege)
         = st_regs_read s' (rv64d_types.R_Privilege rv64d_types.cur_privilege)
        /\ st_regs_read s (rv64d_types.R_bitvector_64 rv64d_types.misa)
         = st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.misa)
        /\ rv64d._get_Mstatus_SXL (st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
         = rv64d._get_Mstatus_SXL (st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
        /\ rv64d._get_Mstatus_UXL (st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
         = rv64d._get_Mstatus_UXL (st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
        /\ rv64d._get_Mstatus_MPRV (st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
         = rv64d._get_Mstatus_MPRV (st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.mstatus))
        /\ st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.mie)
         = st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.mie)
        /\ rv64d._get_Satp64_Mode (st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.satp))
         = rv64d._get_Satp64_Mode (st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.satp))
        /\ rv64d._get_SEnvcfg_PMM (st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.senvcfg))
         = rv64d._get_SEnvcfg_PMM (st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.senvcfg))
        /\ rv64d._get_SEnvcfg_LPE (st_regs_read s  (rv64d_types.R_bitvector_64 rv64d_types.senvcfg))
         = rv64d._get_SEnvcfg_LPE (st_regs_read s' (rv64d_types.R_bitvector_64 rv64d_types.senvcfg))
        /\ Values.vec_access_dec (st_regs_read s  (rv64d_types.R_vector_64_bitvector_8 rv64d_types.pmpcfg_n)) 0
         = Values.vec_access_dec (st_regs_read s' (rv64d_types.R_vector_64_bitvector_8 rv64d_types.pmpcfg_n)) 0
        /\ Values.vec_access_dec (st_regs_read s  (rv64d_types.R_vector_64_bitvector_64 rv64d_types.pmpaddr_n)) 0
         = Values.vec_access_dec (st_regs_read s' (rv64d_types.R_vector_64_bitvector_64 rv64d_types.pmpaddr_n)) 0
        /\ st_regs_read s  (rv64d_types.R_bitvector_1 rv64d_types.elp)
         = st_regs_read s' (rv64d_types.R_bitvector_1 rv64d_types.elp)
        /\ st_regs_read s  (rv64d_types.R_HartState rv64d_types.hart_state)
         = st_regs_read s' (rv64d_types.R_HartState rv64d_types.hart_state)
        /\ st_regs_read s  (rv64d_types.R_list_PMA_Region rv64d_types.pma_regions)
         = st_regs_read s' (rv64d_types.R_list_PMA_Region rv64d_types.pma_regions)
        /\ st_regs_read s  (rv64d_types.R_option_bitvector_64 rv64d_types.htif_tohost_base)
         = st_regs_read s' (rv64d_types.R_option_bitvector_64 rv64d_types.htif_tohost_base).
