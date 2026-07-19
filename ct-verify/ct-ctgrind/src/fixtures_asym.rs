//! Registrations for asymmetric fixtures with one secret scalar input.

use krabi_caliper::{ctgrind_asym_pow_u32, ctgrind_asym_select_u8, ctgrind_asym_shl_u32};

ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u8__N16, u8, 16);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u16__N16, u16, 16);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u32__N4, u32, 4);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u32__N16, u32, 16);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u64__N4, u64, 4);

ctgrind_asym_select_u8!(ct_fix__ASYM__subtle_cond_select__u8__N16, u8, 16);
ctgrind_asym_select_u8!(ct_fix__ASYM__subtle_cond_select__u16__N16, u16, 16);
ctgrind_asym_select_u8!(ct_fix__ASYM__subtle_cond_select__u32__N4, u32, 4);
ctgrind_asym_select_u8!(ct_fix__ASYM__subtle_cond_select__u32__N16, u32, 16);
ctgrind_asym_select_u8!(ct_fix__ASYM__subtle_cond_select__u64__N4, u64, 4);

ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u8__N16, u8, 16);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u16__N16, u16, 16);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u32__N4, u32, 4);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u32__N16, u32, 16);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u64__N4, u64, 4);
