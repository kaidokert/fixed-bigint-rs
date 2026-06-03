//! Category B fixture registrations — mirror of ct-fixtures' cat_b.

use crate::{
    ctgrind_checked_bin, ctgrind_checked_scalar, ctgrind_checked_un, ctgrind_cond_select,
    ctgrind_pred2, ctgrind_un,
};

// ct_eq / ct_gt / ct_lt
ctgrind_pred2!(ct_fix__B__ct_eq__u8__N16, u8, 16);
ctgrind_pred2!(ct_fix__B__ct_eq__u16__N16, u16, 16);
ctgrind_pred2!(ct_fix__B__ct_eq__u32__N4, u32, 4);
ctgrind_pred2!(ct_fix__B__ct_eq__u32__N16, u32, 16);
ctgrind_pred2!(ct_fix__B__ct_eq__u64__N4, u64, 4);

ctgrind_pred2!(ct_fix__B__ct_gt__u8__N16, u8, 16);
ctgrind_pred2!(ct_fix__B__ct_gt__u16__N16, u16, 16);
ctgrind_pred2!(ct_fix__B__ct_gt__u32__N4, u32, 4);
ctgrind_pred2!(ct_fix__B__ct_gt__u32__N16, u32, 16);
ctgrind_pred2!(ct_fix__B__ct_gt__u64__N4, u64, 4);

ctgrind_pred2!(ct_fix__B__ct_lt__u8__N16, u8, 16);
ctgrind_pred2!(ct_fix__B__ct_lt__u16__N16, u16, 16);
ctgrind_pred2!(ct_fix__B__ct_lt__u32__N4, u32, 4);
ctgrind_pred2!(ct_fix__B__ct_lt__u32__N16, u32, 16);
ctgrind_pred2!(ct_fix__B__ct_lt__u64__N4, u64, 4);

// cond_select — (a, b, choice: u8) → out
ctgrind_cond_select!(ct_fix__B__cond_select__u8__N16, u8, 16);
ctgrind_cond_select!(ct_fix__B__cond_select__u16__N16, u16, 16);
ctgrind_cond_select!(ct_fix__B__cond_select__u32__N4, u32, 4);
ctgrind_cond_select!(ct_fix__B__cond_select__u32__N16, u32, 16);
ctgrind_cond_select!(ct_fix__B__cond_select__u64__N4, u64, 4);

// ct_checked_add / sub / mul — checked_bin shape
ctgrind_checked_bin!(ct_fix__B__ct_checked_add__u8__N16, u8, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_add__u16__N16, u16, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_add__u32__N4, u32, 4);
ctgrind_checked_bin!(ct_fix__B__ct_checked_add__u32__N16, u32, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_add__u64__N4, u64, 4);

ctgrind_checked_bin!(ct_fix__B__ct_checked_sub__u8__N16, u8, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_sub__u16__N16, u16, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_sub__u32__N4, u32, 4);
ctgrind_checked_bin!(ct_fix__B__ct_checked_sub__u32__N16, u32, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_sub__u64__N4, u64, 4);

ctgrind_checked_bin!(ct_fix__B__ct_checked_mul__u8__N16, u8, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_mul__u16__N16, u16, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_mul__u32__N4, u32, 4);
ctgrind_checked_bin!(ct_fix__B__ct_checked_mul__u32__N16, u32, 16);
ctgrind_checked_bin!(ct_fix__B__ct_checked_mul__u64__N4, u64, 4);

// ct_checked_shl / shr / pow — checked_scalar(u32) shape
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shl__u8__N16, u8, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shl__u16__N16, u16, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shl__u32__N4, u32, 4, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shl__u32__N16, u32, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shl__u64__N4, u64, 4, u32);

ctgrind_checked_scalar!(ct_fix__B__ct_checked_shr__u8__N16, u8, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shr__u16__N16, u16, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shr__u32__N4, u32, 4, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shr__u32__N16, u32, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_shr__u64__N4, u64, 4, u32);

ctgrind_checked_scalar!(ct_fix__B__ct_checked_pow__u8__N16, u8, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_pow__u16__N16, u16, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_pow__u32__N4, u32, 4, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_pow__u32__N16, u32, 16, u32);
ctgrind_checked_scalar!(ct_fix__B__ct_checked_pow__u64__N4, u64, 4, u32);

// ct_checked_npot
ctgrind_checked_un!(ct_fix__B__ct_checked_npot__u8__N16, u8, 16);
ctgrind_checked_un!(ct_fix__B__ct_checked_npot__u16__N16, u16, 16);
ctgrind_checked_un!(ct_fix__B__ct_checked_npot__u32__N4, u32, 4);
ctgrind_checked_un!(ct_fix__B__ct_checked_npot__u32__N16, u32, 16);
ctgrind_checked_un!(ct_fix__B__ct_checked_npot__u64__N4, u64, 4);

// forget_ct — unary
ctgrind_un!(ct_fix__B__forget_ct__u8__N16, u8, 16);
ctgrind_un!(ct_fix__B__forget_ct__u16__N16, u16, 16);
ctgrind_un!(ct_fix__B__forget_ct__u32__N4, u32, 4);
ctgrind_un!(ct_fix__B__forget_ct__u32__N16, u32, 16);
ctgrind_un!(ct_fix__B__forget_ct__u64__N4, u64, 4);
