//! Category A fixture registrations — mirror of ct-fixtures' cat_a.

use krabi_caliper::{ctgrind_bin, ctgrind_count, ctgrind_pred, ctgrind_shift, ctgrind_un};

// sat_add / sat_sub / sat_mul
ctgrind_bin!(ct_fix__A__sat_add__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__A__sat_add__u16__N16, u16, 16);
ctgrind_bin!(ct_fix__A__sat_add__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__A__sat_add__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__A__sat_add__u64__N4, u64, 4);

ctgrind_bin!(ct_fix__A__sat_sub__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__A__sat_sub__u16__N16, u16, 16);
ctgrind_bin!(ct_fix__A__sat_sub__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__A__sat_sub__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__A__sat_sub__u64__N4, u64, 4);

ctgrind_bin!(ct_fix__A__sat_mul__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__A__sat_mul__u16__N16, u16, 16);
ctgrind_bin!(ct_fix__A__sat_mul__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__A__sat_mul__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__A__sat_mul__u64__N4, u64, 4);

// shl<usize> / shr<usize>
ctgrind_shift!(ct_fix__A__shl_usize__u8__N16, u8, 16, usize);
ctgrind_shift!(ct_fix__A__shl_usize__u16__N16, u16, 16, usize);
ctgrind_shift!(ct_fix__A__shl_usize__u32__N4, u32, 4, usize);
ctgrind_shift!(ct_fix__A__shl_usize__u32__N16, u32, 16, usize);
ctgrind_shift!(ct_fix__A__shl_usize__u64__N4, u64, 4, usize);

ctgrind_shift!(ct_fix__A__shr_usize__u8__N16, u8, 16, usize);
ctgrind_shift!(ct_fix__A__shr_usize__u16__N16, u16, 16, usize);
ctgrind_shift!(ct_fix__A__shr_usize__u32__N4, u32, 4, usize);
ctgrind_shift!(ct_fix__A__shr_usize__u32__N16, u32, 16, usize);
ctgrind_shift!(ct_fix__A__shr_usize__u64__N4, u64, 4, usize);

// unbounded_shl / unbounded_shr — scalar is u32
ctgrind_shift!(ct_fix__A__unbounded_shl__u8__N16, u8, 16, u32);
ctgrind_shift!(ct_fix__A__unbounded_shl__u16__N16, u16, 16, u32);
ctgrind_shift!(ct_fix__A__unbounded_shl__u32__N4, u32, 4, u32);
ctgrind_shift!(ct_fix__A__unbounded_shl__u32__N16, u32, 16, u32);
ctgrind_shift!(ct_fix__A__unbounded_shl__u64__N4, u64, 4, u32);

ctgrind_shift!(ct_fix__A__unbounded_shr__u8__N16, u8, 16, u32);
ctgrind_shift!(ct_fix__A__unbounded_shr__u16__N16, u16, 16, u32);
ctgrind_shift!(ct_fix__A__unbounded_shr__u32__N4, u32, 4, u32);
ctgrind_shift!(ct_fix__A__unbounded_shr__u32__N16, u32, 16, u32);
ctgrind_shift!(ct_fix__A__unbounded_shr__u64__N4, u64, 4, u32);

// abs_diff
ctgrind_bin!(ct_fix__A__abs_diff__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__A__abs_diff__u16__N16, u16, 16);
ctgrind_bin!(ct_fix__A__abs_diff__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__A__abs_diff__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__A__abs_diff__u64__N4, u64, 4);

// is_pow2 / next_pow2
ctgrind_pred!(ct_fix__A__is_pow2__u8__N16, u8, 16);
ctgrind_pred!(ct_fix__A__is_pow2__u16__N16, u16, 16);
ctgrind_pred!(ct_fix__A__is_pow2__u32__N4, u32, 4);
ctgrind_pred!(ct_fix__A__is_pow2__u32__N16, u32, 16);
ctgrind_pred!(ct_fix__A__is_pow2__u64__N4, u64, 4);

ctgrind_un!(ct_fix__A__next_pow2__u8__N16, u8, 16);
ctgrind_un!(ct_fix__A__next_pow2__u16__N16, u16, 16);
ctgrind_un!(ct_fix__A__next_pow2__u32__N4, u32, 4);
ctgrind_un!(ct_fix__A__next_pow2__u32__N16, u32, 16);
ctgrind_un!(ct_fix__A__next_pow2__u64__N4, u64, 4);

// leading_zeros / trailing_zeros
ctgrind_count!(ct_fix__A__leading_zeros__u8__N16, u8, 16);
ctgrind_count!(ct_fix__A__leading_zeros__u16__N16, u16, 16);
ctgrind_count!(ct_fix__A__leading_zeros__u32__N4, u32, 4);
ctgrind_count!(ct_fix__A__leading_zeros__u32__N16, u32, 16);
ctgrind_count!(ct_fix__A__leading_zeros__u64__N4, u64, 4);

ctgrind_count!(ct_fix__A__trailing_zeros__u8__N16, u8, 16);
ctgrind_count!(ct_fix__A__trailing_zeros__u16__N16, u16, 16);
ctgrind_count!(ct_fix__A__trailing_zeros__u32__N4, u32, 4);
ctgrind_count!(ct_fix__A__trailing_zeros__u32__N16, u32, 16);
ctgrind_count!(ct_fix__A__trailing_zeros__u64__N4, u64, 4);

// is_zero / is_one
ctgrind_pred!(ct_fix__A__is_zero__u8__N16, u8, 16);
ctgrind_pred!(ct_fix__A__is_zero__u16__N16, u16, 16);
ctgrind_pred!(ct_fix__A__is_zero__u32__N4, u32, 4);
ctgrind_pred!(ct_fix__A__is_zero__u32__N16, u32, 16);
ctgrind_pred!(ct_fix__A__is_zero__u64__N4, u64, 4);

ctgrind_pred!(ct_fix__A__is_one__u8__N16, u8, 16);
ctgrind_pred!(ct_fix__A__is_one__u16__N16, u16, 16);
ctgrind_pred!(ct_fix__A__is_one__u32__N4, u32, 4);
ctgrind_pred!(ct_fix__A__is_one__u32__N16, u32, 16);
ctgrind_pred!(ct_fix__A__is_one__u64__N4, u64, 4);
