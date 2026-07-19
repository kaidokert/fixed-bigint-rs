//! Category C fixture registrations — mirror of ct-fixtures' cat_c.

use krabi_caliper::{ctgrind_bin, ctgrind_carrying_add, ctgrind_count, ctgrind_un};

// Bitwise — not is unary, and/or/xor are binary.
ctgrind_un!(ct_fix__C__not__u8__N16, u8, 16);
ctgrind_un!(ct_fix__C__not__u32__N4, u32, 4);
ctgrind_un!(ct_fix__C__not__u32__N16, u32, 16);
ctgrind_un!(ct_fix__C__not__u64__N4, u64, 4);

ctgrind_bin!(ct_fix__C__bitand__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__C__bitand__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__C__bitand__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__C__bitand__u64__N4, u64, 4);

ctgrind_bin!(ct_fix__C__bitor__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__C__bitor__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__C__bitor__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__C__bitor__u64__N4, u64, 4);

ctgrind_bin!(ct_fix__C__bitxor__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__C__bitxor__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__C__bitxor__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__C__bitxor__u64__N4, u64, 4);

// overflowing_add / wrapping_mul — binary, overflow bool discarded
ctgrind_bin!(ct_fix__C__overflowing_add__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__C__overflowing_add__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__C__overflowing_add__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__C__overflowing_add__u64__N4, u64, 4);

ctgrind_bin!(ct_fix__C__wrapping_mul__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__C__wrapping_mul__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__C__wrapping_mul__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__C__wrapping_mul__u64__N4, u64, 4);

// carrying_add — (a, b, carry: bool, out) → u8
ctgrind_carrying_add!(ct_fix__C__carrying_add__u8__N16, u8, 16);
ctgrind_carrying_add!(ct_fix__C__carrying_add__u32__N4, u32, 4);
ctgrind_carrying_add!(ct_fix__C__carrying_add__u32__N16, u32, 16);
ctgrind_carrying_add!(ct_fix__C__carrying_add__u64__N4, u64, 4);

// midpoint — binary
ctgrind_bin!(ct_fix__C__midpoint__u8__N16, u8, 16);
ctgrind_bin!(ct_fix__C__midpoint__u32__N4, u32, 4);
ctgrind_bin!(ct_fix__C__midpoint__u32__N16, u32, 16);
ctgrind_bin!(ct_fix__C__midpoint__u64__N4, u64, 4);

// count_ones — count shape
ctgrind_count!(ct_fix__C__count_ones__u8__N16, u8, 16);
ctgrind_count!(ct_fix__C__count_ones__u32__N4, u32, 4);
ctgrind_count!(ct_fix__C__count_ones__u32__N16, u32, 16);
ctgrind_count!(ct_fix__C__count_ones__u64__N4, u64, 4);

// swap_bytes / reverse_bits — unary
ctgrind_un!(ct_fix__C__swap_bytes__u8__N16, u8, 16);
ctgrind_un!(ct_fix__C__swap_bytes__u32__N4, u32, 4);
ctgrind_un!(ct_fix__C__swap_bytes__u32__N16, u32, 16);
ctgrind_un!(ct_fix__C__swap_bytes__u64__N4, u64, 4);

ctgrind_un!(ct_fix__C__reverse_bits__u8__N16, u8, 16);
ctgrind_un!(ct_fix__C__reverse_bits__u32__N4, u32, 4);
ctgrind_un!(ct_fix__C__reverse_bits__u32__N16, u32, 16);
ctgrind_un!(ct_fix__C__reverse_bits__u64__N4, u64, 4);
