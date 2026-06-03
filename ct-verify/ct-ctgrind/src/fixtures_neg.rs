//! Negative-control registrations — mirror of ct-fixtures' fixtures_neg.

use crate::{ctgrind_bin, ctgrind_count};

// nct_div — bin shape
ctgrind_bin!(nct_fix__neg__nct_div__u32__N4, u32, 4);
ctgrind_bin!(nct_fix__neg__nct_div__u32__N16, u32, 16);

// nct_ilog10 — count shape (takes (a) returns u32)
ctgrind_count!(nct_fix__neg__nct_ilog10__u32__N4, u32, 4);

// nct_gcd — bin shape
ctgrind_bin!(nct_fix__neg__nct_gcd__u32__N4, u32, 4);
