// Temporary diagnostic (see CI_BASELINE_PROBE.md). Monomorphizes
// FixedUInt<u32,4>'s const_num_traits::ToBytes under the `nightly`
// (generic_const_exprs) feature — the exact call the local run hit
// E0275 on. On main + crates.io const-num-traits, this tells us whether
// that overflow is a latent library defect or something downstream.
#![cfg(feature = "nightly")]
use const_num_traits::ToBytes;
use fixed_bigint::FixedUInt;

#[test]
fn probe_fixeduint_u32x4_const_tobytes() {
    let f = FixedUInt::<u32, 4>::from(0x1234_5678u32);
    let bytes = <FixedUInt<u32, 4> as ToBytes>::to_be_bytes(f);
    assert_eq!(bytes.as_ref().len(), 16);
}
