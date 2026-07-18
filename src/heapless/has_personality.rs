//! `HasPersonality` projection for `HeaplessBigInt`.
//!
//! Mirrors `FixedUInt`'s `has_personality_impl.rs`: the carrier's
//! declared personality is its type parameter, so downstream personality
//! gates (`T: HasPersonality<P = Nct>`) resolve without naming the
//! carrier. This is what modmath's `NonCt` blanket-impl gates on.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{HasPersonality, Personality};

impl<T: MachineWord, const CAP: usize, P: Personality> HasPersonality
    for HeaplessBigInt<T, CAP, P>
{
    type P = P;
}
