//! Wrapping addition, as a ripple-carry adder. The carry into position `i + 1`
//! is `maj(a_i, b_i, c_i) = (a_i ⊕ c_i)(b_i ⊕ c_i) ⊕ c_i`, one product, and every
//! other wire is affine, so the circuit pays 63 products: the carry out of bit
//! 63 falls off the modulus. The witness is the native sum, whose carries are
//! `(a + b) ⊕ a ⊕ b`.

use super::{Builder, Instance};

/// The carries into bits 1 to 63.
const CARRIES: u128 = (u64::MAX >> 1) as u128;

pub(super) struct Adder {
    /// The first of the carries' 63 product slots.
    slot: usize,
}

impl Adder {
    pub(super) fn build(c: &mut Builder) -> Self {
        let slot = c.next_slot;
        let mut carry = None;
        for i in 0..64 {
            let (a, b) = (c.a[i], c.b[i]);
            let ac = c.xor(a, carry);
            let bc = c.xor(b, carry);
            let out = c.xor(ac, b);
            c.output(i, out);
            if i < 63 {
                let maj = c.and(ac, bc);
                carry = c.xor(Some(maj), carry);
            }
        }
        Self { slot }
    }

    /// Writes the carries' rows and returns the result.
    pub(super) fn witness(&self, a: u64, b: u64, witness: &mut Instance) -> u128 {
        let sum = a.wrapping_add(b);
        let carry_in = sum ^ a ^ b;
        witness.products(self.slot, CARRIES, (a ^ carry_in) as u128, (b ^ carry_in) as u128);
        sum as u128
    }
}
