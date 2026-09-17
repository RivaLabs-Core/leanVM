//! The g-power table and its reverse index, which the machine grows on demand.

use primitives::field::F64;

/// The `g^k` table paired with a reverse index `g^k ↦ k`, both grown on demand
/// (call depth, and so the address range, is unbounded).
///
/// The interpreter needs both directions: a cell index becomes the address `g^k`,
/// and a pointer word read back out of memory must be inverted to the index it
/// addresses. Two things keep this cheap.
///
/// The reverse index holds nothing but the exponent, confirming a candidate slot
/// against the forward table, so a slot is four bytes where a `HashMap` bucket is
/// sixteen plus a control byte. Keys are field elements, hence effectively
/// uniform, which is all the placement asks for: one multiplicative mix, then
/// linear probing. The table stays at most half full to keep probing short.
///
/// And it indexes only the exponents [`Self::note`] announces: a run addresses
/// millions of cells but stores only the few thousand bases of its frames and
/// buffers, and one random write per addressable cell into a table far too large
/// for cache is what building the whole inverse costs. A lookup that misses the
/// announced set indexes everything and retries, so an address arriving by a
/// route the interpreter cannot label is slow, never wrong.
#[derive(Default)]
pub struct GPow {
    pow: Vec<F64>,
    /// The announced exponents, so widening rebuilds from them rather than
    /// scanning the old table.
    noted: Vec<u32>,
    /// `k + 1` at the slot `g^k` mixes to; 0 marks an empty slot. Power-of-two
    /// length.
    index: Vec<u32>,
    /// Set once a lookup missed: every exponent is announced from then on.
    dense: bool,
}

impl GPow {
    /// Seeded with `g^0 = 1`, grown to cover index `upto` or the smallest memory
    /// size, whichever is larger, with every exponent up to there announced.
    /// Callers pass the bytecode size, which bounds the pcs and the return
    /// targets; the memory floor covers the small powers a range check compares
    /// against, which point anywhere below their bound rather than at an
    /// allocation (§Memory).
    pub fn new(upto: usize) -> Self {
        let upto = upto.max(1 << super::MIN_LOG_MEM);
        let mut g = Self::default();
        g.pow.push(F64::ONE);
        g.grow_to(upto);
        g.index = vec![0; (2 * (upto + 1)).next_power_of_two().max(1 << 13)];
        g.noted.reserve((upto + 1).next_power_of_two());
        for k in 0..=upto {
            g.note(k);
        }
        g
    }

    /// `g^k`. Panics past the grown range, which is the honest outcome: every
    /// index the interpreter reads has been covered by a [`Self::grow_to`].
    #[inline(always)]
    pub fn pow(&self, k: usize) -> F64 {
        self.pow[k]
    }

    /// One past the largest index the forward table covers.
    #[inline(always)]
    pub fn covered(&self) -> usize {
        self.pow.len()
    }

    /// Extend the forward table to cover index `upto`.
    pub fn grow_to(&mut self, upto: usize) {
        assert!(upto < (1 << 28), "address space overflow (program too large)");
        while self.pow.len() <= upto {
            // ×g is ×x = `mul_by_g` (shift+fold), not a PMULL.
            let next = primitives::field::mul_by_g(*self.pow.last().unwrap());
            self.pow.push(next);
            if self.dense {
                self.note(self.pow.len() - 1);
            }
        }
    }

    /// Announce that `g^k` may come back for inversion, because the interpreter
    /// is about to store it in memory as an address. Idempotent.
    pub fn note(&mut self, k: usize) {
        if self.noted.len() * 2 >= self.index.len() {
            self.widen();
        }
        let mask = self.index.len() - 1;
        let mut i = slot_of(self.pow[k].0, mask);
        loop {
            let e = self.index[i];
            if e == 0 {
                break;
            }
            // Exponents are distinct (`g` has order `2^64 − 1`), so finding `k`
            // along its own probe chain means it is already announced.
            if e - 1 == k as u32 {
                return;
            }
            i = (i + 1) & mask;
        }
        self.index[i] = k as u32 + 1;
        self.noted.push(k as u32);
    }

    /// The discrete log of `x`, if it is a covered g-power.
    #[inline]
    pub fn log(&mut self, x: F64) -> Option<u32> {
        if let Some(k) = self.lookup(x) {
            return Some(k);
        }
        // Announced exponents are distinct and below `pow.len()`, so an equal
        // count means the whole range is already announced and there is nothing
        // a dense pass could add.
        if self.dense || self.noted.len() == self.pow.len() {
            return None;
        }
        // An address the interpreter never announced: index the lot and retry.
        self.dense = true;
        self.noted = (0..self.pow.len() as u32).collect();
        self.widen();
        self.lookup(x)
    }

    #[inline]
    fn lookup(&self, x: F64) -> Option<u32> {
        let mask = self.index.len() - 1;
        let mut i = slot_of(x.0, mask);
        loop {
            let e = self.index[i];
            if e == 0 {
                return None;
            }
            if self.pow[(e - 1) as usize] == x {
                return Some(e - 1);
            }
            i = (i + 1) & mask;
        }
    }

    /// Rebuild the index at a size that holds `noted` at most half full.
    fn widen(&mut self) {
        let cap = (self.noted.len() * 2 + 1).next_power_of_two().max(1 << 13);
        let mut index = vec![0u32; cap];
        let mask = cap - 1;
        for &k in &self.noted {
            let mut i = slot_of(self.pow[k as usize].0, mask);
            while index[i] != 0 {
                i = (i + 1) & mask;
            }
            index[i] = k + 1;
        }
        self.index = index;
    }
}

/// Bits 32..64 of the mix are the well-distributed ones; the mask keeps as many
/// of them as the table is wide.
#[inline(always)]
fn slot_of(key: u64, mask: usize) -> usize {
    (key.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize & mask
}
