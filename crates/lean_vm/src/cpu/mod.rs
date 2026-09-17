//! Whole-program assembly over GF(2^64) (`doc/leanvm/main.tex`): the instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g. A memory word is one
//! `K = F64` element; `XOR192`/`MUL192` compute in `E = F192 = K[y]/(y³+y+1)` over
//! three consecutive cells. `BLAKE2s` adds the memory/state/bytecode plumbing for a
//! 64→32-byte compression whose relation is discharged by flock (see
//! [`crate::hash_flock`]). Challenges and transcript scalars live in `E`.

use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE2S, OP_DEREF, OP_JUMP, OP_MUL64, OP_SET, OP_XOR64, SEP_BYTECODE, SEP_MEM,
    SEP_STATE,
};
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use crate::witness;
use primitives::field::{F64, F192, g_pow};

mod execute;
pub mod filler;
mod gpow;
mod isa;
pub mod layout;
mod trace;
pub use execute::Execution;
pub use isa::{DerefMode, Op};
pub use layout::*;
pub(crate) use trace::{Access, Brow, Drow, Jrow, Srow, Trace, Xrow};

/// Witness-gen `BLAKE2s` compression: the eight message words laid out
/// little-endian into 64 bytes, combined with the supplied chaining value and
/// metadata, and the 32-byte result split back into four words. Flock proves this
/// same compression relation ([`crate::hash_flock`]).
fn blake2s_compress(va: [F64; 4], vb: [F64; 4], vcv: [F64; 4], metadata: [F64; 2]) -> [F64; 4] {
    crate::hash_flock::digest(&crate::hash_flock::compression(va, vb, vcv, metadata))
}

/// Data-memory size bounds (doc §Memory): memory is `2^h` cells with
/// `MIN_LOG_MEM ≤ h ≤ MAX_LOG_MEM`. The prover pads up to the minimum; the
/// verifier rejects any announced `h` outside the range.
pub const MIN_LOG_MEM: usize = 16;
const MAX_LOG_MEM: usize = 32;

/// Each per-opcode table holds at most `2^MAX_LOG_ROWS` rows (executed
/// instructions of that opcode). Together with `MAX_LOG_MEM` and the bytecode
/// cap these are the instance caps from “Counts must not wrap” in `doc/leanvm/body/06-memory-and-bytecode-lookups.tex`: at `ord(g) = 2^64−1`
/// the memory-soundness and count-non-wrap counting arguments are theorems only
/// for instances whose total read-flush count stays far below `2^64`, so the
/// verifier rejects any announcement exceeding them before running a reduction.
const MAX_LOG_ROWS: usize = 32;

/// Bytecode-length instance cap (see [`MAX_LOG_ROWS`]): programs are at most
/// `2^32` instructions.
const MAX_LOG_BYTECODE: usize = 32;

/// The Fiat-Shamir IV: ONE 32-byte digest, as its four words, committing to
/// everything fixed about the proving environment.
///
/// Two things go in. [`flock::hash::R1CS_DIGEST`] names the flock BLAKE2s
/// circuit, independent of the instance count: the full instance is
/// block-diagonal and the count is announced and absorbed with the other sizes,
/// so one constant covers every shape. And the bytecode enters through the hash
/// cached on `Program`, BLAKE2s over the stacked multilinear
/// ([`layout::bytecode_table`]) rather than over an assembler digest, so a
/// verifier holding only that polynomial reproduces the seed; that inner hash is
/// cached, so the table is walked once per program rather than once per proof.
///
/// The IV IS the transcript's starting chaining value ([`fiat_shamir::FiatShamirState::new`]),
/// so all challenges depend on the circuit version and the program before
/// anything else.
pub fn fs_seed(program: &Program) -> [F64; 4] {
    let mut h = primitives::hash::Hasher::new();
    h.update(b"leanvm");
    // Length-framed so the preimage parses one way: the domain and the bytecode
    // hash are fixed-width, so framing the digest between them is all it takes.
    h.update(&(flock::hash::R1CS_DIGEST.len() as u64).to_le_bytes());
    h.update(&flock::hash::R1CS_DIGEST);
    h.update(&program.bytecode_hash);
    fiat_shamir::digest_words(&h.finalize())
}

/// Announce the prover's sizes (`log_mem`, every table's log height, the PCS rate)
/// by writing them onto the scalar stream, which binds them into the state and lets
/// the verifier reconstruct the layout. The public statement (program + input) is not
/// announced here; it seeds the transcript at construction (see [`fs_seed`]).
/// The boundary states are derived from the program, so they need no binding.
///
/// Log heights, not row counts: every table's rows are real rows, the fill blocks
/// having run each count up to a power of two (`filler`), so a height is all there is
/// to say. That also spares both sides a `log2_ceil`, which
/// in-circuit is a bit decomposition against a hinted exponent rather than a shift.
fn announce_public(
    ps: &mut ProverState,
    log_mem: usize,
    taus: [usize; tables::N_TABLES],
    log_inv_rate: usize,
    ts_final: F64,
) {
    ps.add_scalar(F192::new(log_mem as u64, 0, 0));
    for t in taus {
        ps.add_scalar(F192::new(t as u64, 0, 0));
    }
    ps.add_scalar(F192::new(log_inv_rate as u64, 0, 0));
    // The clock the run ended on: the final state's timestamp (§sec:state).
    ps.add_scalar(F192::from(ts_final));
}

/// Verifier side of [`announce_public`]: read the announced sizes and PCS
/// rate from the stream, validate them, and reconstruct the public [`Layout`]
/// from the program + sizes + public input. (The public input was already bound
/// by seeding the transcript.)
fn read_public(vs: &mut VerifierState, prog: &Program, public_input: &[F64; 4]) -> Result<(Layout, usize), CpuError> {
    let read_size = |vs: &mut VerifierState| -> Result<usize, CpuError> {
        let word = vs.next_scalar().map_err(CpuError::Transcript)?;
        if word.c1 != 0 || word.c2 != 0 {
            return Err(CpuError::PublicInput);
        }
        usize::try_from(word.c0).map_err(|_| CpuError::PublicInput)
    };

    let log_mem = read_size(vs)?;
    let mut taus = [0usize; tables::N_TABLES];
    for t in &mut taus {
        *t = read_size(vs)?;
    }
    let log_inv_rate = read_size(vs)?;
    let ts_final = vs.next_scalar().map_err(CpuError::Transcript)?;
    if ts_final.c1 != 0 || ts_final.c2 != 0 {
        return Err(CpuError::PublicInput);
    }
    // The public instance caps ensure that, with `ord(g) = 2^64 − 1`, the
    // counting arguments (memory soundness, count non-wrap, exponent range checks)
    // are theorems only when the announced instance keeps the total read-flush
    // count provably below `2^64 − 1`, so reject any announcement exceeding the
    // caps BEFORE running any reduction. (A table's row count is the number of
    // times its opcode runs, unbounded by the bytecode size since a small loop
    // body runs many times, so it gets its own cap, not `bytecode_size`.)
    let bytecode_size = prog.prog.len();
    if !bytecode_size.is_power_of_two()
        || bytecode_size > (1usize << MAX_LOG_BYTECODE)
        || !(MIN_LOG_MEM..=MAX_LOG_MEM).contains(&log_mem)
        || taus.iter().any(|&t| t > MAX_LOG_ROWS)
        // flock sizes its argument to at least `n_blocks_log(1)` instances, and the
        // BLAKE2s table's value columns share that instance cube, so a height below the
        // floor describes a layout the arithmetization cannot express. `python-verifier`
        // rejects it here too.
        || taus[tables::BLAKE2S_TABLE] < crate::hash_flock::n_blocks_log(1)
        || U64_OPS
            .iter()
            .any(|&op| taus[tables::u64_table(op)] < crate::arith_flock::n_blocks_log(op, 1))
        || ::pcs::whir::validate_log_inv_rate(log_inv_rate).is_err()
    {
        return Err(CpuError::PublicInput);
    }
    let l = layout(&prog.prog, log_mem, taus, *public_input, F64(ts_final.c0));
    // The caps bound each announced log on its own; what the PCS is configured for
    // is the stacked size they imply, which they do not bound.
    if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&l.shape.mu) {
        return Err(CpuError::PublicInput);
    }
    Ok((l, log_inv_rate))
}

#[derive(Clone)]
pub struct Program {
    pub prog: Vec<Op>, // bytecode (size B, power of two)
    /// BLAKE2s over the stacked bytecode multilinear, computed once at assembly
    /// so proving and verifying the same program do not rehash it (that table is
    /// 16·2^kbc words, tens of megabytes at production sizes). Trusted to match
    /// `prog`: always set by [`Program::assemble`] from the bytecode, so a
    /// `Program` cannot carry a hash inconsistent with its own `prog`.
    pub(crate) bytecode_hash: [u8; 32],
    /// The padding blocks in the bytecode ([`filler`]), whose rows bring every
    /// table's row count to a power of two. Prover-side only, and no program code
    /// reaches them, so a missing or wrong entry costs the prover a run that does not
    /// fill rather than anything a verifier would accept.
    pub filler: Vec<filler::Block>,
}

/// The bytecode digest reinterprets the stacked table as bytes, which is its
/// `to_le_bytes` image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// Assemble a [`Program`] from a whole bytecode, computing its digest. The
    /// single funnel for construction, so the digest is always consistent with the
    /// bytecode. `prog.len()` must be a power of two with a never-executed sentinel
    /// in its last slot: the run halts on reaching `g^{len-1}` (§sec:state).
    pub fn assemble(prog: Vec<Op>) -> Self {
        let bytecode_hash = {
            let table = layout::bytecode_table(&prog);
            // SAFETY: F64 is #[repr(transparent)] over u64, so the slice's byte image is
            // exactly the concatenation of its `to_le_bytes` on little-endian targets.
            let bytes: &[u8] =
                unsafe { core::slice::from_raw_parts(table.as_ptr().cast::<u8>(), core::mem::size_of_val(&table[..])) };
            primitives::hash::Hasher::new().update(bytes).finalize()
        };
        Self {
            prog,
            bytecode_hash,
            filler: Vec::new(),
        }
    }

    /// Assemble a program from its instructions alone, to be run in frame 0 over
    /// `frame_cells` cells, the first four of them the public words.
    ///
    /// `body` runs from its first instruction and halts by falling off its end. What
    /// is appended takes it from there: a jump to the halt sentinel through two cells
    /// past the frame, the padding blocks ([`filler`]), and the fill up to a power of
    /// two that ends on the never-executed sentinel (§sec:state).
    pub fn from_body(mut body: Vec<Op>, frame_cells: u32) -> Self {
        let (dest, frame) = (frame_cells, frame_cells + 1);
        let halt = body.len();
        body.extend([Op::Set { o: 0, k: F64::ZERO }; 2]); // patched below
        body.push(Op::Jump {
            oc: dest,
            od: dest,
            of: frame,
        });
        let blocks = filler::append_blocks(&mut body);
        let len = (body.len() + 1).next_power_of_two();
        body.resize(len, Op::Xor64 { a: 0, b: 0, c: 0 });
        body[halt] = Op::Set {
            o: dest,
            k: g_pow(len - 1),
        };
        body[halt + 1] = Op::Set { o: frame, k: F64::ONE };
        let mut program = Self::assemble(body);
        program.filler = blocks;
        program
    }
}

/// The whole proof is the transcript: a scalar stream plus the PCS hint
/// channels (see [`crate::transcript::Proof`]).
pub use crate::transcript::Proof;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CpuError {
    Bus(leaf::Error),
    Constraint(constraints::Error),
    Open(pcs::Error),
    PublicInput,
    Transcript(crate::transcript::Error),
    /// flock's BLAKE2s R1CS validity sub-proof failed to verify. (A missing or
    /// malformed sub-proof surfaces as [`CpuError::Transcript`] when the shared
    /// `stream`/`openings` fail to reconstruct or fully consume.)
    Blake2s(flock::verifier::VerifyError),
    /// Flock's reduction for `ADD_U64` or `MUL_U64`.
    U64(flock::verifier::VerifyError),
}

/// Per side, which table (if any) owns each bus block, as `(table, column base)`.
type BlockOwners = [Vec<Option<(usize, usize)>>; 3];
/// Each table's `(column base, committed column count)` in the global schema.
type TableSpans = Vec<(usize, usize)>;

/// Blocks sourced from a table's height belong to it; the boundary, memory and
/// bytecode blocks belong to none and keep their own column claims at ζ.
fn block_owners(log_bytecode: usize, sides: [usize; 3]) -> BlockOwners {
    let sch = schema();
    let src = block_kappa_sources(log_bytecode);
    let mut it = src
        .into_iter()
        .map(|(source, _)| source.checked_sub(2).map(|t| (t, sch.base[t])));
    sides.map(|n| it.by_ref().take(n).collect())
}

/// The bus's public wiring: per side which table owns each block, and each table's
/// column span. Derived from the program and the announced layout alone, so prover
/// and verifier build it identically.
fn bus_wiring(program: &Program, l: &Layout) -> (BlockOwners, TableSpans) {
    let owners = block_owners(
        crate::log2_strict_usize(program.prog.len()),
        [l.push.len(), l.pull.len(), l.count.len()],
    );
    (owners, table_spans())
}

/// The table sumcheck carries every committed column of a table, because its bus
/// forms reference the flushed ones and its constraint the rest.
fn table_spans() -> TableSpans {
    let sch = schema();
    tables::tables()
        .iter()
        .enumerate()
        .map(|(t, tb)| (sch.base[t], tb.n_committed_columns()))
        .collect()
}

/// The per-table inputs to the table sumcheck (§constraints), in schema order.
/// Prover and verifier both call this, so their column order and constraint
/// closures agree by construction.
/// The airs carry every committed column of their table, so a constraint indexes the
/// value array directly and each table's three bus forms can be
/// evaluated on the same values. The identities take the air's own `η`-range; the
/// three forms take the shared powers at [`xi_form_base`], folded into the forms'
/// coefficients once rather than multiplied onto every row's form value.
fn airs(taus: &[usize; tables::N_TABLES], forms: &[Vec<leaf::BusForm>; 3], xi: F192) -> Vec<constraints::Air<'static>> {
    let form_pows = xi_form_pows(xi);
    // Each table's slice of the batch's `η`-powers, exactly as `constraints` cuts
    // them, turned into the weights its identities want once rather than per row.
    let pows = primitives::field::powers(xi, xi_form_base());
    let offsets = constraints::xi_offsets(tables::tables().iter().map(|t| t.n_constraints()));
    tables::tables()
        .iter()
        .zip(taus)
        .enumerate()
        .map(|(t, (&table, &tau))| {
            let weights = table.constraint_weights(&pows[offsets[t]..offsets[t] + table.n_constraints()]);
            let weights_k = weights.clone();
            // One form, not three: the batch adds the three sides' evaluations
            // anyway, and summing them here is a setup cost against a dot product
            // and a product list per row per node.
            let bus = leaf::BusForm::sum((0..3).map(|s| forms[s][t].scaled(form_pows[s])));
            let bus_k = bus.clone();
            constraints::Air {
                tau,
                n_cols: table.n_committed_columns(),
                n_constraints: table.n_constraints(),
                eval: Box::new(move |_, vals, quadratic| {
                    let air = <F192 as ColVal>::lift(table.eval_constraint(&weights, vals, quadratic));
                    <F192 as ColVal>::reduce(air ^ bus.eval_unreduced(vals, quadratic))
                }),
                // The same expression over K columns: the identity's K-only products
                // stay 64-bit and the bus form becomes a mixed dot product.
                eval_k: Box::new(move |_, vals, quadratic| {
                    let air = <F64 as ColVal>::lift(table.eval_constraint_k(&weights_k, vals, quadratic));
                    <F64 as ColVal>::reduce(air ^ bus_k.eval_unreduced(vals, quadratic))
                }),
            }
        })
        .collect()
}

/// Each table's claimed sum: its identities vanish, so what its summand comes to
/// is its three bus forms, `η`-weighted. Prover-side only, to build the waiting
/// line each round; the verifier needs just their total, which it derives.
fn sigmas(bus: &[Vec<F192>; 3], form_pows: [F192; 3]) -> Vec<F192> {
    (0..tables::tables().len())
        .map(|t| (0..3).fold(F192::ZERO, |acc, s| acc + form_pows[s] * bus[s][t]))
        .collect()
}

/// Where the three bus forms sit in the batch's `η`-powers: the last three, AFTER
/// every table's identity range, and shared by all tables rather than one triple
/// per table. That sharing is what keeps the batch tied to the bus: with a common
/// `η^{base+s}` per side, the batch's target is `Σ_s η^{FORM_POWS+s}·R_s` for
/// the sides' table shares `R_s`, which the verifier DERIVES from the leaf claims
/// (`xi_form_pows`; a mismatch surfaces as [`CpuError::Constraint`]). Were the
/// powers per table, the target
/// would not factor through the `R_s` and nothing would pin the tables' share of
/// the bus.
pub fn xi_form_base() -> usize {
    tables::tables().iter().map(|t| t.n_constraints()).sum()
}

/// The three shared form powers `η^{base}, η^{base+1}, η^{base+2}`.
fn xi_form_pows(xi: F192) -> [F192; 3] {
    let base = xi_form_base();
    let pows = primitives::field::powers(xi, base + 3);
    [pows[base], pows[base + 1], pows[base + 2]]
}

/// If `col` is a flock-backed **value** column (global index), where its words
/// live: the committed packed witness, the within-instance slot, and the stride
/// between instances. These columns are virtual (uncommitted): their memory-bus
/// evaluation claims are re-routed to slot evaluations of that witness, which is
/// the whole binding: the bus-tied value IS the flock-proven word, no separate
/// check needed.
fn flock_value_slot(col: usize) -> Option<(usize, usize, usize)> {
    let sch = schema();
    let find = |table: usize, cols: &[usize]| cols.iter().position(|&c| sch.base[table] + c == col);
    if let Some(i) = find(tables::BLAKE2S_TABLE, &tables::BLAKE2S_VALUE_COLS) {
        return Some((QFLOCK, crate::hash_flock::SLOTS[i], crate::hash_flock::SLOT_STRIDE_LOG));
    }
    U64_OPS.iter().find_map(|&op| {
        find(tables::u64_table(op), &tables::U64_VALUE_COLS)
            .map(|i| (u64_column(op), crate::arith_flock::SLOTS[i], op.stride_log()))
    })
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts in [`Stats::TABLES`] order, and the
/// committed witness size, the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize, // including the padding to make every instruction count a power of two
    /// Rows per table as proven: each an exact power of two, the fill blocks having
    /// filled them (`filler`).
    pub counts: [usize; tables::N_TABLES],
    /// Rows per table before that filling, i.e. the work the program itself does.
    /// What a cost measurement wants.
    pub base_counts: [usize; tables::N_TABLES],
    pub committed: usize,
    /// Data memory is `2^log_mem` cells (the padded image).
    pub log_mem: usize,
    /// Cells actually touched, before the pad to `2^log_mem`, i.e. the real memory
    /// footprint (`log2` is fractional).
    pub mem_used: usize,
}

impl Stats {
    /// Table names in `counts` order.
    pub const TABLES: [&'static str; tables::N_TABLES] = [
        "XOR64", "MUL64", "SET", "DEREF", "JUMP", "BLAKE2S", "ADD_U64", "MUL_U64",
    ];

    /// One line of per-table instruction counts and shares, largest first, followed by memory and committed-witness sizes.
    ///
    /// The counts are `base_counts`, the work the program itself does, since the proven
    /// `counts` are all exact powers of two once the fill blocks have run (`filler`) and
    /// so say nothing about the workload.
    /// `log_mem` holds the padded memory size the commitment covers. Zero-count
    /// tables are omitted.
    #[must_use]
    pub fn details(&self) -> String {
        if self.cycles == 0 {
            return "-".to_string();
        }
        let base_cycles: usize = self.base_counts.iter().sum();
        let mut shares: Vec<(&str, usize)> = Self::TABLES
            .iter()
            .zip(&self.base_counts)
            .filter(|&(_, &c)| c > 0)
            .map(|(&name, &c)| (name, c))
            .collect();
        shares.sort_unstable_by_key(|&(_, c)| std::cmp::Reverse(c));
        let mut parts: Vec<String> = shares
            .iter()
            .map(|&(name, c)| {
                let pct = 100.0 * c as f64 / base_cycles as f64;
                format!("{name} 2^{} ({pct:.1}%)", primitives::pretty_f64((c as f64).log2()))
            })
            .collect();
        let log2 = |n: usize| primitives::pretty_f64((n.max(1) as f64).log2());
        parts.push(format!("MEMORY 2^{}", log2(self.mem_used)));
        parts.push(format!("TOTAL_COMMITTED 2^{}", log2(self.committed)));
        parts.join("  ")
    }
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`]. `log_inv_rate` selects the PCS rate and is announced in the
/// Fiat-Shamir transcript before the commitment.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(program: &Program, public_input: [F64; 4], log_inv_rate: usize) -> (Proof, Stats) {
    ::pcs::whir::validate_log_inv_rate(log_inv_rate).expect("valid log_inv_rate");
    // One proof is one arena phase: every transient buffer below is bump-allocated
    // and reclaimed wholesale here, rather than faulted in and unmapped again per
    // proof. Bound first so it outlives them; inert unless `init_prover` opted in.
    // The returned `Proof` is system-allocated (`ps.into_proof()` builds `Vec`s),
    // so it survives the next phase.
    let _phase = zk_alloc::enter_phase();
    let exec = crate::stage!("Execute program", || program.execute(public_input));
    prove_execution(program, &exec, public_input, log_inv_rate)
}

/// [`prove`] from a finished run. Split out so a test can hand it a run no honest
/// machine produced.
fn prove_execution(program: &Program, exec: &Execution, public_input: [F64; 4], log_inv_rate: usize) -> (Proof, Stats) {
    let cycles = exec.cycles;
    let w = crate::stage!("Build witness", || program.build(exec));
    let counts = w.layout.taus.map(|t| 1usize << t);
    let committed_size = w.committed_size();
    // The public statement (program digest + input) seeds the transcript, so
    // every challenge depends on the exact program and public input.
    let mut ps = ProverState::new(fs_seed(program), public_input);

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.log_mem, w.layout.taus, log_inv_rate, w.ts_final);
    let committed = crate::stage!("Commit", || {
        pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate)
    });

    // BLAKE2s to flock (§hash_flock), single PCS: q_flock is ALWAYS a column in
    // `w.q` (≥1 instance, a program with no BLAKE2s carries one padding instance,
    // so the proof shape is uniform and there is no has/hasn't-BLAKE2s fork). flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE
    // WHIR over this commitment (below). Message, chaining-value, and output words
    // bind through the memory bus; counter and flags bind through bytecode. Their
    // virtual value columns route to q_flock, so no separate pin claims are needed.
    // Mirrored in `verify`.
    let (owners, spans) = bus_wiring(program, &w.layout);
    // The columns are windows into `w.q`, so both stages read them in place: the
    // table sumcheck lifts each K-column into a fresh `E` copy on the round it
    // joins and never writes the K-columns back.
    let (bus, table_claims) = {
        let l = &w.layout;
        let cols = w.columns();
        let bus = crate::stage!("Prove bus", || {
            leaf::prove_balance(&l.push, &l.pull, &l.count, &cols, &owners, &spans, &mut ps)
        });
        let table_claims = crate::stage!("Prove constraints", || {
            // One sumcheck for all eight tables (§constraints).
            let table_cols: Vec<Vec<&[F64]>> = spans
                .iter()
                .map(|&(base, n)| (0..n).map(|c| cols[base + c]).collect())
                .collect();
            // The eq point is the bus GKR's ζ, not a fresh one: that is what lets the
            // batch settle the bus forms alongside the constraints.
            let xi = ps.sample();
            let form_pows = xi_form_pows(xi);
            let sigma = sigmas(&bus.sigmas, form_pows);
            constraints::prove(
                &airs(&l.taus, &bus.forms, xi),
                &table_cols,
                xi,
                &bus.point,
                &sigma,
                &mut ps,
            )
        });
        (bus, table_claims)
    };
    let l = &w.layout;

    let r_pi = [ps.sample(), ps.sample()];
    let slots = finish_claims(l, bus.claims, &table_claims, r_pi);

    // Run flock's reduction (zerocheck + lincheck) over the prepared native
    // layouts retained from the fused q_flock build pass; it returns the
    // validity claim on the committed `q_flock`, discharged by the PCS below in
    // the SAME WHIR as every leanVM point claim (the point claims become the
    // opener's `point_claims`).
    let flock_reduction = w.flock_reduction;
    let reduced = crate::stage!("Flock reduction", || { flock_reduction.prove(&mut ps) });
    let n_blocks = flock_reduction.n_blocks();
    drop(flock_reduction);
    let offset = w.layout.placements[QFLOCK].offset;
    let mut rings = vec![crate::hash_flock::ring_switch_open(n_blocks, offset, &reduced)];
    // The two u64 circuits the same way, each a ring-switched region of its own.
    let u64_reductions = w.u64_reductions;
    crate::stage!("u64 reductions", || {
        for (op, prepared) in U64_OPS.into_iter().zip(&u64_reductions) {
            let placement = &w.layout.placements[u64_column(op)];
            let reduced = prepared.prove(&mut ps);
            rings.push(flock::reduction::ring_switch_open(
                placement.n_vars,
                placement.offset,
                &reduced,
            ));
        }
    });
    drop(u64_reductions);
    crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &rings) });
    (
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            base_counts: exec.base_counts,
            committed: committed_size,
            log_mem: w.log_mem,
            mem_used: exec.mem_used,
        },
    )
}

/// Everything the PCS has to open, in the ORDER that feeds the batch's weights:
/// the bus's framework claims, then the zerocheck's per-table column claims, then
/// the two public-word claims, each located in its committed slot. Both sides assemble
/// it here, so a claim can never shift by one element.
fn finish_claims(
    l: &Layout,
    bus_claims: Vec<ColumnClaim>,
    table_claims: &[constraints::Claims],
    r_pi: [F192; 2],
) -> Vec<pcs::SlotClaim> {
    let mut claims = bus_claims;
    let sch = schema();
    claims.reserve(sch.n - N_SHARED);
    for (t, table) in tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            claims.push(ColumnClaim {
                col: sch.base[t] + c,
                point: table_claims[t].chi.clone(),
                value: table_claims[t].evals[c],
            });
        }
    }
    for col in [MEM_INIT, MEM_FIN] {
        claims.push(bind_pi_claim(col, r_pi, &l.placements, &l.pi));
    }
    slot_claims(l, claims)
}

/// The public words' binding (§sec:e2e-pi): the committed memory `col` (before the
/// run, or after it) at `(r_0, r_1, 0,…,0)` must equal the multilinear extension of
/// the four public words at `(r_0, r_1)`. Both parties know those words, so the
/// claim's value is computed rather than transmitted, and the opening discharges it
/// like any other.
fn bind_pi_claim(col: usize, r: [F192; 2], placements: &[witness::Placement], pi: &[F64; 4]) -> ColumnClaim {
    let mut point = vec![F192::ZERO; placements[col].n_vars];
    point[..2].copy_from_slice(&r);
    ColumnClaim {
        col,
        point,
        value: primitives::multilinear::mle_eval(pi, &r),
    }
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs, never the prover's witness.
pub fn verify(program: &Program, public_input: &[F64; 4], proof: &Proof) -> Result<(), CpuError> {
    verify_to_raw(program, public_input, proof).map(|_| ())
}

/// [`verify`], returning the proof it accepted with every query's Merkle path
/// written out, the form `python-verifier` reads.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify_to_raw(
    program: &Program,
    public_input: &[F64; 4],
    proof: &Proof,
) -> Result<fiat_shamir::transcript::RawProof, CpuError> {
    let mut vs = VerifierState::new(fs_seed(program), proof, *public_input);
    let (l, log_inv_rate) = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(CpuError::Transcript)?;

    // BLAKE2s to flock (single PCS): flock's R1CS validity and every leanVM point
    // claim are verified together by ONE WHIR opening at the end. The padded
    // BLAKE2s table size is public and announced; its flock sub-proof rides the
    // shared stream and openings. Memory and bytecode bind every compression input
    // and output by routing their virtual value-column claims to q_flock.
    let n_blake2s = 1usize << l.taus[tables::BLAKE2S_TABLE];

    let (owners, spans) = bus_wiring(program, &l);
    let bus = leaf::verify_balance(&l.push, &l.pull, &l.count, &owners, &spans, &mut vs).map_err(CpuError::Bus)?;

    let zc_xi = vs.sample();
    let form_pows = xi_form_pows(zc_xi);
    // THE tie between the batch and the bus, and the reason the batch's target is
    // never transmitted. Each side's leaf claim less what its framework blocks
    // account for is the tables' share `R_s`, which the verifier just derived; the
    // batch must sum to `Σ_s η^{base+s}·R_s`. Since `η` is sampled after the `R_s`
    // are fixed, hitting that one number forces `Σ_t σ_{s,t} = R_s` on all three
    // sides. A transmitted target would be a free value in its own check, and the
    // tables' bus blocks would be settled by nothing at all.
    let target = (0..3).fold(F192::ZERO, |a, s| a + form_pows[s] * bus.totals[s]);
    let table_claims = constraints::verify(&airs(&l.taus, &bus.forms, zc_xi), zc_xi, &bus.point, target, &mut vs)
        .map_err(CpuError::Constraint)?;

    let r_pi = [vs.sample(), vs.sample()];
    let slots = finish_claims(&l, bus.claims, &table_claims, r_pi);

    // Replay flock's reduction straight off the shared stream (each scalar bound
    // as it is read) to recover its validity claim on q_flock, then
    // verify them alongside every point claim in the ONE WHIR opening
    // (mirroring `prove`). The padding convention always supplies at least one
    // instance, including programs that execute no BLAKE2s instruction.
    let n_blocks = n_blake2s.max(1);
    let offset = l.placements[QFLOCK].offset;
    let replay = crate::hash_flock::verify_reduction(n_blocks, &mut vs).map_err(CpuError::Blake2s)?;
    let mut replays = Vec::with_capacity(U64_OPS.len());
    for op in U64_OPS {
        let tau = l.taus[tables::u64_table(op)];
        replays.push(crate::arith_flock::verify_reduction(op, tau, &mut vs).map_err(CpuError::U64)?);
    }
    let mut rings = vec![crate::hash_flock::ring_switch_verify(n_blocks, offset, &replay.claim)];
    for (op, replay) in U64_OPS.into_iter().zip(&replays) {
        let placement = &l.placements[u64_column(op)];
        rings.push(flock::reduction::ring_switch_verify(
            placement.n_vars,
            placement.offset,
            &replay.claim,
        ));
    }
    pcs::verify(&mut vs, &slots, &rings, l.shape, log_inv_rate, &root).map_err(CpuError::Open)?;
    vs.finish().map_err(CpuError::Transcript)?;
    Ok(vs.into_raw_proof())
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE2s value columns are virtual: they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_flock` slot evaluation: an ordinary claim on the committed
/// `QFLOCK` column at the point freezing the low 8 coords to the slot's bits and
/// the high coords to `r`. No downstream special-casing: it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: Vec<ColumnClaim>) -> Vec<pcs::SlotClaim> {
    claims
        .into_iter()
        .map(|c| {
            // A virtual BLAKE2s value column (always virtual): its bus claim at
            // instance point `c.point` is the q_flock slot value, a boolean-selector
            // (strided) claim on QFLOCK, folded sparsely (2^n_log, not the 2^(8+n_log)
            // dense QFLOCK block).
            if let Some((q_col, slot, stride_log)) = flock_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[q_col].offset,
                    slot,
                    stride_log,
                    point: c.point,
                    value: c.value,
                };
            }
            pcs::SlotClaim::Point {
                offset: l.placements[c.col].offset,
                low_point: c.point,
                value: c.value,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const PI: [F64; 4] = [F64(7), F64(11), F64(13), F64(17)];

    /// The default one-block-root metadata for a hand-built BLAKE2s op.
    fn md() -> [F64; 2] {
        crate::hash_flock::metadata(crate::hash_flock::PINNED_T, crate::hash_flock::FINAL_FLAG, 0)
    }

    /// A hand-built straight-line program over the first `frame` cells, padded with
    /// `SET`s so its last instruction lands just before the never-executed sentinel
    /// of a `len`-slot bytecode.
    fn padded(mut prog: Vec<Op>, len: usize, frame: u32) -> Program {
        let mut next = frame;
        while prog.len() < len - 1 {
            prog.push(Op::Set { o: next, k: F64::ONE });
            next += 1;
        }
        prog.push(Op::Xor64 { a: 0, b: 0, c: 0 });
        Program::assemble(prog)
    }

    /// One BLAKE2s row over hand-set cells: `a` at 4..8 and `b` at 8..12, the
    /// metadata at 12..14, the public input as chaining value, the digest at 14..18.
    fn blake2s_program(a: [F64; 4], b: [F64; 4], ins: [u32; 4]) -> Program {
        let mut prog: Vec<Op> = a
            .iter()
            .chain(&b)
            .chain(&md())
            .enumerate()
            .map(|(i, &k)| Op::Set { o: 4 + i as u32, k })
            .collect();
        prog.push(Op::Blake2s {
            ins,
            cv: 0,
            out: 14,
            md: 12,
        });
        padded(prog, 16, 18)
    }

    const A: [F64; 4] = [
        F64(0x0123_4567_89ab_cdef),
        F64(0xfedc_ba98_7654_3210),
        F64(0x1111_2222_3333_4444),
        F64(0x5555_6666_7777_8888),
    ];
    const B: [F64; 4] = [
        F64(0xdead_beef_cafe_babe),
        F64(0x0bad_f00d_0bad_f00d),
        F64(0x9999_aaaa_bbbb_cccc),
        F64(0xdddd_eeee_ffff_0000),
    ];

    /// The opcode's execution semantics: the digest of the four message chunks under
    /// the public input's chaining value lands in the four output cells.
    #[test]
    fn blake2s_computes_the_compression() {
        let exec = blake2s_program(A, B, [4, 6, 8, 10]).execute(PI);
        assert_eq!(exec.mem[14..18], blake2s_compress(A, B, PI, md()));
    }

    /// A self-hash `BLAKE2s(h, h)` names the same chunks as both halves, the aliasing
    /// the DSL's hash-chain lowering relies on.
    #[test]
    fn blake2s_self_hash_aliased_operands() {
        let exec = blake2s_program(A, B, [4, 6, 4, 6]).execute(PI);
        assert_eq!(exec.mem[14..18], blake2s_compress(A, A, PI, md()));
    }

    /// Reassign every range read's count, as a prover would after changing a gap, so
    /// that the range arrays balance and what is left to judge is the memory itself.
    fn recount_range_reads(exec: &mut Execution) {
        let mask = (1u32 << tables::RANGE_LOG) - 1;
        let mut lo = vec![F64::ONE; 1 << tables::RANGE_LOG];
        let mut hi = lo.clone();
        let mut read = |a: &mut Access| {
            let (l, h) = ((a.gap & mask) as usize, (a.gap >> tables::RANGE_LOG) as usize);
            (a.count_lo, a.count_hi) = (lo[l], hi[h]);
            lo[l] = primitives::field::mul_by_g(lo[l]);
            hi[h] = primitives::field::mul_by_g(hi[h]);
        };
        let t = &mut exec.trace;
        t.xor64
            .iter_mut()
            .chain(&mut t.mul64)
            .chain(&mut t.add_u64)
            .chain(&mut t.mul_u64)
            .for_each(|r| r.acc.iter_mut().for_each(&mut read));
        t.set.iter_mut().for_each(|r| r.acc.iter_mut().for_each(&mut read));
        t.deref.iter_mut().for_each(|r| r.acc.iter_mut().for_each(&mut read));
        t.jump.iter_mut().for_each(|r| r.acc.iter_mut().for_each(&mut read));
        t.blake2s.iter_mut().for_each(|r| r.acc.iter_mut().for_each(&mut read));
        (t.range_lo_count, t.range_hi_count) = (lo, hi);
    }

    /// The point of the timestamps: a cell written twice cannot be read as of its
    /// first write. The forged run is consistent everywhere else (the stale value
    /// flows into the result, the final memory and the range reads), so what fails
    /// is the memory multiset itself: the first write's tuple is pulled twice.
    #[test]
    fn a_stale_read_unbalances_the_bus() {
        const RATE: usize = pcs::TEST_LOG_INV_RATE;
        let (cell, other, dest) = (4, 5, 6);
        let program = Program::from_body(
            vec![
                Op::Set { o: cell, k: F64(5) },
                Op::Set { o: cell, k: F64(9) },
                Op::Set { o: other, k: F64(3) },
                Op::Xor64 {
                    a: cell,
                    b: other,
                    c: dest,
                },
            ],
            8,
        );
        let pi = [F64::ZERO; 4];
        let honest = program.execute(pi);
        assert_eq!(honest.mem[dest as usize], F64(9) + F64(3));
        let (proof, _) = prove_execution(&program, &honest, pi, RATE);
        verify(&program, &pi, &proof).expect("the honest run verifies");

        let mut forged = program.execute(pi);
        let row = forged
            .trace
            .xor64
            .iter_mut()
            .find(|r| !r.ts.is_zero())
            .expect("the program's one XOR64 row");
        // The read happens at cycle 4; the first write happened at cycle 1.
        let stride = tables::CLOCK_STRIDE;
        assert_eq!(
            (row.va, row.acc[0].x, row.acc[0].gap),
            (F64(9), g_pow(2 * stride as usize), 2 * stride - 1)
        );
        (row.va, row.acc[0].x, row.acc[0].gap) = (F64(5), g_pow(stride as usize), 3 * stride - 1);
        forged.mem[dest as usize] = F64(5) + F64(3);
        recount_range_reads(&mut forged);
        let refused = std::panic::catch_unwind(|| prove_execution(&program, &forged, pi, RATE).0)
            .expect_err("a stale read was proven");
        let message = refused.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(
            message.contains("two products to agree"),
            "refused for another reason: {message}"
        );

        // The same forgery with an honest read is a no-op: recounting alone changes
        // no product, so the refusal above is the stale read's.
        let mut recounted = program.execute(pi);
        recount_range_reads(&mut recounted);
        let (proof, _) = prove_execution(&program, &recounted, pi, RATE);
        verify(&program, &pi, &proof).expect("recounting is harmless");
    }
}
