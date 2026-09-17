# AGENTS.md

## What this is

A minimal virtual machine and the SNARK that proves its execution. Proofs are not zero knowledge. There is no front end on this branch: programs are hand-assembled with `Program::from_body` (Fibonacci, a BLAKE2s hash chain, a 64-bit LCG), and small for now.

- `doc/leanvm/` is the LaTeX project describing the machine ISA and the snark that proves it. Its root is `doc/leanvm/main.tex`; build it with `cd doc/leanvm && latexmk -pdf main.tex`, which writes to the gitignored `doc/leanvm/.build/`. Sections live in `doc/leanvm/body/`, numbered `01`..`08` plus the lettered annexes `a` (ring switching), `b` (the PCS), `c` (Flock), and `d` (novel basis and additive NTT), and every symbol is defined once in `doc/leanvm/preamble/macros.tex`. If latexmk fails oddly (a bibtex error, or a missing `main.log`) right after inputs are renamed or `refs.bib` is edited, remove `doc/leanvm/.build` and rerun; it has not reproduced on unchanged inputs. **Drafting one section:** each section file carries a `% !TeX root` comment pointing at its generated driver in `doc/leanvm/drafts/`, so the LaTeX build key (`F5`, or the extension's `cmd+alt+b`) compiles only that section, numbered as in the full document and with cross-references and citations resolved against `.build/main.aux`; in `main.tex` the same key builds everything. Run `doc/leanvm/make-drafts.sh` after adding, renaming or renumbering a section.
- The one hash function is BLAKE2s, in `primitives::hash`: scalar, streaming, keyed, and a lane-transposed batched form for the PCS Merkle tree. The VM proves one compression per opcode, and BLAKE2s takes the byte counter and final-block flag as ordinary compression inputs, so repeated opcodes hash arbitrary byte strings by carrying the chaining value and setting the counter and final flag for each block.

## Layout

Dependency order, leaves first:

| crate             | role                                                                   |
| ----------------- | ---------------------------------------------------------------------- |
| `parallel`        | thread pool (below)                                     |
| `zk_alloc`        | proving arena (below)                                    |
| `primitives`      | field kernels (NEON/AVX), bit transposes, multilinear helpers, streaming stores, `bench` |
| `fiat_shamir`     | VM-native `FiatShamirState` + prover/verifier transcript                |
| `pcs`             | additive NTT, Merkle, ring switch, stacked WHIR                    |
| `flock`           | batched R1CS over GF(2): zerocheck + lincheck, for the BLAKE2s circuit (`hash`) and the u64 adder and multiplier (`arith`) |
| `lean_vm`         | arithmetization: tables, bus, constraints, `cpu::prove`/`verify`       |

`src/lib.rs` is the public API and the only thing a user imports: every crate above is `publish = false`, so a new user-facing item is a re-export there. `src/main.rs` is the benchmark CLI, `tests/api.rs` the end-to-end use of the API.

## Building / Testing / Formatting

- `.cargo/config.toml` pins `-C target-cpu=native` and `-D warnings` for rustdoc
- always run in `--release` mode any test or benchmark touching the VM
- **One test binary per crate, not one per file** (`lean_vm/tests/verifiers/main.rs`). Exception: a test opening an arena phase (`lean_vm::init_prover`) needs its own binary. Phases are process-global, so two in one process reclaim each other's `ArenaVec`s and the symptom is a proof that stops verifying, never a crash (`tests/api.rs` is that binary, and `tests/no_arena.rs` the one that must never enable the arena).

An x86-only arm never compiles on an Apple dev machine, so a typo in one ships. Type-check the other target before pushing anything `cfg`-gated:

```bash
CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512vl,+vpclmulqdq,+pclmulqdq,+gfni,+avx2,+aes" \
  cargo check --release --workspace --target x86_64-unknown-linux-gnu
```

It needs `rustup target add x86_64-unknown-linux-gnu` and nothing else, since `check` does not link. The `apple-m4 is not a recognized processor` and `x87` notes are the pinned `target-cpu=native` and the bare cross ABI, not findings. To confirm an arm is really being reached rather than silently skipped, drop a `compile_error!` in it and watch the check fail.

```bash
cargo testall                     # release workspace tests
cargo clippyall                   # clippy, -D warnings
cargo docall                      # rustdoc, -D warnings
cargo fmt --all                   # max_width = 120
ruff format --line-length 150 python-verifier/verifier.py   # and `ruff check` it
```

Heavy benches and measurement harnesses are `#[ignore]`d; run by name with `-- --ignored --nocapture`: `hash_batch_prove_verify`, `add_wrapping_prove_verify`, `mul_wrapping_prove_verify`, `mul_widening_prove_verify`, `pcs_throughput`, `multithreaded_throughput`, `print_whir_query_counts`, `print_whir_query_table`.

## Benchmarking

The benchmarks we care about:

- `cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3`
- `BENCH_REPEAT=3 FLOCK_N_LOG=18 cargo test --release -p flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored`

## Read-write memory

Memory is read-write, by timestamped offline memory checking (`doc/leanvm` §sec:memchan). What to keep in mind before touching it:

- **The clock rides the state tuple**, `(pc, fp, ts)`, and is `g^(4·cycle)`: a row's access in slot `k` carries the timestamp `g^k·ts`, which is what lets one row touch the same cell twice (`MUL64 a a c`, an in-place counter). `BLAKE2S` makes eighteen accesses, so it advances the clock by 20. The run starts at cycle 1, because the memory seed is stamped `g^0` and an access must be strictly later than the one before.
- **Strictness is the soundness.** An access pulls `(addr, prev, old)` and pushes `(addr, g^k·ts, new)`, with `prev·lo = g^k·ts·hi`, where `lo` and `hi` are read off two uncommitted range arrays (`{g^(j+1)}` and `{g^(-2^16·j)}`, 2^16 entries each). The `+1` in the low array is the strict `<`: with a gap of zero a read pulls the tuple it pushes and returns anything.
- **Padding rows have clock zero**, and zero is no power of `g`: their state tuples close around a fill block (`0·g^s = 0`), their accesses are forced to `prev = 0` and cancel themselves, and nothing they flush can meet a tuple of the run. They are written out by `cpu::execute`, not executed, and touch no memory. Any new table has to keep this true: every memory tuple's timestamp must be `g^k·ts` or the committed `prev`, nothing else.
- **Three memory columns**: the memory before the run, after it, and each cell's last timestamp. The four public words are bound in both the first and the second, so they are input and output at once and a run has to leave them as it found them.
- **The initial memory is the prover's** in the protocol, the public words aside: only those four cells of the committed initial memory are bound. The executor starts every other cell at zero, there being no advice channel yet; a front end that wants one gets it by choosing initial cells, and its programs then have to check what they read before writing it.
- **A gap is below 2^32**, and a cell's first access is measured from zero, so a run is capped near 2^30 cycles. The executor asserts it.
- `a_stale_read_unbalances_the_bus` is the soundness regression test (a forged run that serves an overwritten value), `lean_vm/tests/verifiers/read_write.rs` the program that only read-write memory can run, checked by both verifiers.

## Flock-backed instructions

`BLAKE2S`, `ADD_U64` and `MUL_U64` are relations no degree-2 identity over `K` expresses, so each is a Boolean circuit proven by flock (`doc/leanvm` Annex C, §flock:u64), glued in by `lean_vm::hash_flock` and `lean_vm::arith_flock`:

- **One packed witness per circuit**, a committed column of the one stack (`QFLOCK`, `QADD`, `QMUL`): instance `j` is row `j` of the instruction's table. The packing is 64 bits a word and a memory word is 64 bits, so the words a row touches ARE packed words of its instance, and the table's value columns are virtual: their claims are routed to slots of that witness (`cpu::flock_value_slot`). A new flock-backed instruction follows the same three steps: a table with virtual value columns, a committed witness, a ring-switched region.
- **One reduction per circuit, one opening for all.** The three zerocheck plus lincheck runs happen in table order after the public-word claims, each leaving a claim on its own witness; `pcs::stack_open` takes one ring-switched region per witness, all under one map challenge.
- **Batch floors.** Flock needs eight instances and a zerocheck cube of `2^13` bits, so `ADD_U64`'s table has at least 32 rows and the other two at least 8 (`cpu::filler::MIN_ROWS`); padding rows supply them, as all-zero instances.
- **The circuits are gate lists**, walked forwards by the verifier and backwards by the prover, never matrices. `python-verifier/verifier.py` rebuilds the adder and the multiplier gate for gate (`_adder`, `_multiplier`): the multiplier's carry-save schedule sorts rows with a stable sort, so a change to `flock::arith::mul` has to be mirrored there in the same order, and `u64_arithmetic_proves_and_verifies` is what catches a drift.

## The proving arena (`zk_alloc`)

One proof is one **phase**, opened by `cpu::prove`. `ArenaVec` bumps a per-thread slab, a small block's release is at most a cursor pop while a large one is recycled (below), and the next `begin_phase()` reclaims everything. Not a `#[global_allocator]`: `raw_dealloc` picks arena-vs-system by address range, so with no phase open `ArenaVec` is an ordinary system vector (used in particular by the verifier, where correctness and simplicity matters much more than performance).

**The rule:** an `ArenaVec` allocated in a phase dies at the next `begin_phase()`. A reset neither clears nor unmaps, so a buffer that outlives its phase reads the previous proof's plausible bytes, so the symptom is a proof that stops verifying, never a crash. Anything outliving a phase (a `Proof`, a cache, a table) must be a plain `Vec`. And **`drop` means something**: a large released block is handed back out within the phase (a per-thread free list, see the crate docs), so dropping a big buffer where it dies is worth doing, and a use-after-free the bump arena used to mask now reads another buffer's live data. Run `ZK_ALLOC_POISON=1 cargo testall` after changing buffer lifetimes; it fills released blocks and fills what a phase used when it ends, turning a silent wrong answer into a loud failure. That covers both shapes: a buffer read after being dropped, and a buffer that outlives its phase.

`setup_prover_without_arena` (or `lean_vm::init_prover_pool` alone) leaves the arena disengaged, sending every `ArenaVec` to the system allocator. It is the escape hatch for a host where even the recycled peak does not fit; on one that it does fit, the arena is faster, since its pages stay faulted in across proofs.

## The thread pool (`parallel`)

No rayon. Every parallel site is "N independent items, each writing its own disjoint slice", so the pool is a claim counter, not a work-stealing deque: `NUM_THREADS-1` workers plus the dispatcher inline, no per-dispatch allocation. Primitives: `for_each{,_chunk}`, `chunks_mut{,2,_zip}`, `Chunks`, `fill`, `map_collect`, `map_reduce`, `fold_reduce`, `map_reduce_with_state`, `find_first`, `SendPtr`.

- **Nested dispatch panics**, because it would deadlock the dispatch lock.
- **Both core clusters share one queue** (P at `USER_INTERACTIVE`, E at `UTILITY`); guided self-scheduling means a slow core claims fewer batches. Do not add a second pool: that was `primitives::epool`, now deleted.
- **The default holds back one performance worker when efficiency workers exist.**

`LEANVM_NUM_THREADS` sets the **performance**-worker count, leaving E-workers in place. `1` = strictly sequential.

## Two verifiers, one protocol

The same verification algorithm is written out twice, in two languages. Any change to the snark protocol has to land in both.

1. **Rust**, `lean_vm::cpu::verify`. The native verifier.
2. **Python**, `python-verifier/verifier.py` (no dependencies), for readability and simplicity. Pinned by `lean_vm/tests/verifiers/python_verifier.rs`, which feeds it the raw proof `cpu::verify_to_raw` returns.

## Conventions that bite

- **The prover can be memory-bandwidth bound.** Reduce memory traffic before assuming that more workers or fewer instructions improve throughput. `primitives::stream::Stream` publishes a buffer without the read-for-ownership an ordinary store pays, but ONLY where nothing reads the destination again before it is evicted. Where a consumer follows in the same pass, the fetch it avoids becomes that consumer's miss: fold kernels earn it by building their round message from registers, or by folding into an L1 stage first (`whir::fold_and_msg_blocks`). That fetch is an x86 cost only: on Apple silicon a store-only fill already sustains what a read-only pass does and `STNP` measures identical to `STP`, so `Stream` is a plain copy there and the L1 stage earns its keep for the read locality alone, which is still better than writing through.
- **NEON is the width ceiling on Apple silicon**, so an AVX-512 win that is purely width has no counterpart: the M4 has no SVE, and its SME2 is streaming-mode matrix work with no polynomial multiply. What does port is *shape*. A fused NTT pass wants a butterfly at a time over whole rows, not the register-resident tile the AVX-512 arms use: they transpose anyway and want to pay for it once per pass, while NEON transposes nothing and a tile leaves only its own width of independent work to cover the reduction's dependent PMULL folds, where a row leaves the whole lane count. Measured both directions: the tile costs the extension NTT, and costs the base encode's `Commit` again.
- **A `[F192; N]` in a NEON kernel is a memory object, where on AVX-512 it is the register.** Four tower products are four independent PMULL chains wanting most of the 32 vector registers, so an array of them spills and the spill costs more than batching the products saves; the same array is free on AVX-512, where the quad IS one register. Keep the quad as a tuple or as named values and let arrays exist only inside the batched-product helper, on the target that wants them (`flock::zerocheck::multilinear`'s `mul_quad`). The symptom is indirect, so suspect the shape rather than the arithmetic: the products measure the same either way, destructuring the results changes nothing, and forcing the helper to inline recovers almost none of it.
- **On Zen 4, 512-bit cross-lane data movement is half-rate** (every 512-bit shuffle is two 256-bit uops), so packing scalars into vector lanes with `vpermi2q`/`vpermq` and extracting with `vextracti64x4` loses to the scalar moves it replaces. Widening the arithmetic still pays: `mul4` beats the same products issued one at a time. Prefer kernels where both qwords of every 128-bit lane carry a product and nothing crosses lanes.
- Use comments only when necessary: uncommented but readable and simple code is better than commented slop. And when you use comments, be concise.
- **Never put a measurement in a comment, a doc comment, or this file.** Timings, throughputs, percentages and speedup factors go stale the moment the code, the compiler or the host changes, and nothing ever rechecks them, so they end up asserting something false with the authority of a comment. The commit message is where they belong: it is dated, it is immutable, and it says what was true when the change landed. A comment may say which way a result went and why (that a tile lost to whole rows, that one reduction beat another), never by how much.
- Commit tests only that are useful in the future, to prevent regressions / failures. Don't add trivial tests that will always pass.
- Simpler is better.
- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the Fiat-Shamir state as a side effect. The public statement seeds the transcript at construction; the transport exposes no separate observe operation. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive the layout identically** from announced sizes. Changes to `placements_of` or the schema land on both sides. `col_kappas` is derived from `col_kappa_sources` rather than written out twice, so the two can no longer drift; keep it that way.
- **The L0 lane fold binds the committed witness's TOP `INITIAL_FOLDING_FACTOR` variables**, because lane `l` of the interleaved commitment is the stack block `q[l·2^(μ-k) ..)`. That makes the witness's zero tail whole lanes, so `whir::commit` encodes only `StackShape::n_lanes` of them, and the opening's dense weight, its first `k` sumcheck rounds and the stack allocation shrink with it. **A leaf image is still `2^k` words**, the absent lanes contributing their codeword's zeros, but those zeros LEAD it (codeword lane `t` is stack block `n_lanes-1-t`): their whole 64-byte blocks are then one shared chaining value (`hash::zero_prefix_state`) the committer hashes once rather than per leaf, and only the image's tail rides the proof, so `PrunedMerklePaths` stores `n_lanes` words per L0 row while `RawMerklePath` (what the Python verifier reads) carries the full image. Both verifiers therefore derive `n_lanes` from the announced layout to read a row. Since `mu = log2_ceil(placed)`, `n_lanes` is always in `[2^(k-1)+1, 2^k]`: the encode saving caps near half, the hashing saving is quantized to whole blocks of 8 lanes, and both are ~0 just above a power of two. The cost is that fold challenges arrive in round order while every transparent weight is written in witness coordinates, so both verifiers rotate the terminal point left by `k` before evaluating it (`whir.rs` before `eval_b_at`, `verifier.py` before `evaluate_basis`). Anything else that reads the opening's point (per-level induced weights, the residual) stays in round order.
- **One symbol, one meaning, across the whole leanVM document.** All notation is defined in `doc/leanvm/preamble/macros.tex`: define a new macro there rather than inline, and check the letter is free first. Annex B's "Symbols" table maps its letters back to WHIR/Ligerito/BCHKS25, so read it before renaming one. A sumcheck round challenge is `\fc` everywhere, which is what keeps `\rho` free for the rate; `r` is the point a claim is made at, not a challenge. **A rename in the document is a rename in the implementations**: the Rust prover and verifier and `python-verifier/verifier.py` name their variables after the document's symbols, so the three have to move together.
- **Doc labels are an API.** `crates/pcs` cites `thm:rbr` and `thm:mca-johnson` by name and several crates cite `doc/leanvm/main.tex` sections, so renaming a label breaks those pointers with nothing to catch it. `doc/leanvm/body/NN-*.tex` prefixes match section numbers, so inserting a section renumbers the rest.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Env knobs

| var                                                                                                     | effect                                           |
| ------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| `LEANVM_NUM_THREADS`                                                                                    | performance-worker count; `1` = sequential       |
| `LEANVM_PROFILE`                                                                                        | per-stage prover timings                         |
| `ZK_ALLOC_STATS`                                                                                        | arena peak/phase, high water, overflow           |
| `ZK_ALLOC_POISON`                                                                                       | fill released arena blocks, to catch use-after-free |
| `BENCH_REPEAT`, `BENCH_COOLDOWN`                                                                        | `--repeat`/`--cooldown` for `#[ignore]`d benches |
| `LEANVM_HASH_N`, `LEANVM_HASH_UNROLL`                                                                   | workload sizes in tests                          |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING`, `LINCHECK_TRACE`                                 | flock batch size, stage traces                   |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_SAMPLES`                                                          | PCS throughput bench                             |
| `WHIR_TRACE`, `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE`                                          | WHIR NTT/Merkle split                        |

## Side notes

- Grinding chooses the smallest valid nonce, including in parallel.
