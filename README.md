<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>480K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">RISC-V cycles</a></td>
    <td align="right"><b>1.6M/s</b></td>
  </tr>
</table>

## security

leanVM is designed for security:

 * 128-bit ROM (64-bit QROM) soundness
 * no proximity gap conjecture
 * end-to-end formal verification
 * a traditional hash function

**warning**: Formal verification is [in progress](https://github.com/Verified-zkEVM/leanerVM). leanVM is not (yet) production ready.

## work in progress

Expect leanVM to change significantly:

* **hash**: BLAKE2s is a placeholder. SHA2, SHA3, BLAKE3 are actively considered.
* **ISA**: leanVM proves RISC-V (rv64im) plus one custom instruction, the BLAKE2s compression. A run is one proof; continuations, for runs whose witness exceeds one commitment, are planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## guests

A guest is a `no_std` Rust program built for `riscv64im-unknown-none-elf` against the runtime crate in [`guests/rt`](./guests/rt/src/lib.rs), which gives it its public input (four words), its advice (a region of memory the prover fills, which the statement says nothing about), its output (four words) and a BLAKE2s hasher over the custom instruction. The linker script fixes the memory map. Build them with `guests/build.sh` (a nightly toolchain, for `-Zbuild-std`), then prove and verify a run:

```bash
cargo run --release -- guest guests/elf/preimage.elf --advice 5,0x6f6c6c6568
```

The statement a proof makes is the program (an ELF file), the four input words and the four output words; everything a guest reads from its advice it has to check itself, which is what makes a proof a proof of knowledge (`preimage` outputs the digest of a message only the prover has).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (modulo 2^64), N = 2,000,000
  cycles (VM steps)           : 2,097,208
    details                   : ALU 2^20.934 (100.0%)  TOTAL_COMMITTED 2^26.395
  proof size                  : 337.5 KiB
  proving                     : 1.281 s ± 1.2%   1,636,564 cycles/s      peak memory 11.6 GiB
  verifying                   : 6.186 ms
```

### BLAKE2s in plain Rust

The `blake2s` guest is the hash function written in ordinary Rust, compiled by `rustc` for `riscv64im-unknown-none-elf` (`guests/blake2s`): 10,000 bytes, 157 compressions, a mix of arithmetic, shifts, loads and stores.

```bash
cargo run --release -- guest guests/elf/blake2s.elf --input 10000 --repeat 3 --cooldown 2
```

```
guests/elf/blake2s.elf
  input                       : [2710, 0, 0, 0]
  output                      : [8f9fc3d71d84c0cc, 515c979fa65679e8, 9ffc0e1e022efcc7, cef54d0c06836e56]
  cycles (VM steps)           : 1,015,824
    details                   : ALU 2^18.47 (55.2%)  SHIFT 2^17.238 (23.5%)  LOAD 2^16.356 (12.8%)  STORE 2^15.139 (5.5%)  MUL 2^13.288 (1.5%)  MULH 2^13.288 (1.5%)  TOTAL_COMMITTED 2^25.435
  proof size                  : 328.6 KiB
  proving                     : 0.698 s ± 1.2%   1,454,472 cycles/s      peak memory 5.18 GiB
  verifying                   : 7.185 ms
```

### BLAKE2s through the precompile

The `hash` guest hashes 50,000 bytes through the compression instruction, 782 compressions; most of its cycles generate the message.

```bash
cargo run --release -- guest guests/elf/hash.elf --input 50000 --repeat 3
```

```
guests/elf/hash.elf
  cycles (VM steps)           : 869,384
    details                   : ALU 2^18.641 (59.8%)  SHIFT 2^16.61 (14.6%)  STORE 2^15.915 (9.0%)  MULH 2^15.61 (7.3%)  MUL 2^15.61 (7.3%)  LOAD 2^13.618 (1.8%)  HASH 2^9.611 (0.1%)  TOTAL_COMMITTED 2^25.49
  proof size                  : 331.0 KiB
  proving                     : 0.816 s ± 0.9%   1,065,522 cycles/s      peak memory 5.238 GiB
  verifying                   : 7.796 ms
```

### hashing

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release --package flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     64.6 ms ± 7.8%   10.6%
  commit                          :    101.2 ms ± 0.4%   16.6%
  zerocheck                       :    238.3 ms ± 3.9%   39.0%
  lincheck                        :     20.3 ms ± 12.2%   3.3%
  pcs opening                     :    186.0 ms ± 2.9%   30.5%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    545.8 ms ± 1.1%   89.4%
  verify                          :      1.9 ms
  throughput                      :        480,319 compressions/s ± 1.1%
```

### u64 addition

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=24 cargo test --release --package flock --test batch_proving_arithmetic -- add_wrapping_prove_verify --exact --nocapture --include-ignored
```

```
Flock Wrapping u64 addition batch proving, 16,777,216 sums (2^24 slots)
  block                           : 2^8 bits, 256 constrained
  setup (circuit, excluded)       :      0.0 ms
  witness-gen                     :     52.1 ms ± 13.9%   8.1%
  commit                          :    102.3 ms ± 5.5%   15.9%
  zerocheck                       :    252.7 ms ± 11.2%  39.4%
  lincheck                        :     41.6 ms ± 9.6%    6.5%
  pcs opening                     :    192.4 ms ± 8.1%   30.0%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    641.2 ms ± 5.4%
  verify                          :      1.8 ms
  throughput                      :     26,165,809 sums/s ± 5.4%
```

### u64 multiplication

Wrapping (`u64` result):

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=20 cargo test --release --package flock --test batch_proving_arithmetic -- mul_wrapping_prove_verify --exact --nocapture --include-ignored
```

```
Flock Wrapping u64 multiplication batch proving, 1,048,576 products (2^20 slots)
  block                           : 2^12 bits, 2,336 constrained
  setup (circuit, excluded)       :      0.1 ms
  witness-gen                     :     79.7 ms ± 15.3%  13.4%
  commit                          :    101.5 ms ± 0.9%   17.1%
  zerocheck                       :    214.6 ms ± 0.5%   36.2%
  lincheck                        :     12.6 ms ± 17.5%   2.1%
  pcs opening                     :    184.8 ms ± 4.0%   31.2%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    593.2 ms ± 2.3%
  verify                          :      1.8 ms
  throughput                      :      1,767,718 products/s ± 2.3%
```

Widening (`u128` result):

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=19 cargo test --release --package flock --test batch_proving_arithmetic -- mul_widening_prove_verify --exact --nocapture --include-ignored
```

```
Flock Widening u64 multiplication batch proving, 524,288 products (2^19 slots)
  block                           : 2^13 bits, 4,544 constrained
  setup (circuit, excluded)       :      0.1 ms
  witness-gen                     :     49.2 ms ± 22.5%   9.3%
  commit                          :    102.6 ms ± 3.0%   19.4%
  zerocheck                       :    179.2 ms ± 3.0%   33.9%
  lincheck                        :     11.6 ms ± 7.3%    2.2%
  pcs opening                     :    186.6 ms ± 8.4%   35.3%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    529.2 ms ± 5.2%
  verify                          :      1.9 ms
  throughput                      :        990,726 products/s ± 5.2%
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
