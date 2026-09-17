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
* **ISA**: leanVM is moving from its own leanISA to RISC-V (rv64im). The machine, its registers and the add, compare, logic, branch and jump instructions are proven today; memory, shifts, multiplication, division and an ELF loader are in progress. Programs are hand-assembled for now.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

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

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (modulo 2^64), N = 2,000,000
  cycles (VM steps)           : 2,097,152
    details                   : ALU 2^20.934 (100.0%)  TOTAL_COMMITTED 2^26.394
  proof size                  : 305.7 KiB
  proving                     : 1.298 s ± 15.7%   1,615,327 cycles/s      peak memory 11.923 GiB
  verifying                   : 2.524 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
