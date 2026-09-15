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
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>4.0M/s</b></td>
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
* **ISA**: A migration from leanISA to RISC-V (rv64im) is planned. Memory is already read-write; the zkDSL still assumes write-once memory, so the programs it compiles run and prove but are not sound yet.
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

### u64 multiplication

Wrapping (`u64` result):

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=20 cargo test --release --package flock --test batch_proving_mul -- mul_wrapping_prove_verify --exact --nocapture --include-ignored
```

```
Flock Wrapping u64 multiplication batch proving, 1,048,576 products (2^20 slots)
  block                           : 2^12 bits, 2,336 constrained
  setup (circuit, excluded)       :      0.1 ms
  witness-gen                     :     74.0 ms ± 2.1%   12.3%
  commit                          :    102.0 ms ± 0.8%   17.0%
  zerocheck                       :    227.5 ms ± 5.6%   37.8%
  lincheck                        :     12.1 ms ± 3.9%    2.0%
  pcs opening                     :    186.2 ms ± 2.6%   30.9%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    601.7 ms ± 2.0%
  verify                          :      1.8 ms
  throughput                      :      1,742,636 products/s ± 2.0%
```

Widening (`u128` result):

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=19 cargo test --release --package flock --test batch_proving_mul -- mul_widening_prove_verify --exact --nocapture --include-ignored
```

```
Flock Widening u64 multiplication batch proving, 524,288 products (2^19 slots)
  block                           : 2^13 bits, 4,544 constrained
  setup (circuit, excluded)       :      0.1 ms
  witness-gen                     :     48.3 ms ± 5.5%    9.0%
  commit                          :    102.3 ms ± 4.7%   19.1%
  zerocheck                       :    185.1 ms ± 9.5%   34.6%
  lincheck                        :     11.3 ms ± 4.4%    2.1%
  pcs opening                     :    188.7 ms ± 2.4%   35.2%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    535.6 ms ± 2.4%
  verify                          :      1.9 ms
  throughput                      :        978,878 products/s ± 2.4%
```

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,880
    details                   : MUL64 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR64 2^10.966 (0.1%)  MEMORY 2^20.959  TOTAL_COMMITTED 2^25.825
  proof size                  : 321.8 KiB
  proving                     : 0.534 s ± 2.8%   3,982,409 cycles/s      peak memory 8.604 GiB
  verifying                   : 2.705 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
