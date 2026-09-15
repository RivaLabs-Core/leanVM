<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM, for post-quantum Ethereum</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#xmss-aggregation">leanXMSS aggregation</a></td>
    <td align="right"><b>1.2K/s</b></td>
  </tr>
  <tr>
    <td><a href="#sphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>280/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>0.29s</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>480K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>5.4M/s</b></td>
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
* **ISA**: A migration from leanISA to RISC-V (rv64im) is planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### XMSS aggregation

The XMSS parameters are specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/xmss/XmssSecurity/Statement.lean).

```bash
cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

```
aggregation, 900 XMSS signatures
  cycles (VM steps)           : 2,188,060 = 2^21.061
    details                   : SET 2^19.265 (28.8%)  DEREF 2^19.126 (26.2%)  MUL64 2^18.734 (19.9%)XOR64 2^18.21 (13.9%)  BLAKE2S 2^16.989 (5.9%)  JUMP 2^16.827 (5.3%)  XOR192 2^5.209 (0.0%)  MEMORY 2^22.014  TOTAL_COMMITTED 2^26.384
  proof size                  : 306.6 KiB
  proving time                : 0.868 s ± 0.8%      peak memory 9.837 GiB
  per signature               : 1,036.452 signatures/s
  verifying                   : 4.237 ms
```

### SPHINCS aggregation

The SPHINCS parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/sphincs/SphincsSecurity/Statement.lean).

```bash
cargo run --release -- aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

```
aggregation, 245 SPHINCS signatures
  cycles (VM steps)           : 2,581,573 = 2^21.3
    details                   : MUL64 2^19.304 (25.1%)  XOR64 2^19.139 (22.4%)  SET 2^19.13 (22.2%)  DEREF 2^19.089 (21.6%)  BLAKE2S 2^16.992 (5.0%)  JUMP 2^16.534 (3.7%)  XOR192 2^4.858 (0.0%)  MEMORY 2^22.056  TOTAL_COMMITTED 2^26.562
  proof size                  : 316.4 KiB
  proving time                : 1.058 s ± 4.7%      peak memory 12.524 GiB
  per signature               : 231.676 signatures/s
  verifying                   : 4.348 ms
```

### data availability

```bash
cargo run --release -- aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 5,220,524 = 2^22.316
    details                   : MUL64 2^20.672 (32.0%)  DEREF 2^20.667 (31.9%)  XOR64 2^20.595 (30.3%)  SET 2^17.643 (3.9%)  BLAKE2S 2^16.295 (1.5%)  JUMP 2^13.448 (0.2%)  XOR192 2^12.139 (0.1%)  MEMORY 2^22.545  TOTAL_COMMITTED 2^26.952
  proof size                  : 342.6 KiB
  proving time                : 1.741 s ± 82.6%      peak memory 16.34 GiB
  blob throughput             : 9.189 blobs/s, 1.149 MiB/s
  verifying                   : 6.892 ms
```

### recursion

```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 834,835 = 2^19.671
    details                   : MUL64 2^18.093 (33.5%)  DEREF 2^18.064 (32.8%)  SET 2^16.321 (9.8%)  XOR64 2^16.299 (9.7%)  MUL192 2^15.582 (5.9%)  XOR192 2^15.424 (5.3%)  BLAKE2S 2^13.997 (2.0%)  JUMP 2^13.206 (1.1%)  MEMORY 2^20.434  TOTAL_COMMITTED 2^24.681
  proof size                  : 209.0 KiB
  proving time                : 0.394 s ± 6.0%      peak memory 11.354 GiB
  verifying                   : 4.346 ms
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
  (~3289.9 XMSS/s equivalent at 146 compressions/signature)
```

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,882
    details                   : MUL64 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR64 2^10.966 (0.1%)  MEMORY 2^20.96  TOTAL_COMMITTED 2^24.716
  proof size                  : 299.3 KiB
  proving                     : 0.272 s ± 10.7%   7,813,917 cycles/s      peak memory 3.418 GiB
  verifying                   : 2.3 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
