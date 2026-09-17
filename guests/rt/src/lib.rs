//! The runtime of a leanVM guest: where a run starts, how it ends, its public input
//! and output. A guest is a `no_std`, `no_main` binary defining
//!
//! ```ignore
//! #[unsafe(no_mangle)]
//! extern "C" fn main() { leanvm_guest::output([..]) }
//! ```
//!
//! The environment has no traps to handle: an illegal instruction, a misaligned or
//! unmapped access, or an `ecall` that is not `exit` leave a run with no proof. So a
//! panic is one illegal instruction, and nothing else is needed.
#![no_std]

use core::arch::global_asm;

// The run starts here: a stack, `main`, then `exit` with the output in `a0..a3`.
global_asm!(
    ".section .text._start",
    ".globl _start",
    "_start:",
    ".option push",
    ".option norelax",
    "la sp, __stack_top",
    ".option pop",
    "call main",
    "la t0, {output}",
    "ld a0, 0(t0)",
    "ld a1, 8(t0)",
    "ld a2, 16(t0)",
    "ld a3, 24(t0)",
    "li a7, 93",
    "ecall",
    output = sym OUTPUT,
);

static mut OUTPUT: [u64; 4] = [0; 4];

unsafe extern "C" {
    /// RAM's first four words (`link.ld`).
    static __input: [u64; 4];
}

/// The run's public input.
pub fn input() -> [u64; 4] {
    // SAFETY: the linker script reserves these words, and nothing writes them.
    unsafe { core::ptr::read_volatile(&raw const __input) }
}

/// Set the run's public output, which the run returns in `a0..a3` when `main` does.
pub fn output(words: [u64; 4]) {
    // SAFETY: one hart, no interrupts: nothing else touches `OUTPUT`.
    unsafe { core::ptr::write_volatile(&raw mut OUTPUT, words) }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // `unimp`: an illegal instruction, so a panicking run has no proof.
    unsafe { core::arch::asm!("unimp", options(noreturn)) }
}
