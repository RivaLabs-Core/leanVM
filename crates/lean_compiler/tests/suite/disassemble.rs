//! `disassemble` must render every one of the eight opcodes without panicking,
//! so it stays usable when a failure names only a pc.

use lean_compiler::{compile, disassemble, parse};
use primitives::pretty_integer;

#[test]
fn disassemble_covers_every_opcode() {
    let src = "\
def main():
    buff = HeapBuf(6)
    buff[1] = 1
    buff[GEN] = GEN
    for i in mul_range(1, GEN ** 4):
        buff[i * GEN ** 2] = buff[i] * buff[i * GEN]
    h = [5, 0, 7, 0]
    d = StackBuf(4)
    blake2s(h, h, d)
    p = 1
    p[1] = add_u64(mul_u64(buff[GEN ** 4], d[1]), d[2])
    p[GEN] = d[0]
    return
";

    let program = compile(&parse(src).expect("parse"));

    println!("\n=== zkDSL source ===\n{src}");
    println!(
        "=== compiled ISA ({} instructions) ===",
        pretty_integer(program.prog.len())
    );
    let text = disassemble(&program.prog);
    print!("{text}");

    for mnemonic in [
        "SET", "XOR64", "MUL64", "DEREF", "JUMP", "BLAKE2S", "ADD_U64", "MUL_U64",
    ] {
        assert!(text.contains(mnemonic), "disassembly is missing {mnemonic}");
    }
}
