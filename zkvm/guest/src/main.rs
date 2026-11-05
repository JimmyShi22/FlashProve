//! S5: the FlashProve verifier inside SP1.
//!
//! Private input, in this order. Each byte string uses `sp1_zkvm::io::read`'s standard
//! serialization (a length, then the bytes):
//!
//!   policy.txt | layout.txt | KL.bin | key.bin | the entry file (ivk/leaf/<k>.bin) |
//!   the entry number k (u32) | the request file | the y file | the proof file |
//!   the commitment ID (a string)
//!
//! The reference call's five paths are the configuration folder (`policy.txt`, `layout.txt`,
//! `KL.bin`), the ivk folder (`key.bin` and the leaf file that the proof names), and the request,
//! y and proof files; a zkVM guest cannot read a folder, so each file is its own input.
//!
//! The public output is the call's accounting, the `result-v1` line and `YES` — the same lines
//! that `fp-host` prints on the accepted example.

#![no_std]
#![no_main]

extern crate alloc;

mod call;

use alloc::string::String;
use alloc::vec::Vec;

use sp1_zkvm::io;

sp1_zkvm::entrypoint!(main);

fn bytes() -> Vec<u8> {
    io::read::<Vec<u8>>()
}

pub fn main() {
    let pol = bytes();
    let layout = bytes();
    let kl = bytes();
    let key = bytes();
    let entry = bytes();
    let entry_number = io::read::<u32>();
    let request = bytes();
    let y = bytes();
    let proof = bytes();
    let id = io::read::<String>();
    let part = io::read::<u32>();

    let (out, status) = call::run(call::Inputs {
        pol: &pol,
        layout: &layout,
        kl: &kl,
        key: &key,
        entry: &entry,
        entry_number,
        request: &request,
        y: &y,
        proof: &proof,
        id_asked: &id,
        asked: fp_core::consts::BAR,
        part,
    });
    io::commit(&out);
    io::commit(&status);
}
