//! S5 host: execute the guest in SP1 (execution only, no proving) and check its public output
//! against `fp-host`, the S3 reference.
//!
//! The guest's private input is what a `cp_verify` call reads from its five paths: the
//! configuration folder's `policy.txt`, `layout.txt` and `KL.bin`, the ivk folder's `key.bin` and
//! the leaf file that the proof names, and the request, y and proof files; then the commitment ID.
//! Each byte string is written with `SP1Stdin::write`, the length-prefixed serialization that the
//! guest reads with `sp1_zkvm::io::read`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use sp1_core_executor::SP1CoreOpts;
use sp1_sdk::blocking::{Elf, Prover, ProverClient, SP1Stdin};

fn fail(msg: &str) -> ! {
    eprintln!("host-exec: {msg}");
    std::process::exit(1)
}

fn read(path: &Path) -> Vec<u8> {
    fs::read(path).unwrap_or_else(|e| fail(&format!("cannot read {}: {e}", path.display())))
}

fn find_elf(zkvm: &Path) -> PathBuf {
    let mut tried = Vec::new();
    for triple in [
        "riscv64im-succinct-zkvm-elf",
        "riscv32im-succinct-zkvm-elf",
    ] {
        for base in [zkvm.join("target"), zkvm.join("guest").join("target")] {
            tried.push(
                base.join("elf-compilation")
                    .join(triple)
                    .join("release")
                    .join("guest"),
            );
        }
        for base in [zkvm.join("elf"), zkvm.join("guest").join("elf")] {
            tried.push(base.join(triple).join("release").join("guest"));
        }
    }
    for c in &tried {
        if c.is_file() {
            return c.clone();
        }
    }
    let list = tried
        .iter()
        .map(|p| format!("  {}", p.display()))
        .collect::<Vec<_>>()
        .join("\n");
    fail(&format!(
        "the guest ELF was not found. Run `cargo prove build` in zkvm/guest (or set GUEST_ELF).\nTried:\n{list}"
    ))
}

fn main() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let zkvm = manifest
        .parent()
        .expect("zkvm/host-exec has a parent")
        .to_path_buf();
    let repo = zkvm.parent().expect("zkvm has a parent").to_path_buf();
    let fixtures = repo.join("rust-nostd-verifier").join("fixtures");
    let elf_path = match std::env::var("GUEST_ELF") {
        Ok(p) => PathBuf::from(p),
        Err(_) => find_elf(&zkvm),
    };
    let elf = read(&elf_path);
    println!(
        "host-exec: sp1 circuit {}, guest ELF {} ({} bytes)",
        sp1_sdk::SP1_CIRCUIT_VERSION,
        elf_path.display(),
        elf.len()
    );

    let config = fixtures.join("config");
    let ivk = fixtures.join("ivk");
    let request_path = fixtures.join("example.req");
    let y_path = fixtures.join("example.y");
    let proof_path = fixtures.join("example.proof");
    let policy = read(&config.join("policy.txt"));
    let layout = read(&config.join("layout.txt"));
    let kl = read(&config.join("KL.bin"));
    let key = read(&ivk.join("key.bin"));
    let proof = read(&proof_path);
    let request = read(&request_path);
    let y = read(&y_path);
    let id = String::from_utf8(read(&fixtures.join("ID.txt")))
        .expect("ID.txt is UTF-8")
        .trim()
        .to_string();
    // The proof header's third word is the leaf number (`cpProofHead`, cp_verify.cpp:3365-3374).
    if proof.len() < 12 {
        fail("the proof file is shorter than its header");
    }
    let entry_number = u32::from_le_bytes(proof[8..12].try_into().unwrap());
    let entry = read(&ivk.join("leaf").join(format!("{entry_number}.bin")));

    let mut stdin = SP1Stdin::new();
    stdin.write(&policy);
    stdin.write(&layout);
    stdin.write(&kl);
    stdin.write(&key);
    stdin.write(&entry);
    stdin.write(&entry_number);
    stdin.write(&request);
    stdin.write(&y);
    stdin.write(&proof);
    stdin.write(&id);

    let client = ProverClient::builder().cpu().build();
    let started = std::time::Instant::now();
    let (mut public, report) = client
        .execute(Elf::from(elf), stdin)
        .run()
        .unwrap_or_else(|e| fail(&format!("SP1 execute failed: {e}")));
    let elapsed = started.elapsed().as_secs_f64();

    let out: String = public.read();
    let status: i32 = public.read();
    let cycles = report.total_instruction_count();
    let shard_size = SP1CoreOpts::default().shard_size as u64;
    let shards = cycles.div_ceil(shard_size);
    println!("host-exec: execute {elapsed:.2} s, guest exit code {}, status {status}", report.exit_code);
    println!("host-exec: total cycles {cycles}");
    println!(
        "host-exec: shards {shards} (estimate ceil(cycles / shard_size), shard_size {shard_size}; \
         the executor also splits at the trace-area thresholds)"
    );
    println!("host-exec: syscalls {}", report.total_syscall_count());
    println!(
        "host-exec: memory {} addresses touched, {} bytes of execution record",
        report.touched_memory_addresses,
        report.total_record_size()
    );
    println!("host-exec: public output ({} bytes):", out.len());
    print!("{out}");
    if !out.ends_with('\n') {
        println!();
    }

    // The S3 reference: `fp-host` on the same five paths, with the same ID and -q.
    let fp_host = repo.join("rust-nostd-verifier").join("target").join("debug").join("fp-host");
    if !fp_host.is_file() {
        fail(&format!(
            "{} is missing; build it with `cargo build` in rust-nostd-verifier/",
            fp_host.display()
        ));
    }
    let reference = Command::new(&fp_host)
        .arg(&config)
        .arg(&ivk)
        .arg(&request_path)
        .arg(&y_path)
        .arg(&proof_path)
        .arg("-id")
        .arg(&id)
        .arg("-q")
        .output()
        .unwrap_or_else(|e| fail(&format!("cannot run fp-host: {e}")));
    let reference_out = String::from_utf8_lossy(&reference.stdout);
    let want_result = reference_out
        .lines()
        .find(|l| l.starts_with("result-v1 "))
        .unwrap_or_else(|| fail("fp-host printed no result-v1 line"));
    let want_yes = reference_out.lines().last() == Some("YES");
    let got_result = out
        .lines()
        .find(|l| l.starts_with("result-v1 "))
        .unwrap_or_else(|| fail("the guest's public output has no result-v1 line"));
    let got_yes = out.lines().last() == Some("YES");

    let result_ok = got_result == want_result;
    let yes_ok = got_yes == want_yes;
    println!(
        "host-exec: result-v1 {}",
        if result_ok { "IDENTICAL" } else { "DIFFERS" }
    );
    if !result_ok {
        println!("  fp-host: {want_result}");
        println!("  guest:   {got_result}");
    }
    println!(
        "host-exec: YES {}",
        if yes_ok { "IDENTICAL" } else { "DIFFERS" }
    );
    if !(result_ok && yes_ok) {
        fail("the guest's public output does not match fp-host");
    }
    if status != 0 {
        fail(&format!("the guest ended with status {status}, expected 0"));
    }
    println!("host-exec: PASS (result-v1 and YES are byte-identical to fp-host)");
}
