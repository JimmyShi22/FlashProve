//! Host shell for the S1 verifier skeleton.
//!
//! S1 implements the command line, file reading, the two header checks and the three-stage
//! skeleton. Each stage body is still a stub: it returns `Internal("not-implemented")`, and the
//! host prints `NOT CHECKED: internal-stage` with status 5. The stub path can never print `YES`.
//!
//! The C++ source of each piece is named in the comments. CLI text is taken from
//! `verifier/src/cp_verify.cpp:3015-3115`; the static part is `usage.txt`, captured from the
//! reference binary so that the bytes match.

use std::env;
use std::ffi::CStr;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::os::raw::c_char;
use std::process::exit;

use fp_core::consts::{BAR, DIGEST_HALF_BITS, HEXW};
use fp_core::head::{cp_key_head, cp_policy_word, cp_proof_head};
use fp_core::out::{
    cp_not_checked_lines, input_unreadable_line, no_line, role_name,
};
use fp_core::refusal::Refusal;
use fp_core::stage_state::StageState;

const USAGE: &str = include_str!("usage.txt");

/// `POLICY_OPTION_FORM_TEXT` (`vf_common.h:683-686`).
const POLICY_OPTION_FORM_TEXT: &str = "-policy requires <kind>,<C>,<theta>,<cap>,<s>,<sh>: exact-match or clipped-gap and five whole numbers of at most ten digits without leading zeros, with commas and no blanks between them";

/// `ASKED_FORM` (`cp_verify.cpp:3011`).
const ASKED_FORM: &str = "<asked>, the requested bits, is a whole number from 0 to 1000000, in digits alone, without a leading zero";

/// `THREADS_FORM` (`cp_verify.cpp:3012`).
const THREADS_FORM: &str =
    "after -j comes a whole number from 1 to 256, in digits alone, without a leading zero";

fn main() {
    let args: Vec<String> = env::args().collect();
    exit(cp_main(&args));
}

/// `cpMain()` (`cp_verify.cpp:3274-3389`), S1 subset.
fn cp_main(args: &[String]) -> i32 {
    let arg1 = args.get(1).map(String::as_str).unwrap_or("");
    if arg1 == "-plan" {
        return plan_main(args);
    }
    let key_part = arg1 == "-key";
    let leaf_part = arg1 == "-leaf";
    let first = if key_part || leaf_part { 2 } else { 1 };
    let places = if key_part {
        2
    } else if leaf_part {
        3
    } else {
        5
    };
    if args.len() < first + places {
        usage(&format!(
            "too few arguments: this call wants {} file and folder names",
            places
        ));
    }
    let at = &args[first..first + places];

    let mut bits_arg: Option<&str> = None;
    let mut j_arg: Option<&str> = None;
    let mut id_arg: Option<&str> = None;
    let mut quiet = false;
    let mut next_token_asked = false;
    let mut show_stages = false;
    let mut no_work = false;
    let mut policy = PolicyNamed::default();

    let mut i = first + places;
    while i < args.len() {
        if args[i] == "-bits" && bits_arg.is_none() && i + 1 < args.len() {
            i += 1;
            bits_arg = Some(&args[i]);
        } else if args[i] == "-id" && id_arg.is_none() && i + 1 < args.len() {
            i += 1;
            id_arg = Some(&args[i]);
        } else if args[i] == "-j" && j_arg.is_none() && i + 1 < args.len() {
            i += 1;
            j_arg = Some(&args[i]);
        } else if args[i] == "-q" {
            quiet = true;
        } else if args[i] == "-show-stages" {
            show_stages = true;
        } else if args[i] == "-no-proof-of-work" {
            no_work = true;
        } else if args[i] == "-next-token" && !key_part && !leaf_part {
            next_token_asked = true;
        } else if args[i] == "-policy"
            && !policy.given
            && !key_part
            && !leaf_part
            && i + 1 < args.len()
        {
            i += 1;
            match policy_named_read(&args[i]) {
                Some(p) => policy = p,
                None => {
                    eprintln!("{}", POLICY_OPTION_FORM_TEXT);
                    return 2;
                }
            }
        } else {
            usage(&format!(
                "argument {} is not an option of this call, comes a second time, or lacks its value",
                i
            ));
        }
        i += 1;
    }

    let mut asked = BAR;
    if let Some(arg) = bits_arg {
        match decimal(arg, 1_000_000) {
            Some(v) => asked = v as f64,
            None => usage(&format!("after -bits comes <asked>; {}", ASKED_FORM)),
        }
    }
    let mut threads: u32 = 1;
    if let Some(arg) = j_arg {
        match decimal(arg, 256) {
            Some(v) if v != 0 => threads = v,
            _ => usage(THREADS_FORM),
        }
    }

    let mut id_asked = id_arg.unwrap_or("").as_bytes().to_vec();
    for c in &mut id_asked {
        if (b'A'..=b'F').contains(c) {
            *c += b'a' - b'A';
        }
    }
    let id_asked = String::from_utf8(id_asked).unwrap_or_default();
    if id_arg.is_some()
        && (id_asked.len() != HEXW
            || !id_asked
                .bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)))
    {
        eprintln!("-id requires {} hex digits", HEXW);
        return 2;
    }

    let below_bar = !(asked >= BAR);
    if asked > DIGEST_HALF_BITS {
        end_with_refusal(Refusal::named("cp-bits-above-digest"), "");
    }
    // `cpPolicySays(policy, 0, 0)`: the numbers alone, before any file is opened.
    policy_says(&policy, 0, 0);
    let _ = (below_bar, quiet, next_token_asked, show_stages, no_work, &id_asked);

    let conf = cp_conf_read(&at[0]);
    let key_path = if key_part || leaf_part {
        at[1].clone()
    } else {
        format!("{}/key.bin", at[1])
    };
    let key_b = need_bytes(&key_path, "key");

    let pol_ver = match cp_policy_word(&conf.pol) {
        Ok(v) => v,
        Err(r) => end_with_refusal(r, ""),
    };
    if let Err(r) = cp_key_head(&key_b, pol_ver) {
        end_with_refusal(r, "");
    }

    if leaf_part {
        let _entry_b = need_bytes(&at[2], "entry");
    } else if !key_part {
        // `cpLengthHeld()` uses the parameter file's `lt` when present. S1 reads `lt` with a
        // simple line search; the strict parameter parser arrives in S2.
        if let Some(lt) = pol_word_u64(&conf.pol, "lt") {
            if lt <= 20 {
                cp_length_held(&at[2], (1u64 << lt) + 2);
            }
        }
        cp_length_held(&at[3], 1);
        let (_request, _odd_request) = must_read_words(&at[2], "request");
        let (_y, _odd_y) = must_read_words(&at[3], "y");
        // cpPolicyHeld() needs the strict parameter parser and the request's words; S2.
        let proof_b = need_bytes(&at[4], "proof");
        let k = match cp_proof_head(&proof_b, pol_ver) {
            Ok(k) => k,
            Err(r) => end_with_refusal(r, ""),
        };
        let leaf_path = format!("{}/leaf/{}.bin", at[1], k);
        // C++ uses readWholeFile() here and turns any failure into cp-entry-missing, not into
        // input-unreadable-entry (`cp_verify.cpp:3373-3374`).
        if read_regular_file(&leaf_path).is_err() {
            end_with_refusal(Refusal::named("cp-entry-missing"), "");
        }
    }
    let _ = conf.kl;
    let _ = conf.layout;

    // Three stages, one process, each with a fresh StageState. C++ forks one child per stage
    // (`cpStagesRun`, cp_verify.cpp:2670); the default `-j` is 1, so parFor is serial.
    let stages: &[&str] = if key_part {
        &["key"]
    } else if leaf_part {
        &["leaf"]
    } else {
        &["key", "leaf", "request"]
    };
    let mut internal: Option<(&str, String)> = None;
    for stage in stages {
        let stage_threads = if key_part || leaf_part || *stage == "request" {
            threads
        } else {
            core::cmp::max(1, threads / 8)
        };
        let mut state = StageState::default();
        state.inner_threads = stage_threads as i32;
        match run_stage_stub(stage) {
            Ok(()) => {}
            Err(Refusal::Named(name)) => end_with_refusal(Refusal::Named(name), ""),
            Err(Refusal::Internal(reason)) => {
                if internal.is_none() {
                    internal = Some((stage, reason));
                }
            }
        }
        drop(state);
    }
    if let Some((stage, reason)) = internal {
        let how = format!("the stage {} is not implemented in S1 ({})", stage, reason);
        print!("{}", cp_not_checked_lines(&how, "internal-stage"));
        flush_stdout();
        return 5;
    }
    0
}

/// S1 stage body: the proof system arrives in S2.
fn run_stage_stub(_stage: &str) -> fp_core::refusal::Result<()> {
    Err(Refusal::internal("not-implemented"))
}

/// `cpPlanMain()` (`cp_verify.cpp:3118+`). S1 parses nothing beyond the subcommand's presence
/// and checks nothing; it must never print YES.
fn plan_main(args: &[String]) -> i32 {
    if args.len() < 3 {
        usage("-plan wants id, request, accounting or arrays");
    }
    let how = "-plan is not implemented in S1";
    print!("{}", cp_not_checked_lines(how, "internal-stage"));
    flush_stdout();
    5
}

/// `cpUsage()` (`cp_verify.cpp:3015-3115`): the static text, then the fault line, status 2.
fn usage(fault: &str) -> ! {
    eprint!("{}", USAGE);
    eprintln!("cp_verify: this command line was not accepted: {}", fault);
    exit(2)
}

/// Ends a call with a `Refusal`: `NO: <name>` status 1, or `NOT CHECKED: <name>` status 5.
fn end_with_refusal(r: Refusal, how: &str) -> ! {
    match r {
        Refusal::Named(name) => {
            print!("{}", no_line(&name));
            flush_stdout();
            exit(1)
        }
        Refusal::Internal(name) => {
            print!("{}", cp_not_checked_lines(how, &name));
            flush_stdout();
            exit(5)
        }
    }
}

fn flush_stdout() {
    let _ = io::stdout().flush();
}

/// `decimal()` (`vf_common.h:353-365`): 1 to 7 digits, no leading zero, at most `max`.
fn decimal(arg: &str, max: u32) -> Option<u32> {
    let b = arg.as_bytes();
    if b.is_empty() || b.len() > 7 || (b.len() > 1 && b[0] == b'0') {
        return None;
    }
    let mut v = 0u32;
    for &c in b {
        if !c.is_ascii_digit() {
            return None;
        }
        v = 10 * v + (c - b'0') as u32;
    }
    if v > max {
        None
    } else {
        Some(v)
    }
}

/// The caller's `-policy` value (`PolicyNamed`, `vf_common.h:642-682`).
// `kind` and `s` are read by cpPolicyHeld() in S2 (`vf_common.h:674-681`).
#[allow(dead_code)]
#[derive(Default)]
struct PolicyNamed {
    given: bool,
    kind: String,
    c: u64,
    theta: u64,
    cap: u64,
    s: u64,
    sh: u64,
}

/// `policyNamedRead()` (`vf_common.h:688-704`).
fn policy_named_read(text: &str) -> Option<PolicyNamed> {
    let comma = text.find(',')?;
    let kind = &text[..comma];
    if kind != "exact-match" && kind != "clipped-gap" {
        return None;
    }
    let b = text.as_bytes();
    let mut i = comma + 1;
    let mut vals = [0u64; 5];
    for (k, slot) in vals.iter_mut().enumerate() {
        let first = i;
        while i < b.len() && b[i].is_ascii_digit() {
            *slot = 10 * *slot + (b[i] - b'0') as u64;
            i += 1;
        }
        if i == first || i - first > 10 || (b[first] == b'0' && i - first > 1) {
            return None;
        }
        if k < 4 {
            if i >= b.len() || b[i] != b',' {
                return None;
            }
            i += 1;
        } else if i != b.len() {
            return None;
        }
    }
    Some(PolicyNamed {
        given: true,
        kind: String::from(kind),
        c: vals[0],
        theta: vals[1],
        cap: vals[2],
        s: vals[3],
        sh: vals[4],
    })
}

/// `policyEmpty()` (`vf_common.h:660-671`).
fn policy_empty(n: u64, c: u64, theta: u64, cap: u64, sh: u64) -> u8 {
    let least = if sh < 63 { 1u64 << sh } else { u64::MAX };
    if c < least {
        1
    } else if theta < least {
        2
    } else if theta > c {
        3
    } else if theta == c && n != 0 && n <= cap {
        4
    } else {
        0
    }
}

/// `cpPolicySays()` (`cp_verify.cpp:3241-3252`).
fn policy_says(p: &PolicyNamed, n: u64, t: u64) {
    if !p.given {
        return;
    }
    let kind = policy_empty(n, p.c, p.theta, p.cap, p.sh);
    if kind == 0 {
        return;
    }
    let why = [
        "",
        "C is below 2^sh, the least cost of a token, so no cost is read",
        "theta is below 2^sh, the least cost of a token, so no request can meet it",
        "theta is above C, which no parameter file may set",
        "theta = C and cap is not below the number of the request's tokens that are checked, so none of them is barred",
    ];
    let mut text = format!("a result under the named policy would mean nothing: {}", why[kind as usize]);
    if kind == 4 {
        text.push_str(&format!(
            "; for the output token alone send a request with r = {}",
            t.wrapping_sub(1)
        ));
    }
    policy_refused(&text)
}

/// `cpPolicyRefused()` (`cp_verify.cpp:3235-3238`).
fn policy_refused(why: &str) -> ! {
    print!("policy: {}\nNO: policy\n", why);
    flush_stdout();
    exit(1)
}

/// `CpConf` + `cpConfRead()` (`vf_input_files.h:31-47`). The configuration folder's reads are
/// host-side; the header checks stay in `fp-core`.
struct CpConf {
    pol: Vec<u8>,
    kl: Vec<u32>,
    layout: Option<Vec<u8>>,
}

fn cp_conf_read(folder: &str) -> CpConf {
    let pol = need_bytes(&format!("{}/policy.txt", folder), "policy");
    let (kl, odd) = must_read_words(&format!("{}/KL.bin", folder), "KL");
    if odd {
        end_with_refusal(Refusal::named("KL-length"), "");
    }
    let layout_path = format!("{}/layout.txt", folder);
    // C++ uses lstat(): a name that exists must be readable, even a broken link.
    let has_layout = fs::symlink_metadata(&layout_path).is_ok();
    let layout = if has_layout {
        Some(need_bytes(&layout_path, "layout"))
    } else {
        None
    };
    CpConf { pol, kl, layout }
}

/// Why a read failed: `None` is C++'s `errno == 0` sentence, `Some(e)` is `strerror(e)`.
struct ReadFail(Option<i32>);

/// The checks of `readWholeFile()` (`vf_common.h:145-168`): regular path before the open,
/// regular file after it.
fn read_regular_file(path: &str) -> Result<Vec<u8>, ReadFail> {
    let meta = match fs::metadata(path) {
        Ok(m) => m,
        Err(e) => return Err(ReadFail(e.raw_os_error())),
    };
    if !meta.is_file() {
        return Err(ReadFail(None));
    }
    let mut f = match File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(ReadFail(e.raw_os_error())),
    };
    match f.metadata() {
        Ok(m) if m.is_file() => {}
        Ok(_) => return Err(ReadFail(None)),
        Err(e) => return Err(ReadFail(e.raw_os_error())),
    }
    let mut out = Vec::new();
    match f.read_to_end(&mut out) {
        Ok(_) => Ok(out),
        Err(e) => Err(ReadFail(e.raw_os_error())),
    }
}

/// `needBytes()` (`vf_common.h:317-320`).
fn need_bytes(path: &str, role: &str) -> Vec<u8> {
    match read_regular_file(path) {
        Ok(b) => b,
        Err(ReadFail(errno)) => unreadable(role, errno),
    }
}

/// `readWords()` (`vf_common.h:254-286`), without the parallel reader: words are little-endian,
/// and `odd` says whether the file's length is no multiple of 4.
fn read_words(path: &str) -> Result<(Vec<u32>, bool), ReadFail> {
    let bytes = read_regular_file(path)?;
    let odd = bytes.len() % 4 != 0;
    let words = bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    Ok((words, odd))
}

/// `mustReadWords()` (`vf_common.h:313-316`).
fn must_read_words(path: &str, role: &str) -> (Vec<u32>, bool) {
    match read_words(path) {
        Ok(v) => v,
        Err(ReadFail(errno)) => unreadable(role, errno),
    }
}

/// `unreadableInput()` (`vf_common.h:298-312`): status 2.
fn unreadable(role: &str, errno: Option<i32>) -> ! {
    let why = errno.map(strerror_string);
    print!(
        "{}",
        input_unreadable_line(role, role_name(role), why.as_deref())
    );
    flush_stdout();
    exit(2)
}

// `strerror()` from the host C library, for byte parity with the reference binary.
unsafe extern "C" {
    fn strerror(errnum: i32) -> *const c_char;
}

fn strerror_string(errnum: i32) -> String {
    let p = unsafe { strerror(errnum) };
    if p.is_null() {
        return format!("Unknown error {}", errnum);
    }
    unsafe { CStr::from_ptr(p) }.to_string_lossy().into_owned()
}

/// `cpLengthHeld()` (`cp_verify.cpp:3229-3233`): reject a regular file that is not `4 * words`
/// bytes long, without reading it.
fn cp_length_held(path: &str, words: u64) {
    let Ok(meta) = fs::metadata(path) else {
        return;
    };
    if !meta.is_file() || meta.len() == 4 * words {
        return;
    }
    let name = if meta.len() == 0 || meta.len() % 4 != 0 {
        "statement-required"
    } else {
        "statement-range"
    };
    end_with_refusal(Refusal::named(name), "")
}

/// `polWord()` (`cp_verify.cpp:281-305`), S1 simplification: a line search over the whole file.
///
/// The strict parser (`blk::read_parameters`) strips the frame first. For a valid parameter file
/// the named line is unique and appears after the frame, so the value is the same. S2 replaces
/// this with the strict parser.
fn pol_word_u64(pol: &[u8], name: &str) -> Option<u64> {
    let name = name.as_bytes();
    for line in pol.split(|&b| b == b'\n') {
        if line.len() > name.len() + 1
            && line.starts_with(name)
            && line[name.len()] == b' '
        {
            let v = &line[name.len() + 1..];
            if v.len() > 10 {
                return None;
            }
            let mut x = 0u64;
            for &c in v {
                if !c.is_ascii_digit() {
                    return None;
                }
                x = 10 * x + (c - b'0') as u64;
            }
            return Some(x);
        }
    }
    None
}
