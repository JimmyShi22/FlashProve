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
use fp_core::frame::parameters::pol_word_u64;
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
        // `cpLengthHeld()` uses the parameter file's `lt` when present. Like C++'s polWord(), the
        // strict parser strips the frame first.
        if let Some(lt) = pol_word_u64(&conf.pol, "lt") {
            if lt <= 20 {
                cp_length_held(&at[2], (1u64 << lt) + 2);
            }
        }
        cp_length_held(&at[3], 1);
        let (request, odd_request) = must_read_words(&at[2], "request");
        let (_y, odd_y) = must_read_words(&at[3], "y");
        if !odd_request && !odd_y {
            cp_policy_held(&policy, &conf.pol, &request);
        }
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

/// A `-plan request` option's value (`cpPlanMain`'s `value` lambda, cp_verify.cpp:3173-3178): the
/// option may not come twice, and its value must exist.
fn plan_take<'a>(args: &'a [String], into: &mut Option<&'a str>, i: &mut usize) -> bool {
    if into.is_some() || *i + 1 >= args.len() {
        return false;
    }
    *i += 1;
    *into = Some(args[*i].as_str());
    true
}

/// `cpPlanMain()` (`cp_verify.cpp:3120-3218`): the same usage, file reads and rejections as C++.
/// Where C++ would run a stage and print a plan (exit 4), the port still ends NOT CHECKED: the
/// planners and `configure` are not ported yet, and the stub must never print YES.
fn plan_main(args: &[String]) -> i32 {
    if args.len() < 3 {
        usage("-plan wants id, request, accounting or arrays");
    }
    let what = args[2].as_str();
    if what == "id" {
        if args.len() != 5 {
            usage("-plan id wants exactly <config folder> <key.bin>");
        }
        let _conf = cp_conf_read(&args[3]);
        let _key = need_bytes(&args[4], "key");
        return plan_stub();
    }
    if what == "accounting" || what == "arrays" {
        if args.len() != 5 || decimal(&args[4], 1_000_000).is_none() {
            usage(&format!(
                "-plan accounting and -plan arrays want exactly <config folder> <asked>; {}",
                ASKED_FORM
            ));
        }
        let conf = cp_conf_read(&args[3]);
        // A made-up request: T tokens 0, with r = 0 and e = T. If `lt` is missing or above 20 the
        // request stays empty; the stage rejects such a parameter file.
        let _request = match pol_word_u64(&conf.pol, "lt") {
            Some(lt) if lt <= 20 => {
                let mut r = vec![0u32; (1usize << lt) + 2];
                let t = 1u32 << lt;
                *r.last_mut().unwrap() = t;
                r
            }
            _ => Vec::new(),
        };
        let _y = vec![0u32];
        return plan_stub();
    }
    if what != "request" {
        usage("-plan wants id, request, accounting or arrays");
    }
    if args.len() < 6 || decimal(&args[5], 1_000_000).is_none() {
        usage(&format!(
            "-plan request wants <policy.txt> <KL.bin> <asked>; {}",
            ASKED_FORM
        ));
    }
    let mut layout_path: Option<&str> = None;
    let mut prompt_path: Option<&str> = None;
    let mut reply_path: Option<&str> = None;
    let mut j_arg: Option<&str> = None;
    let mut i = 6usize;
    while i < args.len() {
        let a = args[i].as_str();
        let mut ok = true;
        if a == "-layout" {
            ok = plan_take(args, &mut layout_path, &mut i);
        } else if a == "-prompt" {
            ok = plan_take(args, &mut prompt_path, &mut i);
        } else if a == "-reply" {
            ok = plan_take(args, &mut reply_path, &mut i);
        } else if a == "-j" {
            ok = plan_take(args, &mut j_arg, &mut i);
        } else if a == "-shapes" || a == "-fields" || a == "-arrays" || a == "-q" {
            // Flags may repeat.
        } else {
            ok = false;
        }
        if !ok {
            usage(&format!(
                "argument {} is not an option of -plan request, comes a second time, or lacks its value",
                i
            ));
        }
        i += 1;
    }
    let mut threads: u32 = 1;
    if let Some(j) = j_arg {
        match decimal(j, 256) {
            Some(v) => threads = v,
            None => usage(THREADS_FORM),
        }
    }
    if threads < 1 || prompt_path.is_none() || reply_path.is_none() {
        usage(&format!("-plan request wants -prompt and -reply; {}", THREADS_FORM));
    }
    let _pol = need_bytes(&args[3], "policy");
    let (_kl, odd) = must_read_words(&args[4], "KL");
    if odd {
        end_with_refusal(Refusal::named("KL-length"), "");
    }
    if let Some(l) = layout_path {
        let _ = need_bytes(l, "layout");
    }
    let _request = must_read_words(prompt_path.unwrap(), "request");
    let _y = must_read_words(reply_path.unwrap(), "y");
    plan_stub()
}

/// The safe ending where a planning stage would print its plan.
fn plan_stub() -> i32 {
    let how = "-plan is not implemented in S2b-4 yet";
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

/// `acceptancePolicyIsExactMatch()` (`vf_common.h:615-617`).
fn acceptance_policy_is_exact_match(c: u64, theta: u64, cap: u64, sh: u64, st: u64) -> bool {
    sh < 63 && c == theta && theta == (1u64 << sh) && cap == 0 && st + 4 == sh
}

/// `policyKind()` (`vf_common.h:623-627`).
fn policy_kind(c: u64, theta: u64, cap: u64, s: u64, sh: u64, st: u64) -> &'static str {
    if acceptance_policy_is_exact_match(c, theta, cap, sh, st) {
        "exact-match"
    } else if st + 4 == sh {
        "clipped-gap"
    } else if st == s {
        "log-probability"
    } else {
        "another-table"
    }
}

/// `PolicyNamed::is()` (`vf_common.h:674-681`).
fn policy_is(p: &PolicyNamed, c: u64, theta: u64, cap: u64, s: u64, sh: u64, st: u64) -> bool {
    p.kind == policy_kind(c, theta, cap, s, sh, st)
        && p.c == c
        && p.theta == theta
        && p.cap == cap
        && p.s == s
        && p.sh == sh
}

/// `cpPolicyHeld()` (`cp_verify.cpp:3254-3273`): compares the caller's policy (or `exact-match`)
/// with the parameter file and the request. A missing or malformed line returns silently; a stage
/// rejects such a file later.
fn cp_policy_held(p: &PolicyNamed, pol: &[u8], request: &[u32]) {
    let (Some(c), Some(theta), Some(cap), Some(s), Some(sh), Some(st)) = (
        pol_word_u64(pol, "C"),
        pol_word_u64(pol, "theta"),
        pol_word_u64(pol, "cap"),
        pol_word_u64(pol, "s"),
        pol_word_u64(pol, "sh"),
        pol_word_u64(pol, "sT"),
    ) else {
        return;
    };
    if st + 4 != sh {
        policy_refused(&format!(
            "the parameter file sets the kind of policy {}; this program takes exact-match and clipped-gap",
            policy_kind(c, theta, cap, s, sh, st)
        ));
    }
    if p.given && !policy_is(p, c, theta, cap, s, sh, st) {
        policy_refused("the option -policy names another kind of policy or another C, theta, cap, s or sh than the parameter file sets");
    }
    let Some(lt) = pol_word_u64(pol, "lt") else { return };
    if lt > 20 || request.len() as u64 != (1u64 << lt) + 2 {
        return;
    }
    let t = 1u64 << lt;
    let r = request[t as usize] as u64;
    let e = request[t as usize + 1] as u64;
    let last = core::cmp::min(e, t - 1);
    if r >= e || e > t {
        return;
    }
    let n = if r < last { last - r } else { 0 };
    if !p.given && n != 0 && !acceptance_policy_is_exact_match(c, theta, cap, sh, st) {
        policy_refused("the request covers more than the output token, the parameter file sets another policy than exact-match, and the call has no -policy");
    }
    policy_says(p, n, t);
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

// `polWord()` is `fp_core::frame::parameters::pol_word_u64`: the strict parser strips the frame,
// then the named line is read from `Parameters::rest`.
