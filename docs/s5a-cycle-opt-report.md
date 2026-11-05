# S5a-1 report: compile-level optimization of the SP1 guest

S5a-1 changes only the guest's compile configuration. No `.rs` business code and no BLAKE2b
implementation was touched; the C++ sources are untouched.

## 1. Method

- The S5 debug-executor run took 4,672 s per execute, too slow to iterate. `host-exec` was rebuilt
  with `--release` (`cargo build --release -p host-exec`, 2m13s); the release executor runs the same
  guest in about 322–542 s depending on machine load. **The executor's build does not change the
  cycle count**: the release executor reproduced S5's 32,385,267,062 exactly.
- Each experiment is one `cargo prove build -p guest --binaries guest` (plus the experiment's
  `--rustflags`), then one `target/release/host-exec` execute. The host prints the total cycles and
  compares `result-v1` and `YES` with `fp-host`; every measured variant passes that gate.
- The ELF's SHA-256 is recorded: an unchanged hash proves the variant's binary is identical, so its
  cycle count cannot differ.

## 2. The initial state

- `zkvm/Cargo.toml` had no `[profile.release]`. Cargo's release defaults therefore applied:
  `opt-level = 3`, `lto = false`, `codegen-units = 16`, `panic = "unwind"`.
- `sp1-build 6.10.0` always passes these rustflags to the guest build:
  `-C passes=lower-atomic`, `-C link-arg=--image-base=2013265920`, `-C panic=abort`,
  `--cfg getrandom_backend="custom"`,
  `-C llvm-args=-misched-prera-direction=bottomup`,
  `-C llvm-args=-misched-postra-direction=bottomup`.
- The target spec (`rustc --print target-spec-json -Z unstable-options --target
  riscv64im-succinct-zkvm-elf`) has `"features": "+m"` and `"panic-strategy": "abort"`.
  So the multiply extension is already enabled and panics already abort.

## 3. Experiments

| Step | Configuration change | Guest ELF (bytes / SHA-256) | Total cycles | Δ vs previous | Δ vs baseline | Consistency |
|---|---|---|---|---|---|---|
| 0 | none (cargo release defaults) | 3,207,568 / `6644c05a…` | 32,385,267,062 | — | — | PASS |
| 2 | `opt-level = 3` explicit | 3,207,568 / `6644c05a…` (identical) | 32,385,267,062 | 0 | 0 | PASS |
| 3 | `+ lto = "fat"`, `codegen-units = 1` | 2,832,504 / `4fc33452…` | 29,959,850,047 | −2,425,417,015 (−7.49%) | −7.49% | PASS |
| 4 | `+ panic = "abort"` | 2,832,504 / `77c1984a…` | 29,959,850,047 | 0 | −7.49% | PASS |
| 5 | target features: none added | unchanged (no rebuild) | 29,959,850,047 | 0 | −7.49% | n/a |
| 6 | `--rustflags="-Cllvm-args=-inline-threshold=1000"` | 12,194,968 / `8b841981…` | 27,176,326,759 | −2,783,523,288 (−9.29%) | −16.09% | PASS |
| final | `lto = "fat"`, `codegen-units = 1`, the LLVM flag (the two no-op lines removed) | 12,194,968 / `ce966b26…` | see §5 | — | — | see §5 |

Execute wall-clock varied with machine load (542.57 s, 381.30 s, 530.08 s, 482.82 s, 323.13 s) while
the cycle counts repeated exactly; wall-clock is not the metric.

## 4. Attribution

- **`lto = "fat"` + `codegen-units = 1` is the first real win: −7.49%.** Before it, `fp-core` was a
  separate codegen unit with no cross-crate inlining. The ELF also shrank from 3.21 MB to 2.83 MB.
- **The LLVM inlining threshold adds another −9.29% (total −16.09%).** Passing
  `-C llvm-args=-inline-threshold=1000` through `cargo prove build --rustflags` makes LLVM inline
  much more aggressively; the ELF grows 4.3× (2.83 MB → 12.19 MB), but the executed instruction
  count falls. This is the experiment that the S5a task book asked for: the cycle count is
  sensitive to the LLVM pass configuration, and the knob is landable through `--rustflags`
  (note the value must be attached: `--rustflags="-Cllvm-args=..."`; a space after `-C` makes rustc
  read an unknown codegen option).
- **`opt-level = 3` is already the default**: the ELF and the cycles are bit-for-bit identical.
- **`panic = "abort"` changes nothing**: `sp1-build` already passes `-C panic=abort`, and the target
  spec sets the abort strategy; the explicit profile line only changed a metadata byte in the ELF
  (the cycles stayed identical), so it was reverted.
- **No target feature can be added.** The target spec declares `features = "+m"` and `+m` is
  already enabled. `rustc --print target-features` lists other RISC-V features (`+a`, `+c`, …), but
  the SP1 target is RV64IM: its core does not include them, so enabling them is outside the
  declared ISA and was not attempted.

The final build command (reproducible):

```sh
cd zkvm
cargo prove build -p guest --binaries guest --rustflags="-Cllvm-args=-inline-threshold=1000"
# zkvm/Cargo.toml: [profile.release] lto = "fat", codegen-units = 1
```

## 5. Acceptance

The final configuration (`[profile.release] lto = "fat"`, `codegen-units = 1`, and
`--rustflags="-Cllvm-args=-inline-threshold=1000"`) executes the accepted example in
**27,176,326,759 cycles**, against the S5 baseline of **32,385,267,062**: **−5,208,940,303 cycles,
−16.09%**. The run ends with `guest exit code 0`, `status 0`, and the consistency gate:
`host-exec: result-v1 IDENTICAL`, `host-exec: YES IDENTICAL`, `host-exec: PASS (result-v1 and YES
are byte-identical to fp-host)`. The final ELF is 12,194,968 bytes, SHA-256 `ce966b26…` (the
final rebuild differs from Step 6's `8b841981…` only in metadata; its cycle count is identical).

No `.rs` file changed: the only working-tree change of S5a-1 is `zkvm/Cargo.toml`. The C++ sources
are untouched.

# S5a-2: the BLAKE2b soft implementation

Scope: the two BLAKE2b sites of `fp-core` — `hash/earlier.rs`'s `f2b::F` path and
`hash/modes.rs`'s `compress64` path — both of which call the single compression
`hash/blake2b.rs::f`. No C++ source and no protocol semantics were changed.

## 1. Reading the code (Step 1)

The current implementation was read first, before any edit:

- `blake2b.rs::f` works on 64-bit words already; the 32-bit wrappers (`earlier_hash_c`,
  `compress`) convert each call (16 + 16 words), a small per-compression overhead.
- The rotations use `u64::rotate_right`. The RV64IM target has no rotate instruction; rustc lowers
  `rotate_right` to a funnel shift (`fshr`), and LLVM lowers that to shifts + or. Writing
  `(x >> n) | (x << (64 - n))` by hand is the same code.
- `g` is `#[inline(always)]`; `f` is `#[inline]`. The twelve rounds are a runtime loop
  (`for r in 0..12`), and inside it `m[SIGMA[r][2 * i]]` is a dynamic, double-indexed lookup: the
  SIGMA row and the message word are not compile-time constants unless the loop is unrolled.
- `IV` and `SIGMA` are `const` arrays; `v` is a 16-word local with dynamic indices (`v[a]`, …).
- There were no explicit unrolling pragmas.

Hypotheses for the hot spots: the un-unrolled round loop and the dynamic SIGMA/message indices;
everything else (word width, rotations, inline hints) already looked reasonable.

## 2. Microbenchmarks (Step 2)

`zkvm/bench` is an independent SP1 guest with four modes (`0` current fp-core `f`, `1` handwritten
unrolled with explicit shifts, `2` `blake2b_simd 1.0.5` (no_std, portable path, one-block hash),
`3` the same unrolled code with `rotate_right`). It performs `n` compressions of one 128-byte block;
the cycles-per-compression figure subtracts the `n = 0` execution (~9.2k cycles) and divides by
`n = 4096`. `zkvm/host-exec/src/bin/bench-exec.rs` executes it. The bench ELF was built with the
S5a-1 final profile and `-Cllvm-args=-inline-threshold=1000`, so the comparison matches the
production build.

| Mode | Implementation | `n = 0` cycles | `n = 4096` cycles | Cycles per compression |
|---|---|---|---|---|
| 0 | current `fp-core::hash::blake2b::f` | 9,219 | 12,112,937 | **2,955.0** |
| 1 | handwritten, unrolled, explicit shifts | 9,221 | 9,315,377 | **2,272.0** |
| 2 | `blake2b_simd` 1.0.5 (no_std), 1-block hash | 9,222 | 8,189,013 | **1,997.0** |
| 3 | handwritten, unrolled, `rotate_right` | 9,223 | 9,270,318 | **2,261.0** |

- **Equivalence evidence**: modes 0, 1 and 3 commit identical public values after 4,096
  compressions (`sink=269ed10c9428e2c1`, `h0=a431fa3dc99b5208`, `h7=3400bdd87529d1ef`). Mode 2 is
  a cost reference only: `blake2b_simd` exposes the standard BLAKE2b hash, not the verifier's custom
  counter/tweak, so it cannot replace `f` directly.
- **The stated premise is refuted**: the current compression costs **2,955 cycles**, not ~238k.
  The verifier performs 136,088 compressions (`q_V`); at ~2,955 cycles each that is about
  **0.40G of the 27.18G total (1.5%)**. Most of the guest's cycles are in the verifier's own
  planning and checking code (big-integer arithmetic, allocation, plans), not in BLAKE2b.
- **Best equivalent implementation**: the unrolled compression (mode 3, `rotate_right`), 2,261
  cycles, 23.5% faster than the current one. Mode 1 (explicit shifts) is statistically the same
  (2,272; the difference is noise). `blake2b_simd` is faster per compression (1,997) but needs a
  third-party crate in fp-core and does not expose the tweak API; it is not usable as a drop-in.

The whole-call projection of integrating the unrolled version is
136,088 × (2,955 − 2,261) ≈ **94M cycles, about 0.35%** of the S5a-1 total.

## 3. Replacement (Step 3)

**Selected**: the hand-written unrolled compression (`rotate_right` form, mode 3). It is
bit-equivalent to the current compression on the benchmark's 4,096 compressions and 23.5% cheaper
per compression. It is written by us, so no third-party crate enters `fp-core` and no dependency
decision is needed.

**Not selected**: `blake2b_simd 1.0.5`. It is the fastest candidate per compression (1,997), but it
would be a new dependency of `fp-core` (only `libm` is approved there) and it exposes the standard
BLAKE2b hash — not the verifier's custom counter/tweak — so it cannot be the `f` that `f2b` and
`compress64` call. It stays a cost reference in `zkvm/bench`.

The change: in `fp-core/src/hash/blake2b.rs`, `f`'s round loop became twelve unrolled
`rounds!` calls; `g` now takes the round's two message words and the four state indices, so every
array index is a compile-time constant. `SIGMA`, `IV`, the counters and the public API are
unchanged; `compress64`, `compress`, `earlier_hash_f` and all callers are untouched.

The measured whole-call effect and the full regression follow.

## 4. Acceptance (S5a-2)

With the unrolled compression in `fp-core`, the same accepted example executes in
**27,079,048,885 cycles**, against the S5a-1 final 27,176,326,759: **−97,277,874 cycles (−0.36%)**,
and against the original S5 baseline 32,385,267,062: **−16.39%**. The consistency gate passes
(`result-v1 IDENTICAL`, `YES IDENTICAL`), the guest exits 0, and the ELF is 12,165,856 bytes.

The measured saving matches the projection (136,088 × 694 ≈ 94M cycles): the small whole-call
effect is not a failure of the new compression; it is the direct consequence of BLAKE2b being only
about 1.5% of this call's cycles.

The full regression is green: `cargo test --workspace` **229 passed, 0 failed**;
`scripts/parity.sh` **31 passed, 0 failed**; `scripts/parity_e2e.sh` **3 passed, 0 failed**;
`scripts/parity_negative.sh` **70 passed, 0 failed** (rejection-name checklist 11/11).

## 5. What the numbers say

- The S5a-2 premise "the current compression costs ~238k cycles" came from dividing the call's
  total by `q_V`. The microbenchmark shows the compression itself costs 2,955 cycles; the call's
  136,088 compressions are ~0.40G of 27.18G cycles (1.5%).
- The verifier's remaining ~26.8G cycles are its own planning and checking code: the exact
  big-integer arithmetic (`Big`/`Real`), allocation and the large plan structures. The next
  meaningful step, if the PM authorizes one, is to profile that code, not BLAKE2b.
- The benchmark harness is kept: `zkvm/bench` (four modes) and
  `zkvm/host-exec/src/bin/bench-exec.rs`; it can measure any future compression change against the
  same protocol.

# S5a-3: profiling the verifier's own code

## Step 0: localization

The instruments: `host-exec` now prints the execute report's full opcode distribution (top 20 plus
"other"), and takes `--part 0|1|2|3` (whole call / key alone / leaf alone / request alone). The
guest gained a `part` input; a partial run executes one stage and commits its text, and `host-exec`
skips the consistency comparison for it. The full run still passes the gate. All changes are in
`zkvm/` only; no `fp-core` and no C++ change in this step.

Full call with the instruments: **27,055,820,319 cycles**, `result-v1`/`YES` IDENTICAL. (This is the
new measured baseline for S5a-3; it differs from S5a-2's 27,079,048,885 by a code-layout shift of
the instrumented guest.)

### Opcode distribution (whole call)

| Opcode | Cycles | Share | | Opcode | Cycles | Share |
|---|---|---|---|---|---|---|
| add | 3,819,218,385 | 14.12% | | beq | 698,642,841 | 2.58% |
| addi | 3,490,021,164 | 12.90% | | bne | 676,091,903 | 2.50% |
| sub | 2,414,953,211 | 8.93% | | mulhu | 504,601,414 | 1.87% |
| and | 2,111,775,807 | 7.81% | | lui | 417,181,068 | 1.54% |
| sll | 1,936,498,578 | 7.16% | | bltu | 386,310,842 | 1.43% |
| ld | 1,823,290,774 | 6.74% | | lwu | 301,863,665 | 1.12% |
| srl | 1,791,639,825 | 6.62% | | xor | 270,595,368 | 1.00% |
| sltu | 1,544,485,031 | 5.71% | | bgeu | 263,058,852 | 0.97% |
| sd | 1,511,831,884 | 5.59% | | auipc | 239,974,342 | 0.89% |
| or | 1,002,133,828 | 3.70% | | other | 1,106,567,209 | 4.09% |
| mul | 745,084,328 | 2.75% | | | | |

Grouped: arithmetic/logic (`add`, `addi`, `sub`, `and`, `sll`, `srl`, `or`, `sltu`, `xor`) **~68%**;
loads and stores (`ld`, `sd`, `lwu`) **~13.5%**; branches ~7.5%; `mul`/`mulhu` ~4.6%; address
materialisation (`lui`, `auipc`) ~2.4%. There are no `div`/`rem` in the top 20.

### The three stages, measured separately

| Part | Total cycles | Share of the full call | Opcode notes |
|---|---|---|---|
| key | 5,716,271,928 | 21.1% | addi 15.9%, add 11.6%, srl/sll 8.3/8.3%, and 7.0%, ld/sd 6.2/5.8% |
| leaf | 5,562,665,955 | 20.6% | addi 15.5%, add 12.1%, sll/srl 8.2/8.1%, and 7.1%, ld/sd 6.0/5.7% |
| request | 15,875,165,332 | 58.7% | add 15.8%, sub 11.3%, addi 10.9%, and 8.3%, sltu 8.1%, ld 7.2%, sd 5.5%, mul 3.2%, mulhu 2.6% |

The three parts sum to 27,154,103,215 against the full call's 27,055,820,319; the 98,282,896
difference is about twice the per-execution prefix (guest start-up plus reading the private input,
~49M each), with the call assembly negligible.

**Caveat**: every partial run also performs the shared `setup()` (policy scan, layout, shape plans,
`configure`); the full call performs it three times (once per stage). The measured ratios are
therefore not pure stage-body shares, and the key/leaf parts, which are almost equal (5.72G vs
5.56G), mix the same setup with two similar table checks.

### Preliminary hypothesis

1. **Exact big-integer arithmetic (`Big`/`Real`) is the largest head.** Arithmetic/logic is ~68% and
   loads/stores ~13.5%, with `mul`/`mulhu` ~4.6% and no division in the top 20: this is the
   limb-by-limb shape of the ported `Big`/`Real` operations, their comparisons, and the
   `Vec<u32>`/`Vec<u64>` traffic they cause. BLAKE2b is only ~1.5% (S5a-2), so this is the
   verifier's own analysis and checking code, not hashing.
2. **Allocation and copying** show up as the ~13.5% of loads/stores plus the address materialisation
   (~2.4%): `Big`/`Real`/`Bound` are `Vec`-backed, cloned freely in plans, accounting and printed
   figures. `format!`-built strings contribute here too.
3. **The repeated setup** is unmeasured on its own. It is included in every partial run and paid
   three times in the full call; it builds all shapes and plans (`build_links`, the layer/head
   plans, the attention plans). Its size decides whether caching it across the three stages is the
   first thing to do.

### Step 1 candidates (for the TL's ordering)

- **Measure setup alone** (a plan-only/spy path in fp-core, or one more `part` mode that stops after
  `setup`): decisive for a reuse-across-stages optimization, which would otherwise be blind.
- **`Big`/`Real` fast paths**: inline storage for one- and two-limb values instead of a heap `Vec`,
  `u64`/`u128` fast paths in add/sub/mul/compare, inlining the hot element-wise loops.
- **Allocation/copy reduction**: `with_capacity`, buffer reuse, fewer `clone`s of `Big`/`Real`/
  `Binding`s in plan construction and accounting, and fewer `format!` allocations in the printed
  paths.

The instruments (`--part`, the opcode dump) stay in `zkvm/` for the next rounds.
