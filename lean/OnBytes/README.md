# verify-on-bytes: a hand translation of cp_verify into Lean

Terms: [TERMS.md](../TERMS.md); this folder's words: [GLOSSARY.md](GLOSSARY.md).

`verify-on-bytes` is the Lean text below `OnBytes.Main`: a hand translation of `cp_verify` into
Lean, from which this repository builds no stand-alone program; one test (`tools/accepts/`) compiles
it and has Lean load the compiled code while it evaluates files of `lean/Ask/`. Below, "the program"
is a stand-alone program built from that text; this repository builds none, and the calls told here
were made with builds of copies of the sources that differ from this repository's. The program reads
the same proof files as the C++ verifier `cp_verify`, in the same byte format, which this
repository's format specification (`docs/format/FORMAT.md`) defines, and it takes the same
arguments. It follows `cp_verify`'s source, and is a test tool.

It is not `verify`, the Lean verifier that is proved sound in the random-oracle model, at exact
match ([lean/THEOREM.md](../THEOREM.md)), and it does not run it. To run that verifier's executable
form on a proof, use `lean-verify` (THEOREM.md says how, and what you then trust). Definitions under
`OnBytes/` are also used beneath that theorem ([lean/README.md](../README.md)). Below, `verify`,
`verify -key` and `verify -leaf` are commands of `verify-on-bytes`. These pages use the programs'
words (key file, commitment ID); [LIMITS.md](LIMITS.md), "Which verifier", gives TERMS.md's terms
for them.

**No soundness theorem reaches a call that checks a real proof, and no theorem bounds the chance
that the program accepts a false file.** No security level is claimed for it; nor does any soundness
theorem cover `cp_verify`'s answer. **The program follows `cp_verify`'s source text, so the two
programs are not independent:** where they agree, that is not independent evidence.

| page | what it holds |
|---|---|
| [THEOREMS.md](THEOREMS.md) | what is proved about the program, theorem by theorem, and what each does not say |
| [LIMITS.md](LIMITS.md) | the program's limits, its known differences from `cp_verify`, and what has been tested |
| [Slice/README.md](Slice/README.md) | the files on one protocol of the format, the link between the first table and a copy |
| [Guard/README.md](Guard/README.md) | the build-time guards on the program's compiled code |

## What is proved

"Is proved" means accepted by Lean's kernel ([CHECKING.md](../CHECKING.md) says how to check it).
All theorems concern the Lean source, not compiled code.

- *From the real calls: which checks said yes.* If the program's entry function `main` returns 0,
  then in Lean's model of input and output its key, entry and proof checks each said yes on the
  bytes it read, and the ID behind `-id` among the call's options is the commitment ID it computed
  from the checked key table (`main_zero`, `main_zero_id`, `main_zero_named`). This claims nothing
  on soundness: it does not mean that the proof is correct or that the reply is the model's, and
  nothing is thereby "checked at 128 bits". The bytes are the answers of the program's reads in that
  model: nothing says that they are a file's content.

[THEOREMS.md](THEOREMS.md) has these statements whole, with their limits, and the other main
theorems.

## What a proof claims, and what a passing result means

**What a proof claims.** In one pass of the integer model (not the floating-point model) over the
request's T tokens, with the committed weights, the checked tokens meet the acceptance policy (the
paper's definition of the acceptance policy) in the public files, and the next token, if it is
checked, is the model's top choice, whatever the policy. This repository's documentation of the
protocol explains this in full.

**What a passing result means.** A passing result is `YES` or `WITHIN LIMITS: ...`, both with exit
code 0. It means that every check that this program makes of that claim passed, and that the call
qualifies as a verification: the caller supplied the commitment ID with `-id` and did not lower
`-bits` below 128 (more than 128 is rejected), the public files meet the standard conditions (format
specification, sections 13.7 and 14.4), and, if the call had `-no-proof-of-work`, no round needs its
work to meet the target. A passing result is also no better than the caller's own inputs.
`docs/verifying.md` explains where the ID must come from, who must write the request, and which
policies give only weak guarantees. No verifier can test how the provider created the commitment or
generated its randomness, so no result says anything about hiding. Nor do this folder's theorems.

**What a second program is worth.** `cp_verify` is faster, and it is the program that the rest of
the documentation describes. That both programs accept can guard against an implementation bug in
just one of them. It does not guard against a design flaw or a shared mistake, because this program
follows the C++ sources. Where only one program accepts a call, and [LIMITS.md](LIMITS.md) does not
list the case, one of them has a bug. Which values the lines of a parameter file may have is
`cp_verify`'s to judge: this program admits some that `cp_verify` and the provers refuse
([LIMITS.md](LIMITS.md), point 16). To report a security problem: [SECURITY.md](../../SECURITY.md).

## The most important limits

Each is told, with the tests behind it, at its point of [LIMITS.md](LIMITS.md).

- The printed bits are per-round figures of an accounting that rests on theorems and steps that this
  folder does not prove. They are not a security level (point 4).
- Among other gaps, two properties that a proof's claim depends on have not been proved, and a
  policy that passes the test for empty policies can still bar no token (point 5).
- In one experiment, on copies of the program, for most model checks (263 of 378), removing the
  check changed the result of no full call (point 7).
- In a second experiment, faults put into the program one at a time were run on honest calls alone
  (point 7).
- Checked tokens have faced no lying prover's proof at the default setting, and no false proof has
  been tested at full size (points 8 and 10). Proofs have been tested at few combinations of model
  options (point 9).
- A `YES` rests on the theorem on codes, which this folder takes as given. The library proves a Lean
  statement that stands in its place (`Cb/Bridge/CodeListRSProved.lean`; point 4); no theorem ties
  that statement to a program. At the default setting a `YES` also leans on counted proof of work,
  and no soundness theorem of this folder is stated at that setting (points 4 and 11).
- In a few cases this program could accept public files that `cp_verify` rejects, so do not assume
  that it is at least as strict (points 15 and 16).
- Nearly all tests used synthetic weights. Build-time tests apart, the test runs were made on builds
  of copies of the sources that differ from this repository's, none on a build of this repository's
  sources ("Tests").

## The command line

This repository holds this program's sources, not a compiled program, and `lakefile.toml` names no
target that builds one. A call has this form:

```text
verify-on-bytes verify <config folder> <ivk folder> <request file> <y file> <proof file>
    -id <64 hex digits> [-bits N] [-next-token] [-policy kind,C,theta,cap,s,sh]
    [-no-proof-of-work]
```

`lake build` checks the theorems of [THEOREMS.md](THEOREMS.md) and runs the guards of `Guard/`; it
builds no program. Arguments and options are the same as for `cp_verify` (`verifier/README.md`);
`-q`, `-j` (1 to 256; any other value is an invalid command line) and `-show-stages` are accepted
but change nothing. The program runs on one thread. On the stored small example a call took about 7
s and 0.3 GB (eight calls); at full size 121 s and 5.2 GB, against 25 s and 3.4 GB in a `cp_verify`
that can use several threads and was no build of this repository's sources (one call each, on a busy
machine; all with another C compiler than Lean's release brings: [CHECKING.md](../CHECKING.md),
"Before you start"; [LIMITS.md](LIMITS.md), "Tests").

`verify -key` checks the key file and reads no copy's file. `verify -leaf` checks a copy's file
against the root in the key file, and does not check the key file's proofs. `plan <config folder>`
prints a digest of each chain's parameter bytes; `cp_verify` has no call that prints these. The
other five commands (`product`, `links`, `key`, `entry`, `toy-proof`) check files of small test
protocols. They are no verification of a model's files, and they accept any `-bits` up to 1,000,000,
even 0.

## Results

A result consists of the last line of standard output and the exit code. Both are meant to be the
same as for `cp_verify`, apart from `TEST FILES PASSED`; [LIMITS.md](LIMITS.md), points 11, 14 and
15 to 21, lists the known differences.

| last line | exit code | meaning |
|---|---|---|
| `YES` | 0 | passed. The policy is exact match, or only the next token is checked |
| `WITHIN LIMITS: ...` | 0 | passed, for checked tokens under the policy shown, which the call must have stated with `-policy` |
| `NOT-A-VERIFICATION` | 14 | no check failed, but the call does not qualify, or it had `-no-proof-of-work` and work is counted |
| `NO: <name>` | 1 | a check failed |
| `NOT CHECKED: <name>` | 5 | nothing was verified: an internal check of the verifier failed (by `verifier/README.md`, a rare challenge value can also cause that in `cp_verify`, and nothing rules it out here), or this program does not support the parameter file |
| `PART PASSED: key` or `leaf`; `TEST FILES PASSED` | 3 | `verify -key`, `verify -leaf` or a test command reported no errors. Only the last line tells them apart. None of them is a verification |
| `PLAN ONLY: no proof was checked` | 4 | the `plan` command |
| `input-unreadable-...`, or nothing | 2 | no result: an unreadable input file or an invalid command line |
| unreliable | 15 | the answer could not be written: the call counts as not made |

Every other outcome is a broken run: neither an acceptance nor a rejection. This includes exit code
1 *without* `NO: ...` as the last line, which is how the Lean runtime exits if it runs out of memory
or cannot start. A `NO` is not evidence that the provider cheated: an overlong file or a bug in this
program also produces one.

**Closing lines.** Above the last line, under the heading `---- the call ----`, a full call prints,
among other lines, the commitment ID, what the result covered (`covered:`), `weight hiding: NOT
CHECKED BY THIS CALL (...)`, on what the proximity terms of the committer's files rest (`commitment:
...`: "the proved lemma", see `../GLOSSARY.md`; the line ends "; the table has a record: the binding
of the weights rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given": read
that last clause; "the binding of the weights" is the programs' own printed word, and nothing of it
is proved in Lean of the programs; [LIMITS.md](LIMITS.md), points 4 and 11), the line on proof of
work, and `result-v1 ...`. If a call ends in `NOT-A-VERIFICATION`, lines directly under the heading
can name a cause. One reads:

```text
the call: not the standard parameter form: id-named (the call named no ID: add -id with the commitment ID)
```

The other has the name `no-proof-of-work` and also says how many rounds need their work. This
program prints only these two causes. `cp_verify` also repeats the causes that its stages found, a
`-bits` below 128 among them. So the causes printed here may be incomplete: a full call with `-bits
100` and without `-id` prints `id-named` alone; with `-id` added it ends in `NOT-A-VERIFICATION`
again, and prints no cause. The line `result-v1 ...` repeats the outcome as name=value fields for
scripts, including the proof-of-work figures (`work=`, `work-rounds=`, and the weakest round with
and without its work counted, `least-round=` and `least-round-without-work=`), which the last line
and the exit code do not show.

**Proof of work.** A passing result may depend on it, and at the default setting it does: there
`-no-proof-of-work` ended in `NOT-A-VERIFICATION` in all 11 calls tried, one on each of 11 honest
sets, 3 of them at full size, and the truth of an accepted request and the binding of the weights
both lean on counted proof of work in the rounds that draw positions ([LIMITS.md](LIMITS.md), point
11). `prover/examples/TARGET-KITS.md` tells that setting's lines. The closing line is either `proof
of work: none counted` or a line that begins `proof of work: up to N bits counted in M rounds;` and
goes on `with it the least round has X bits, without it Y bits`: the most work that the parameter
file requires in any round, the number of rounds that meet the 128-bit target only if their work is
counted, and the weakest round with and without its work. A result does not rely on proof of work if
that line reads `none counted`, or if the call had `-no-proof-of-work`: every check still runs. If
some round meets the parameter file's target only with its work counted, a call that would have
passed ends in `NOT-A-VERIFICATION` (exit code 14) instead, and a line under the heading names the
cause; a call that fails a check ends as it would without the option. `verify`, `verify -key` and
`verify -leaf` take the option; a `plan` call with it is an invalid command line (exit code 2).

## The guards on compiled code

A theorem is about definitions; a program runs compiled code. Fifteen commands in
`Guard/Program.lean` look, whenever the whole library is built (`lake build`), for the marks by
which Lean lets the two differ (a compiler rule, `implemented_by`, `extern`, `opaque`, `unsafe`,
`partial`) and for some other ways in which the compiled program could part from the definitions
that the theorems are about; if one rejects something, the default build fails. They catch a slip
and the plain written forms. They do not stop someone who runs code at compile time in a file that
the program's root imports. They do not compare compiled code with a definition, and they cover
neither Lean's compiler and runtime nor the C compiler. [Guard/README.md](Guard/README.md) says what
each command checks, what to do when it rejects, and what it does not reach.

## Layout of the folder

| where | what |
|---|---|
| `Base.lean`, `Walk.lean`, `Result.lean`, `Shell/`, `Main.lean` | shared types; the command-line logic; the few lines that touch the operating system |
| `Field/`, `Hash/`, `Chain/` | field arithmetic, the format's two hash functions, the reader |
| `Params/`, `Plan/` | deriving each chain's schedule of rounds from the public files |
| `Iop/` | the protocol's building blocks |
| `Key/`, `Entry/`, `Proof/`, `Model/` | the three kinds of file; the model checks |
| `ChecksWithHashAsArgument/` | the same checks written out once more, with the hash as an argument; `main` runs four of them ([LIMITS.md](LIMITS.md), point 24) |
| `Toy/` | the small test protocols |
| `Tie/`, `Slice/`, `Guard/` | theorems and build-time checks; the program imports none of them |
| the other subfolders (`Flat/`, `K/`, `TypedOracleCompiler/` and others) | further files, among them definitions that are used beneath the theorem of THEOREM.md and, in `Dry/` and `Prover/`, lemmas and a prover that the conditional theorem on index privacy uses. Each has a header comment on what it holds; not every one says what the file does not claim. These pages do not describe them, but for "The copy's file alone" on [THEOREMS.md](THEOREMS.md) |
