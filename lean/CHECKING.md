# Building and checking the Lean library

Terms: [TERMS.md](TERMS.md).

One script checks the Lean files of the library, and with them the six theorems on `compile
(flashProve setup)` and the soundness theorem on `verify` (what they say: [LIMITS.md](LIMITS.md),
"What is proved, and of which object"): `python3 -B scripts/check.py`, from `lean/` (the files under
`Ask/` are run by their own commands). It checks the files' text, builds the library from nothing in
a scratch copy, has Lean's kernel check the compiled modules a second time (the replay), and audits
the axioms and the kind of every declaration. This is *the full check*. It takes hours and a large
machine: "What you can do, and on what machine", below; the commands themselves: "The commands",
below. Its build step names all three libraries of `lakefile.toml` in one call, `ShapeLines` too,
three of whose files no other target reaches, and hands Lake a bound on parallel work, which that
library's heavy files need ("What you can do, and on what machine", below). The library's full check
has been run over this repository's files, whole, and has passed
([CHECK-RESULTS.md](CHECK-RESULTS.md)). One Lean file, with one definition and four theorems, which
nothing else imports, was added after the runs reported here and checked on its own
([CHECK-RESULTS.md](CHECK-RESULTS.md)). Three of the check script's pinned values were changed and
three of its stored lists were extended for it; nothing else in the script or the lists changed.
Over a copy of the Lean files that differs from this repository's, two things were seen to fail: the
audit under a limit of 48 GiB of address space, and 23 modules under `leanchecker`, with "deep
recursion detected"; what the script does about each, and what is not measured, is told below.

In the replay 1,439 modules of two libraries (`AtFullSide/`: 915; `ShapeLines/`: 524) are replayed
by Lean's own replay under a wider stack, not by `leanchecker`: every module of a library that
`lakefile.toml` compiles at a larger thread stack goes that way
([scripts/README.md](scripts/README.md), **replay**). What is shown of the need was seen over Lean
files that differ from this repository's, with 901 modules in `AtFullSide/`: 22 of them stopped
under `leanchecker` with "deep recursion detected", six of them in a whole run of the script over
those files, one to a job, and so does `AtFullSide/Layout/TieRfl.lean` (seen on two machines); each
of the 23 went through under Lean's own replay at the wider stack, its four lines of Lean lying in a
file, where the script hands them to Lean on standard input. For the other modules of these two
libraries no such need is shown; the rule sends them to Lean's own replay all the same. 878 of the
901 passed under `leanchecker`, so for such modules the second check could be made by that program
and is not. Of `ShapeLines/` nobody has tried which modules need the wider stack.

Code that runs at build time can replace the code that does the replay under the wider stack, and
this is not the only such way: the call imports a module `LeanChecker` by its name on the search
path, so a file `LeanChecker.olean` placed there by such code would be imported instead, unnoticed.
This affects every one of the 1,439 modules: for none of them does the standalone program
`leanchecker` make the second check (`scripts/RULES.txt`, "One module is replayed by another call",
"A road that is open").

With Lean, a call of the form that the script makes for the replay under the wider stack was made
apart from the script on one module of `AtFullSide/` (status 0, its closing line once) and on a
module that does not exist (status 1, no closing line). A small program, not the script, that makes
this call with the same command line and the same four lines, but with `LEAN_NUM_THREADS=8` for each
process where the script sets 1, made it for all 1,438 such modules of one built copy of the
library, 28 at a time: each ended with status 0 and its closing line once. That copy had 914 modules
in `AtFullSide/` and 524 in `ShapeLines/`; whether its files were these to the byte was not checked.
In the whole run over this repository's files the script's own step made the call for all 1,438 such
modules: each ended with status 0 and its closing line once ("What you can do, and on what machine",
below).

Each process of the audit may reserve at most 96 GiB of address space. In a whole run over a copy of
the Lean files that differs from this repository's (29,905 modules) the script's own audit step
failed under a limit of 48 GiB: its process ended with "failed to read file" while it imported,
before any verdict. The same audit file, run apart from the script, failed so again under 48 GiB and
went through under 96 GiB ("ALL PASSED"), with a peak of 53.0 GiB of address space at
`LEAN_NUM_THREADS=24` on 84 cores. The peak at more threads, or on a larger library, is not
measured.

What has been run of the full check: [CHECK-RESULTS.md](CHECK-RESULTS.md). What each step of the
script shows and does not show: [scripts/README.md](scripts/README.md). How to check the soundness
theorem on `verify` itself and how to run `verify`'s executable form on a proof:
[THEOREM.md](THEOREM.md), "How to check it" and "The executable form, and how to run it". All of
this is about the protocol as written in Lean. Nothing is proved about the released programs (the
C++ verifier and committer and the CUDA prover), nor that they run the protocol that `verify` checks
([README.md](README.md)).

Run everything as an ordinary user, not as root and not under `sudo`. As with any Lean project,
building runs code from the repository (macros and tactics) as your user. Only installing system
packages needs root.

## What you can do, and on what machine

A build (step 4) shows that Lean has compiled every file and that its kernel has checked each proof
that is there; it does not fail on a `sorry` or on a new axiom. The full check (step 5) adds the
checks of the files' text, a build from nothing, so that no compiled file of yours is trusted, the
replay, the audit and a listing of the named theorems' statements as compiled. Its text steps alone
(`--only tree,words,imports`) need no Lean.

The library holds some 30,000 Lean files. A memory limit is what a run is allowed, no measure of
what the check needs. Chance decides how many of the heaviest files meet, and a scratch directory in
memory comes on top of the processes' own memory.

**The files of `ShapeLines/` are the heaviest.** A plain `lake build` reaches nearly all of them,
since the side library imports them. Compiling `ShapeLines/` over this repository's files took 39
minutes by the clock, on one machine, held to 84 cores and 960 GiB of memory, with up to 56 files
compiled side by side. Added up file by file, Lake's own times for its 524 modules come to 20.2
hours: that is the work done, not the time waited. Its heaviest stage, 310 modules, took 16 minutes
at `LEAN_NUM_THREADS=48`; the dearest module took 879 seconds. In samples taken every ten seconds
the largest process had 48.6 GiB resident, and all processes together at most 595 GiB of memory of
their own ([ShapeLines/README.md](ShapeLines/README.md), "How to build, and what it costs"). With
Lake's default, as many processes as cores, a common machine runs out of memory (reckoned, not run).
Set `LEAN_NUM_THREADS` to what the machine's memory bears. `lake build ShapeLines` builds also three
of its files that a plain `lake build` does not reach: two hold controls, one a closed fact
([GLOSSARY.md](GLOSSARY.md), "control", "closed fact"). Of the rest of the library by itself no time
is told; the next paragraph tells what the build from nothing took in the whole run over this
repository's files.

The whole run over this repository's files took 4 hours 26 minutes, by the clock, on one machine,
held to 84 cores and 960 GiB of memory, with `LEAN_NUM_THREADS=72`, 48 replay jobs and 24 processes
at a time under the wider stack (given by `--wide-jobs 24`): 8 minutes for the copy and the text
steps, 1 hour 39 minutes for the build from nothing, 2 hours 24 minutes for the replay and 14
minutes for the audit. Apart from that run: the audit, run apart from the script, over Lean files
other than this repository's, took 13 to 22 minutes where the limit on its address space left it
room; on which machines, and with how many threads, is not on record.

The script asks for 21 GiB of available memory at its start, before the build, before the replay and
before the audit (7 before the audit with `--jobs 1`). These are floors, not needs, and they do not
guard against the heaviest files. For those the script hands `lake build` a bound on parallel work:
your `LEAN_NUM_THREADS`, taken as it stands, or else one process, and one more for each 12 GiB of
available memory beyond 50, at most one for each core (one, where the free memory cannot be read).
The 50 and the 12 are a rule of thumb: 50 is 49.1 GiB rounded up, the greatest resident memory of
one process in one build of `ShapeLines/` at `LEAN_NUM_THREADS=16`, by samples taken every five
seconds ([ShapeLines/README.md](ShapeLines/README.md), "How to build, and what it costs", under the
first table); for 48 processes the rule counts 614 GiB (50 + 47 × 12), and what the processes of the
heaviest stage told above held together at `LEAN_NUM_THREADS=48` is close to that, so the rule
leaves little room, or none (`scripts/RULES.txt`, "The build", "The bound on parallel work"). None
of the whole runs told on this page tested the two numbers. Your `LEAN_NUM_THREADS` also reaches the
audit; a bound that the script works out does not, and Lean then chooses its own number of threads.
Each process of the replay runs with one thread.

The modules that are replayed under the wider stack come first, one process a module. How many run
at a time is `--wide-jobs N`, if you give it. Otherwise it is the lowest of three numbers: that
bound; the number of the replay's jobs; and a rule of thumb of its own, one process and one more for
each 40 GiB of available memory beyond 50, which holds also where you have set `LEAN_NUM_THREADS`.
The 50 is taken over from the build. The 40 GiB are 39.4 GiB rounded up, which one process was seen
to hold of its own in two of the trials told here.

The small program told above was run three times on 84 cores, under a limit of 800 GiB on the
processes' own memory (the program's processes ran with `LEAN_NUM_THREADS=8`, where the script sets
1: all figures of these three trials are of that setting). 72 at a time held 819 GiB after 7 minutes
52 seconds, and 40 at a time 803 GiB after 12 minutes 20 seconds. Both trials were ended when they
had passed that limit; no call had failed among the 300 and the 400 that were reported by then; the
largest process held 29.5 and 32.6 GiB, mapped files counted. 28 at a time went through for all
1,438, in 35 minutes 11 seconds (another job shared the machine in the last minutes): the highest of
the samples, taken every 30 seconds, was 568 GiB held together, a figure that counts the whole
machine, and 39.4 GiB of its own for one process. In another trial 24 at a time went through for the
524 modules of `ShapeLines/`; in which form of the call is not on record.

At one thread, the script's own setting, the script's own step has made the call with `--wide-jobs
28` (in a form of the script that differs from this one only in three pinned values and in how it
works that number out where it is not given), as a part of a whole run over a library with 914
modules in `AtFullSide/` and 524 in `ShapeLines/`, whose files were not this repository's to the
byte, on 84 cores, under a limit of 800 GiB on the processes' own memory. The logs of all 1,438
calls were there after about 41 minutes, by the logs' times. What is told of that run is these
measures alone, no verdict. By samples taken every 60 seconds, which can miss a peak, the processes
held 577 GiB together at most, a figure that counts the whole machine, on which nothing else ran,
and one of them 39.4 GiB of its own: as much as at eight threads.

At 800 GiB available the rule gives 19 at a time, fewer than the 28 that went through under that
limit at eight threads a process, and than the 28 of the run at one thread, which stayed under it by
its samples. What the rule counts covers as many processes of 39.4 GiB as it allows. No process was
seen to hold more in these samples; one that does is not covered. Whether the rule is enough is not
known: none of the runs told on this page used it. A number given by `--wide-jobs` can ask for more
memory than a machine has, and so can your `LEAN_NUM_THREADS` where the script cannot read the
available memory.

The calls under the wider stack end before the jobs of `leanchecker` start. Of these the replay runs
up to 48 side by side, fewer on a machine with less memory, or as many as `--jobs` says. Where the
script cannot read the free memory (not Linux) and `--jobs` is not given, the replay starts one job
per core, at most 48, whatever the memory. On a smaller library the replay ran more than ten times
as slowly with the scratch directory on a container's overlay file system as on a disk with a file
system of its own, and one job of the replay wanted more than 21 GiB; how small a `--jobs` number a
machine with less memory needs, no run has tried.

## Before you start

You need Linux (x86-64; nothing here is tested on another system), `git`, `curl` and Python 3.9 or
later (tested with 3.13). On a minimal Ubuntu 24.04, for example (this line needs root; without
`ca-certificates` every https download fails):

```sh
apt-get update && apt-get install -y --no-install-recommends git curl ca-certificates python3
```

Lean is installed by `elan`, which reads the version from the file `lean-toolchain` (4.29.1). The
call is the one that Lean's own page gives (<https://lean-lang.org/install/manual>):

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

If the shell then says `lake: command not found`, open a new shell, or type `. ~/.elan/env`.

The first steps from scratch are untried: the installing of elan, Lean's download and the fetch of
the packages with Mathlib's compiled files from the public servers. The runs told on this page took
Lean as it was installed on their machines, and the packages as they were compiled beforehand,
without their git history; how these copies of the packages came, as far as it is known:
`lean/GAPS.md`, 81 (g).

**Which C compiler.** Lean's release brings its own (clang 19.1.2 and a linker). It is untried: the
machines of these runs hand Lean's generated C code to GCC 15.3.0 and GNU ld 2.46 instead. This
touches natively compiled Lean code alone: a stand-alone program built from `verify-on-bytes` (the
Lean text below `OnBytes.Main`: a hand translation of `cp_verify` into Lean, from which this
repository builds no stand-alone program; one test (`tools/accepts/`) compiles it and has Lean load
the compiled code while it evaluates files of `lean/Ask/`), `libvob.so`
([Ask/README.md](Ask/README.md), "The faster way"), the helper library behind the runs of `verify`'s
executable form, and the test program of `integrations/vllm/integer_model/tests/lean_vectors/`. With
Lean's own compiler expect other checksums of compiled files (inferred), and times and memory may
differ; another checksum alone is no sign of a fault. The full check links no program; that its
builds call no C compiler is inferred from how Lake works, not tested.

Use a fresh clone or a fresh unpack. Lake resets `.lake/packages` to the pinned revisions without
asking and can delete what it finds there, and a build replaces files under `.lake/build`. So do not
reuse a working copy in which `.lake`, or a directory in it, is a symbolic link or a mount point for
a directory that is used for anything else.

Only the installing of elan and steps 2 and 3 need the network. By reading the tools' sources, not
by a run: they download from github.com, release.lean-lang.org and lakecache.blob.core.windows.net.
Lean takes 2.6 GiB when installed; the packages take 6.5 GiB, their git history not counted. Files
are written to `.lake` in this folder and to elan's and Mathlib's caches under your home directory.

The script writes nothing in `lean/` (as long as no other account interferes). It makes one new
scratch directory, whose name begins with `lean-check-`, in the system's temporary directory or in
the directory that `CHECK_SCRATCH_DIR` names. At the end it removes its copy of the library; the
logs and the listing stay there, and its last lines say where. If another account could change that
directory's parent or a folder above it, a run with the step "build" refuses at its start, because
that account could put another folder in its place while the build runs: no step is run, and the
exit status is 1. A folder that only you or root can change, or `/tmp` with its sticky bit, will do.
On a machine where you trust every account, `--i-trust-every-account-on-this-machine` takes such a
folder all the same, and the first and last lines of the run say so. None of the whole runs with
Lake and Lean told on this page had its scratch directory in the default place, which most readers
will use: of what is told here and in `scripts/RULES.txt`, only the text steps, `--digest` and whole
runs with a small program in Lake's place went to their end there. Nor was any whole run with Lake
and Lean told on this page made under `--other-lake` (`scripts/RULES.txt`, "One copy", "How far
these trials go").

## The commands

All commands are typed in the directory `lean/`.

1. Check the build configuration. This compares `lakefile.toml`, `lake-manifest.json` and
   `lean-toolchain`, which decide what the next steps download and run, with SHA-256 checksums
   stored in the script, and refuses a `lakefile.lean`. It calls neither Lake nor Lean.

   ```sh
   python3 -B scripts/check.py --only tree
   ```

2. See that Lean has arrived. This step downloads Lean. The line ends with `(Lean version 4.29.1)`.

   ```sh
   lake --version
   ```

3. Fetch the packages with Mathlib's compiled files. `lake-manifest.json` names all nine packages,
   with their addresses and revisions. By reading Mathlib's tool, and by one run through a local
   mirror, a good fetch ends with the line `Already decompressed N file(s)`, also at the first run.
   An empty one prints `Decompressed 0 file(s)` and `No cache files to decompress`, with exit
   code 0. Through a local mirror this step has ended both ways on different machines, and why is
   not known: with every one of Mathlib's compiled files fetched, and with none; a fetch from the
   public servers, and going on after an empty fetch, are untried. A download that fails prints
   `Downloading N files failed`, with exit code 1.

   ```sh
   lake exe cache get
   ```

4. Build the library. `lakefile.toml` names three libraries: the main library and `AtFullSide` are
   default targets, and the files of `ShapeLines` (no default target) are built where those import
   them, which is the heaviest part of the build ("What you can do, and on what machine", above).
   Three of its files, two with controls and one with a closed fact, are reached by `lake build
   ShapeLines` alone. Lake starts as many processes as the machine has cores (on memory, and on
   `LEAN_NUM_THREADS`: "What you can do, and on what machine", above). Without
   `LEAN_ABORT_ON_PANIC=1` a build does not fail if Lean panics while it compiles a file: Lean goes
   on with a default value, and the build can end with exit code 0. Nor does `lake build` fail on a
   `sorry` or on a new axiom: step 5 looks for both. The build does not check Mathlib, which is used
   as downloaded.

   ```sh
   LEAN_ABORT_ON_PANIC=1 lake build
   ```

5. Run the script. It does not use the build of step 4: it builds in its scratch copy. So you may
   skip step 4, but not step 3: without the packages the script does not call Lake.

   ```sh
   python3 -B scripts/check.py
   ```

Its steps are called `tree`, `words`, `imports` and `build`. At success the last line begins:

```text
All steps passed: tree, words, imports, build (kernel replay, audit). This script runs no mutation tests and no second, independent proof checker (see lean/scripts/README.md). The result is about the compiled definitions:
```

That line also says that no theorem got a verdict on binders or on `Classical.choice`: every line of
`scripts/top-theorems.txt` says "general".

| exit status | what it means |
|---|---|
| 0 | all steps passed; with `--only`: "Partial run passed (…): only these steps were run" |
| 1 | "Check failed:" and the steps that failed; or, without that line, the refusal at the start: "no step was run, and nothing was built" |
| 2 | a wrong argument, a scratch directory that cannot be used, or a `lakefile.toml` from which the script cannot read the thread stacks ("Nothing was checked") |
| 3 | "Passed so far, and not the full check": no step failed, but part of a step was not run or had nothing to check (a line `NOT RUN` above says which), or the Lake files are not the expected ones |

The listing, `statement-listing.txt` in the scratch directory, has for each theorem that
`scripts/listing-for.txt` names its statement as compiled, also in full without notations, and the
names on which the statement depends, each with type and value. `sound_of_verify_at` is not among
them: of the soundness theorem on `verify` the run gives the statement and counts only.

## The six theorems, and eight more

Each of these theorems stands in a file that has, among its last lines, a `#print axioms` line for
its name. From `lean/`:

```sh
LEAN_ABORT_ON_PANIC=1 lake build AtFullSide.Face.TheSixLines E2E.SoundAsIOPAtFilesProofs AtFullSide.Honest.CompleteAtTheFiles AtFullSide.E2E.ZeroKnowledgeFromTheRows AtFullSide.E2E.TheCompiledStepFilled AtFullSide.Face.TheFinalStatementOneBitHolds AtFullSide.Face.TheFinalStatementHolds AtFullSide.Face.TheThreeAtTheFiles AtFullSide.E2E.CompleteWhereSomeWorstCaseCheckPasses > .lake/top_theorems.log 2>&1; echo "exit status: $?"
for n in VerifiableInference.sound VerifiableInference.soundAndBinding VerifiableInference.completeOnCanServe VerifiableInference.zeroKnowledgeOnCanServe VerifiableInference.refusedHandsOutNoProof VerifiableInference.repliesFit soundAsIOPAtTheProtocol complete_in_scope zkOnServedRequests_inScope finalAtT1_filled theFinalStatementOneBitHolds theFinalStatementHolds threeAtFiles_in_use theHonestPart_complete_where_some_worst_case_check_passes; do grep -A2 "[.']$n' depends on axioms" .lake/top_theorems.log || echo "NO ANSWER: $n"; done
```

In the order of the names these are the six theorems on `compile (flashProve setup)`
(`VerifiableInference.sound`, `VerifiableInference.soundAndBinding`,
`VerifiableInference.completeOnCanServe`, `VerifiableInference.zeroKnowledgeOnCanServe`,
`VerifiableInference.refusedHandsOutNoProof`, `VerifiableInference.repliesFit`:
[LIMITS.md](LIMITS.md), L93), and then soundness as an interactive oracle proof
(`AtPublicFiles.AtFiles.soundAsIOPAtTheProtocol`), completeness as one
(`AtFullSide.Honest.complete_in_scope`), honest-verifier zero knowledge before hashing
(`VerifiableInference.Compilation.zkOnServedRequests_inScope`), the compiled step
(`VerifiableInference.Compilation.finalAtT1_filled`), the final statement with the simulator told
one bit (`VerifiableInference.Compilation.theFinalStatementOneBitHolds`), the final statement with
the label shown (`VerifiableInference.Compilation.theFinalStatementHolds`), the three at one
protocol (`VerifiableInference.Compilation.threeAtFiles_in_use`) and completeness at weights that
pass the first worst-case check, or the least-bound check with numbers that hold
(`VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes`):
[LIMITS.md](LIMITS.md), L89 to L93. The build compiles about 28,000 Lean files, the heavy files of
`ShapeLines/` among them, and needs a large machine ("What you can do, and on what machine", above).
A module is compiled with the arguments of the library whose globs hold it, whichever target reaches
it, so Lake takes the thread stacks of `AtFullSide` and `ShapeLines` from `lakefile.toml` (tested:
one module, one call).

The exit status must be 0, and there must be fourteen answers, one for each name, each reading `…
depends on axioms: [propext, Classical.choice, Quot.sound]`, with nothing else in the brackets (an
answer of more than 120 characters Lean breaks over three lines, `[propext,`, `Classical.choice,`
and `Quot.sound]`; the last name's has 150). "NO ANSWER" means that nothing is shown for that name.
A build alone does not fail on an unfinished proof or a new axiom: that answer is what shows that
none lies beneath the name. It reads the compiled files and re-checks nothing. Run as they stand on
a build of this repository's files: exit status 0 and fourteen answers, each [propext,
Classical.choice, Quot.sound]. On a built tree Lake replays the messages of modules that were
compiled before, so the answers are those of the build that compiled them. `grep -A2` prints the two
lines after each match: of a broken answer the rest, else the next lines of the log, such as other
theorems' answers or lines "Replayed …". So the print has more than fourteen lines with "depends on
axioms": some of the fourteen names come more than once, names that were not asked for come too, and
such a neighbour's answer can be cut off inside its brackets. What counts is the answer to each of
the fourteen names.

## What a pass shows, and what it does not

The audit's verdict covers every declaration of the library: it depends on no axiom but `propext`,
`Classical.choice` and `Quot.sound`. Each theorem on `scripts/top-theorems.txt` also gets a line
with the axioms that it uses; the audit's verdict does not rest on the `#print axioms` lines in the
files. The statement on codes, which the library proves and which some theorems take as a
hypothesis, is not an axiom and does not show among a theorem's axioms ([LIMITS.md](LIMITS.md),
L15). A named hypothesis is a definition that a theorem takes as a premise: Lean's list of axioms
shows none of them, and "Lean's three axioms" says nothing on whether they hold.

Every line of that list is of the kind "general": the audit fails if the name does not exist, is no
theorem or rests on another axiom, and it prints the compiled statement; it gives no verdict on what
the statement quantifies over or on the use of `Classical.choice`. `scripts/front-statements.txt`
holds the compiled statement of each theorem that has a block there, the six theorems and the
soundness theorem on `verify` among them, and after the audit the script compares it with this run's
listing, to the letter: such a statement cannot be weakened under its name without notice. Some
blocks pin a name alone: the statement is compared, and the body of what it names is not. A theorem
without a block is compared with no stored copy: there you compare the listing with its Lean text
yourself, and what a page says of it rests on a reading of its file. Most theorems of
`VerifiableInference/` have no block, `SoundForWith.manyProofs` ([LIMITS.md](LIMITS.md), L82) among
them. Not caught either: a change to a definition that a statement names, after which the statement
reads the same and means something else.

The fourteen theorems of "The six theorems, and eight more", above, each have a line in
`scripts/top-theorems.txt`. The six also have a block in `scripts/front-statements.txt`; the eight
more have none. For these eight the audit looks each up by name, fails if it does not exist, is no
theorem or mentions no declaration of this library, and reports its statement, its axioms and what
the statement rests on. It gives no verdict on binders or on `Classical.choice`, does not compare
the statement with a stored copy, and does not test that the hypotheses inside the statement can be
met.

How far all this checking goes:
[LIMITS.md](LIMITS.md), "How far the checking goes".

**Paths in comments.** A path in a comment that you do not find in this repository, with or without
the mark "[not in this library]", names a file that is not here: no proof here depends on it, and
what a comment says on the strength of it is not shown in this repository. Three kinds differ. Some
comments cite Lean files under a shorter folder name, such as `ToldDesc/` for `Johnson/ToldDescR/`:
search for the file's name; that the file so found is the file meant is not checked. Some cite
source files of the C++ verifier: their text may differ from what a comment says of it, and Lean
reads none of them. A path into Lean's own sources or a package that `lake-manifest.json` pins,
Mathlib among them, names a file on which a proof here can depend, in the version that is pinned;
ArkLib and VCV-io are no such packages, and the files of `ThirdParty/MathlibBackport/` cite a newer
Mathlib than the one pinned: what a comment says on the strength of those is not shown here, except
where `ThirdParty/` holds its text in an adapted form.

No program in this repository compares the Lean text on [AUDIT.md](AUDIT.md) with the Lean files:
what a statement means is settled by Lean alone.

## The independent checker

The script runs no second proof checker. The independent checker is nanoda: the project
`nanoda_lib`, program `nanoda_bin`, version 0.4.13 (commit 418320295890faed83a96fd97907b12a3b6728c2;
<https://github.com/ammkrn/nanoda_lib>; Apache-2.0), "an external type checker for the Lean 4
programming language and theorem prover". It is written in Rust, by another author, in another
language than Lean's own kernel, and calls no Lean. It is set to permit Lean's three axioms and no
other. The binary was built from an archive of that source; that archive has not been compared with
the public repository, nor have the libraries that it is built with, beyond their locked checksums,
the compiler and the linker. The checker is trusted, not proved, as Lean's kernel is, and no run
shows this binary refusing a wrong proof.

It judges a text that this project's own exporter writes out of the compiled library: every
declaration on which the given names rest. So its yes is only as good as that exporter. Two more of
this project's programs count the text without Lean and read it back against the compiled library.
That shows that what is in the text is what the compiled library says, not that all that the library
holds is in the text, and it goes through the same two functions of Lean as the exporter, so that a
fault in those two functions would be seen by neither. All three are this project's own programs,
written by the same hands, and there is no record that the exporter was ever tried against a planted
fault. A verdict is a yes only if the checker ends without an error and the three counts of
declarations are equal.

Over a build of this repository's files the independent checker (that the compiled files that its
passes read were that build's is known from a report alone; Lean's own files were not compared with
a list of checksums) has accepted the soundness theorem on `verify` (`sound_of_verify_at`), with
every declaration beneath it, and nothing that does not lie beneath it, in a pass on that theorem's
export alone ([CHECK-RESULTS.md](CHECK-RESULTS.md)). Of the six, the independent checker has
accepted `sound`, `repliesFit` and `refusedHandsOutNoProof` by name, over a build of this
repository's files; over such a build the three on binding, completeness and zero knowledge have
been checked by Lean's kernel alone. So, but for the soundness theorem on `verify`, these three and
those on which they rest, no theorem of this repository has more than Lean's own kernel over this
repository's files: not the other three of the six, not the results on hiding
([LIMITS.md](LIMITS.md), L62 to L65), not the theorems on completeness and zero knowledge of L88 to
L93 there ([LIMITS.md](LIMITS.md), L80; `lean/GAPS.md`, 18 (b)).

But for what is said above of the independent checker, none of what follows was run over this
repository's files. At four theorems (`Bind.Cpp.extractsCommitted`, `Bind.Cpp.bindsAt`,
`Bind.Cpp.soundAtCommitted_own`, `AtFullSide.Top.theLive_zFull`) the checker cannot give a verdict:
what they depend on outgrows a limit of its own, a table of 2^31 entries. That is no refusal.

**You cannot run the independent checker over this repository's files as they stand.** The checker
is public, and the library and its lists of names (`scripts/claimed-theorems.tsv`,
`scripts/top-theorems.txt`) are in this repository; the exporter, the recount, the read-back and the
rule for a verdict are not. Whether the public exporter lean4export would serve in its place is
untried.

## The HTML pages

`STATEMENTS.html` shows statements and definitions, each Lean declaration in rows, with plain words
beside its whole Lean text. A second, long page, `STATEMENTS-ALL.html`, shows many more
declarations, each with its comment beside its Lean text; it is not in this repository: the first
call below makes it, in `lean/`, where its links lead. One generator makes both pages from the Lean
files and from text files under `scripts/statements-html/`, and one program, which `check.py` does
not run, checks the two together: that is the second call. From `lean/` (Python 3.7 or later, the
standard library alone):

```sh
python3 -B scripts/make_statements_html.py . STATEMENTS-ALL.html --front="$(mktemp -d)/STATEMENTS.html"
python3 -B scripts/check_statements_html.py . STATEMENTS-ALL.html --front=STATEMENTS.html
```

On success the second call's last line is "RESULT: all eight checks pass" and the exit code is 0.
"RESULT: N of the checks fail.": exit code 1. "CANNOT CHECK: …": exit code 1, nothing was decided. A
wrong call: exit code 2. The first call makes the front page too, as it must for the long page's
first line to lead to it; it writes that copy into a scratch folder, so that `STATEMENTS.html` stays
as it came. Called with the second call's arguments, `scripts/make_statements_html.py` makes both
pages in `lean/` and replaces `STATEMENTS.html`.

A pass shows that the pages show the files' own Lean text, whole (but for the numbers of sections,
definitions and propositions in the comments of the files that
`scripts/statements-html/unnumbered.txt` names, which they show as "…"), and no proof. It does not
show that words say what the Lean text beside them says; the plain words on those pages have not
been independently compared with the Lean text beside them (`lean/LIMITS.md`, L43).

The two programs read Lean files as text, by written rules, without Lean: a file written to deceive
them may still pass, for instance by a command of its own making, by notation from an imported file,
or where their rules on strings, comments and names part from Lean's; no such file is known in the
library. One author wrote nearly all of both programs, and the checker follows the generator's rules
step by step, so a mistake that both share passes unseen; no comparison of a card's text with the
statement that Lean prints is made.

The checker was tried on copies of the two pages with one planted fault each, with the generator and
the checker of this repository, on pages made from Lean files and data files other than the ones
here. Seven faults were planted, each alone. Three changed a number (688127 to 688128): on the long
page in a field of a structure; on the front page in the embedded lines of Lean; on the front page
in a visible line of a card. Four changed the front page's form: an empty chip was put at a card's
foot; the title of a group in the list of definitions was set back to its folder's name; a word that
the data files lack was added to that title; a sub-section's line was put into the contents. The
checker, run without its check 8 (`--skip-check-8`: check 8 makes the page again and compares bytes,
so it would refuse any change; the trial is of checks 1 to 7, which read the page itself), ended
with exit code 1 each time: check 1 failed at each changed number, check 5 at the chip and at the
contents line, check 3 at the two titles. On those pages as made, all eight checks passed.
`scripts/test_statements_notation_docstring.py` (16 small cases),
`scripts/test_statements_empty_chip.py` (9) and `scripts/test_statements_front_switches.py` (26)
pass on the two programs of this repository. Each was also run against copies of these two programs
in which the rule that it tests was taken out or loosened on purpose (4, 5 and 15 copies), and it
failed on every one of these. The trial with the seven planted faults was not made on pages made
from this repository's files. Check by check: the top of `scripts/check_statements_html.py`.

## The stored files and the examples

The goals of `Ladder.lean` ([TERMS.md](TERMS.md), table 2), and every theorem "at storedPublicFiles"
or "at zGap", are about two terms of `Ladder/Stored.lean`, `storedPublicFiles` and `zGap`, the
library's written copies of the two stored sets of public files. No theorem ties them to a file on
disk: that they match the files of `examples/full-size/config/` and
`examples/full-size-clipped-gap/config/` is checked by a script (90 comparisons, 11 of them against
this repository's example files), not by a theorem; run over this repository's files, it passed.
From `lean/` (under a second; the second call runs its negative tests, some fifteen seconds):

```sh
python3 -B scripts/check_stored_examples.py . ../examples
python3 -B scripts/check_stored_examples.py . ../examples --self-test
```

Exit code 0: every comparison holds; 1: one fails, or the program cannot go on; 2: a wrong call. A
row under A (an example file against the Lean text) or B (against a value in a test of
`Ladder/Guards.lean`) that says DIFFERS means that nothing said "at storedPublicFiles" or "at zGap"
may be read as said of these example files. CHANGED or CANNOT CHECK means that no verdict was
reached. Part B counts only for a library that was built from these very sources: the program looks
at no compiled file, so run it beside the steps `build` and `words` of `check.py`. It catches
accidents and drift, not a change made to deceive it, and says nothing about the other files of
these two folders' examples, nor about the two small examples.

## Asking files (`lean/Ask/`)

The files under `Ask/` lie outside the library. Each runs code of the library on stored files; these
runs are tests, and a yes from them is not a verification. Each one's head gives its command, its
time and memory, what its print means and what it does not mean. What they share, and the steps
before a run: [Ask/README.md](Ask/README.md).
