# lean/scripts: the audit script

Terms: [TERMS.md](../TERMS.md).

`check.py` audits the Lean library in the parent directory. `python3 -B scripts/check.py --help`
lists its options, results and exit codes. The commands, and what is known of the time, memory and
disk that they need, are in [../CHECKING.md](../CHECKING.md).

- `check.py`, `check.sh`, `lclib.py`, `Audit.lean.in`: the script, a shell wrapper that calls it,
  its parser for import lines, and the Lean program that it runs for the audit step
- `top-theorems.txt`: the theorems that the audit step looks up by name (the top of the file
  describes the forms of a line); `listing-for.txt`: those that the listing covers;
  `claimed-theorems.tsv`: the named theorems, each of which must be in the first
  list. No step checks that these lists are complete: a theorem that is on none of them is not
  looked up by name
- `IMPORTS.txt`, `long-lines.txt`, `guards.txt`, `front-statements.txt`, `scan-exceptions.txt`,
  `choice-allow.txt`: allowed imports between directories; the files that may have lines of more
  than 100 characters; the files that have `#guard` commands; the compiled statements of the
  theorems at the front; allowed exceptions to the word search and to two of the rules on the
  modules below `OnBytes.Main`; allowed exceptions to the audit's search for `Classical.choice` (a
  run prints their number as "allowed steps")
- `make_statements_html.py`, `check_statements_html.py`, `statements-html/`: the program that makes
  the two pages [../STATEMENTS.html](../STATEMENTS.html) (statements and definitions as HTML, in
  plain words beside the Lean text) and `STATEMENTS-ALL.html` (long: many more declarations, the
  comments beside the Lean text; it is not in this repository: that program makes it) from the Lean
  files, the program that checks the two against them, and the folder of texts that both read.
  `check.py` does not run them, and no step of it judges them or the pages. The calls, from `lean/`:
  [../CHECKING.md](../CHECKING.md), "The HTML pages". The top of the checking program lists its
  checks and says what they are worth, and what on the pages it does not check.
- `test_statements_notation_docstring.py`: a small test of one rule of the generator's scanner (16
  cases): from `lean/`, `python3 scripts/test_statements_notation_docstring.py`, exit 0 if all come
  out as due. It reads no file of the library but the generator and runs no Lean. `check.py` does
  not run it.
- `test_statements_empty_chip.py`: a small test of one rule of the front page: a status with no
  words for its chip gets no chip, and `make_statements_html.py` and `check_statements_html.py`
  write the same text (9 cases): from `lean/`, `python3 scripts/test_statements_empty_chip.py`, exit
  0 if all come out as due. `check.py` does not run it.
- `test_statements_front_switches.py`: a small test of two optional lines of
  `statements-html/front/labels.txt` (26 cases): `group-TOP | words` gives a group in the list of
  definitions a title of its own, and `contents-depth | sections` leaves the sub-sections out of
  the contents. It loads both programs and calls the code of each on the same made-up labels. From
  `lean/`, `python3 scripts/test_statements_front_switches.py`, exit 0 if all come out as due.
  `check.py` does not run it.
- `test_statements_scopes.py`: a small test of one rule of the scanner of `make_statements_html.py`:
  `namespace A.B.C` opens three scopes, and `end C` closes the innermost alone, as in Lean. It
  writes four small Lean texts into a temporary folder of its own, reads no file of the library but
  the generator, and runs no Lean. `check.py` does not run it.
- `check_stored_examples.py`: compares the two stored terms `storedPublicFiles` and `zGap` of
  `Ladder/Stored.lean` (three public files each) with six of the repository's example files, from
  outside Lean. It only reads, and runs no Lean. `check.py` does not run it, and no step of
  `check.py` judges it. The call, from `lean/`: [../CHECKING.md](../CHECKING.md), "The stored files
  and the examples". The comment at the top of the program lists its comparisons and says what a
  pass is worth.
- `RULES.txt`: what the help text of `check.py` omits: the build, the Lake files and what their pins
  do not give you, the scratch directory, and how the text rules of the steps `tree` and `words`
  work, each with what it does not catch; among them are the three rules on `verify-on-bytes`, the
  Lean text below `OnBytes.Main`: a hand translation of `cp_verify` into Lean, from which this
  repository builds no stand-alone program; one test (`tools/accepts/`) compiles it and has Lean
  load the compiled code while it evaluates files of `lean/Ask/`

## What each step shows, and what it does not

- **`tree`** reads file names and the files' text, above all the import lines. A pass shows: the
  Lean files are ordinary modules, without a `module` or `prelude` header, and contain only the
  characters that `RULES.txt` allows; no line has more than 100 characters, except in the files that
  `long-lines.txt` lists; every import of a library module resolves to one of them; there are no
  symbolic links among them; `.lake`, `.lake/packages`, `.lake/build` and the package directories
  are not symbolic links (the step looks no deeper into `.lake`); `lakefile.toml`,
  `lake-manifest.json` and `lean-toolchain` have the pinned SHA-256 (unless `--other-lake` was
  given: the last line then says so, `RULES.txt`, "Lake files"). It does not show: that anything
  compiles. Files named `*_wip.lean` (this repository has none), and Lean files whose path is not a
  module path, are left out of every step: the run prints `LEFT OUT` and how many. Lean files below
  `Ask/` are asking files: a reader runs each by the command that its own head gives. The text steps
  read them and the digest covers them, but they are not built, not replayed and not audited; no
  file of the library may import one; the run prints `ASKING FILES` and their paths (`RULES.txt`,
  "Asking files").
- **`words`** searches the source for words such as `sorry`, `axiom` and `opaque`: most of them
  twice, in the raw text and with comments and strings blanked, but `sorry`, `axiom` and `partial`
  only in the blanked text (`RULES.txt`, "Every word is searched twice"); and checks, as text, that
  every theorem in `claimed-theorems.tsv` has its file in the library and its line in
  `top-theorems.txt`, or says "no" with a reason, which is allowed only for a theorem that `NO_ROWS`
  in `check.py` lists (`RULES.txt`, "The named theorems"); and that the `#guard` commands, tests
  that Lean evaluates while it compiles a file, stand in files whose code is what `guards.txt` lists
  (`RULES.txt`, "The "#guard" commands"); and that `top-theorems.txt` has as many lines of each kind
  as `check.py` expects. It applies three stricter rules to `verify-on-bytes`, that is, to the
  modules below `OnBytes.Main` (`RULES.txt`, "The three rules on the program", which also says what
  "the program" means in its titles and in the script's messages; none of the three rules covers
  `lean-verify`, which has one row in `guards.txt`): in the files that the root `OnBytes/Main.lean`
  imports, no command programs Lean, but for one listed line, and no module of the rest of the
  library joins these files unlisted; the words of a passing outcome, what makes a passing ending
  and the passing exit codes stand only in the definitions that `check.py` names; and the files that
  hold the build-time guards on that text's compiled code, with the root itself and a few more, have
  the pinned lines and SHA-256 values.

  A pass shows: the usual ways of writing these constructs are absent. It does not show: that no
  macro or other compile-time code has the same effect: outside the files that `verify-on-bytes` or
  its guard file imports, macros and the like are not searched for; inside them only in their
  plainly written forms, and not at all in the guards' own files, whose SHA-256 is pinned instead.
  The verdict line on the guards says "that none of the … other modules which they import defines a
  new command": that says more than the rule, which is a search of these modules' text for six words
  (`RULES.txt`, "The program's guards", (d)). It does not show that the guards ran: that is the
  build's matter. The search has its own tokenizer, which differs from Lean's on unusual input
  (`RULES.txt`, "How comments are blanked").
- **`imports`** compares direct and indirect imports with `IMPORTS.txt`, which is read as a rule on
  what a file reaches through other files of the library, not only on what it imports. A pass shows:
  the intended layering between directories. Some files lie in a lower folder and import a higher
  one, among them `Hiop/Seeded/Game.lean`, `OnBytes/Dry/ChainLaw.lean`, `OnBytes/Dry/SpecView.lean`,
  `Rom/Handle/Adv.lean`, `ZKCP/OnRange.lean`; no file that a proposition of `Ladder.lean` unfolds to
  imports these; by import lines, two of them, `Hiop/Seeded/Game.lean` and `ZKCP/OnRange.lean`, lie
  beneath the final statement's file, and these two and `Rom/Handle/Adv.lean` beneath
  `VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean`; all five lie beneath
  `AtFullSide/Face/TheSixLines.lean`, the file of the six theorems. It does not show: anything about
  statements or proofs.
- **`build`** runs `lake build` on a fresh copy and names all three libraries of `lakefile.toml` in
  one call: the main library, `AtFullSide` and `ShapeLines`. (`ShapeLines` is no default target, and
  three of its files are reached by its own target alone.) With `--only`, the step includes the next
  two. It always hands Lake a bound on parallel work, which the heavy files of `ShapeLines/` need:
  your `LEAN_NUM_THREADS`, or else one process, and one more for each 12 GiB of available memory
  beyond 50, at most one for each core. That is a rule of thumb, which leaves little room, or none
  (`RULES.txt`, "The build", "The bound on parallel work"). The library's full check has been run
  over this repository's files, whole, and has passed ([../CHECK-RESULTS.md](../CHECK-RESULTS.md)).
  One Lean file, with one definition and four theorems, which nothing else imports, was added after
  the runs reported here and checked on its own ([../CHECK-RESULTS.md](../CHECK-RESULTS.md)). Three
  of the check script's pinned values were changed and three of its stored lists were extended for
  it; nothing else in the script or the lists changed. Over a copy of the Lean files that differs
  from this repository's, the audit was seen to fail under a limit of 48 GiB of address space, and
  23 modules under `leanchecker`, with "deep recursion detected" (`RULES.txt`, "The build").

  A pass shows: the three files that only the target `ShapeLines` reaches are in the copy; every
  Lean file of the library compiles from scratch, without errors, without a `sorry` warning and
  without a panic of Lean's; the guards on `verify-on-bytes` (`OnBytes/Guard/Program.lean`), which
  are commands that fail the build, found nothing to reject; the packages are used as they are in
  `.lake/packages` (whether they are what the manifest names is not checked: "Against whom"). It
  does not show: that there is no `sorry`, since a file can disable the warning (the audit step
  tests for that). A Lean file for which `lake build` leaves no compiled file fails the step; the
  run prints `Not compiled` with its name; replay and audit go on without it, or are not run if
  `lake build` ended with an error.
- **replay** runs `leanchecker` on every compiled module of the library, except a module that
  consists of import lines only and shares its name with a directory, and except the modules of the
  two libraries that `lakefile.toml` compiles at a larger thread stack, `AtFullSide/` and
  `ShapeLines/`. These 1,439 modules of two libraries (`AtFullSide/`: 915; `ShapeLines/`: 524) are
  replayed by Lean's own replay under a wider stack, not by `leanchecker`: the same function of
  Lean's, by another call, one process a module, at the stack of the module's library. What is shown
  of the need was seen over Lean files that differ from this repository's, with 901 modules in
  `AtFullSide/`: 22 of them stopped under `leanchecker` with "deep recursion detected", and so does
  `AtFullSide/Layout/TieRfl.lean` (seen on two machines); each of the 23 went through at the wider
  stack. For the other modules of these two libraries no such need is shown; the rule sends them to
  Lean's own replay all the same. Which modules go by the other call is pinned in `check.py`
  (`WIDE_SUMS`), and compared in the step `tree` and in the replay's verdict (`RULES.txt`, "One
  module is replayed by another call": why, and what that call does not do that `leanchecker` does).

  With Lean, a call of this form was made apart from the script on one module of `AtFullSide/`. A
  small program, not `check.py`, that makes this call with the same command line and the same four
  lines, but with eight threads for each process where `check.py` sets one, made it for all 1,438
  such modules of one built copy of the library: each went through. In the whole run over this
  repository's files `check.py`'s own step made it for all 1,438 such modules, and each went through
  (`lean/CHECKING.md`, "What you can do, and on what machine").

  A pass shows: Lean's kernel accepts every declaration in the compiled files, so none of them got
  there without passing the kernel. It does not show: anything about a bug in the kernel, since it
  is the same kernel; or that the other call ran the toolchain's own `LeanChecker`: a compiled file
  `LeanChecker.olean` that code running during the build laid on the search path would be what that
  call imports, unseen, for all of these modules. The packages are not replayed.
- **audit** loads the compiled modules in Lean, as data. A pass shows: every declaration depends
  only on `propext`, `Classical.choice` and `Quot.sound`; none is an axiom, `opaque`, `unsafe`,
  `partial`, `implemented_by` or `extern`, apart from the helpers that Lean generates for recursion;
  no module has a `csimp` entry or an initialiser; every theorem in `top-theorems.txt` exists, and
  its statement depends on a declaration of the library; for the theorems whose line names
  definitions to be searched, the values below these definitions reach no `Classical.choice` (proofs
  are not entered, nor the steps that `choice-allow.txt` allows); for the theorems whose line gives
  the form of the statement (`headline`), the compiled statement has that form. On a definition that
  a line marks `report` the step only reports, and on a theorem whose line says `general` it reports
  the axioms and the compiled statement and makes no further judgement: no verdict on binders or on
  `Classical.choice`, and no test that the hypotheses can be met together. Every line says
  `general`: no line names definitions to be searched or gives a statement's form.

  For the theorems at the front of the library (those that a document names and that lie in
  `VerifiableInference/`), and for further theorems (how many: the first lines of
  `front-statements.txt`), `check.py` then compares the compiled statement, as the audit printed it,
  with the text in `front-statements.txt`, to the letter (`RULES.txt`, "The front's compiled
  statements"). Some of these are theorems on the Lean verifier (which: the blocks of
  `front-statements.txt`, that of the soundness theorem on `verify` among them;
  [../CHECKING.md](../CHECKING.md), "What a pass shows, and what it does not"). The comparison can
  fail: it would if the compiled statement differed from the stored text. What has been run of it:
  `lean/CHECK-RESULTS.md`. The definitions that a statement names are not compared with anything. It
  does not show: that a statement means what you want, or has no hidden hypothesis. The audit prints
  a legend, whose lines begin `HOW TO READ THE LINES`.

## Panics

Left alone, Lean goes on after a panic of one of its functions with a default value, and can write
the compiled file and end with exit code 0. So build, replay and audit run with
`LEAN_ABORT_ON_PANIC=1`, under which Lean aborts at its first panic and the step fails. Each of the
three also fails if its output reports a panic (a line with the word `PANIC`, or the line before a
line `backtrace:`); that line tells you why. The search would not be enough by itself: on toy
projects one of seven panics was not shown at all. The replay does not stand in for this either: it
replayed a file whose compile had panicked and said nothing. Before the build the script runs a
control, a one-line file that panics: unless Lean stops at it, the verdict on the build fails; your
system may log one crash of `lean` for it. The script sets the limit on core files to 0.

## The listing

The audit step also writes a *listing*: for each listed theorem, the definitions that its statement
depends on, printed from the compiled files. A library can define notations and macros, so the
listing, not the source, shows what the kernel checked. The run prints the path of the file,
`statement-listing.txt`. The listing covers the theorems named in `listing-for.txt`, which are fewer
than the named theorems of `claimed-theorems.tsv`. The soundness theorem on `verify` is not among
them: of it, as of every theorem of `top-theorems.txt` that `listing-for.txt` does not name, the
listing has the statement and some counts only. If `listing-for.txt` is absent or names nothing, the
listing covers every theorem whose line does not say `general`, that is, none.

## How to run it

The script uses Lake on your machine and runs all the steps above: `python3 -B scripts/check.py`
(`lean/CHECKING.md`). With `--only tree,words,imports` it reads text only and starts no program. Run
`--only tree` before you let Lake fetch anything: `RULES.txt`, "Lake files".

The memory that the script asks for is a floor, not what a run needs. It asks for 21 GiB of
available memory before the build, before the replay and before the audit (7 before the audit with
`--jobs 1`). For the parallel work of the build it counts 50 GiB for the first process and 12 for
each further one. For the replay by the other call it counts 50 and 40, also where you have set
`LEAN_NUM_THREADS` higher (a lower number of yours holds), unless `--wide-jobs N` gives the number:
a process was seen to hold 39.4 GiB of its own, in samples taken 30 or 60 seconds apart, which can
miss a peak, with eight threads for each process and with one, which the script sets: the 40 GiB are
that figure rounded up. Both counts are rules of thumb and can ask for more memory than a machine
has, and so can a number given by `--wide-jobs`. Each process of the audit may reserve at most 96
GiB of address space. Seen over a copy of the Lean files that differs from this repository's (29,905
modules, 901 of them in `AtFullSide/`): in a whole run of the script the audit step failed under a
limit of 48 GiB, its process ending with "failed to read file"; the same audit file, run apart from
the script, went through under 96 GiB, with a peak of 53.0 GiB of address space at
`LEAN_NUM_THREADS=24` on 84 cores. The particulars: `RULES.txt`, "The build". What has been run, and
what is not measured: `lean/CHECKING.md`, "What you can do, and on what machine".


The script works on a copy of the library in a scratch directory, which it makes in the directory
that `CHECK_SCRATCH_DIR` names, by default in the system's temporary directory (on most systems
`/tmp`). Once it has opened that directory it holds it open and reaches it so, not by its path: from
then on another account cannot lead elsewhere what the script reads or writes in it. Lake and Lean
cannot be held in that way. So where another account could change the place or a directory above it,
a run that includes the step `build` refuses at its start and runs no step: name a place that only
you or root can change, such as a directory in your home directory, or, on a machine where you trust
every account, say so with `--i-trust-every-account-on-this-machine`. A run of the text steps alone
prints a note in that case and goes on if the named directory exists; if it does not exist, the run
does not make it, and stops. If you set `CHECK_SCRATCH_DIR`, name a directory that exists, or one
below directories that only you or root can write in. What is left open, above all with a directory
that has yet to be made in a place such as `/tmp`, is told in `RULES.txt`, "One copy".

## What the script does not run

It runs no mutation tests (listed changes to the source, after each of which a named file must fail
to compile). Such tests were run, but not on this library as it is here, and a reader cannot rerun
them: [../LIMITS.md](../LIMITS.md), "Tests that change the source", says what they show and what
they do not. The script runs no independent proof checker either: that would need an export of the
compiled library, for which this repository has no tool.

## Against whom

The script is meant to catch honest mistakes. It is not a defence against a repository that was
modified to deceive it:

- Code in the library runs while the library is compiled, as the same user and on the same machine
  as the script, so it could alter the script's files or output. Apart from the words of the word
  list (`initialize`, `register_option` and a few more), the audit's verdict on initialisers and
  `csimp` entries, and the rules on the files that `verify-on-bytes` or its guard file imports, no
  step rejects such code or searches for it; the audit step counts the rest in the compiled files,
  without a verdict. These rules catch the plain forms: the script does not stop an attacker who
  adds compile-time code to a file that `verify-on-bytes` imports. The script links no program, and
  runs none that is built from this library: of `verify-on-bytes` it checks the Lean modules.
- `check.py`, `lclib.py` and `Audit.lean.in` are stored in the repository that they check. The
  pinned checksums help only if you take these three files from a copy that you trust and point them
  at the library with `--root`, or compare their full sha256 with a record that you trust.
- `lean-toolchain` names Lean by a version tag, not by a digest, and no step checks which Lean
  actually ran.
- No step compares `.lake/packages` with the manifest. Mathlib's compiled files come from a public
  cache and are neither rebuilt nor replayed.

The particulars of the last three points are in `RULES.txt`, "What the pinned Lake files do not give
you".

## How the script was tested, and what passes by design

The script was tested against deliberately broken libraries. The tests are not independent of the
script: the same system devised both, and the script has not been independently reviewed. Several of
these broken libraries got past the script; each such case was fixed, which does not show that there
are no others. Most of the tests were not run on this script or on this library. That holds for the
three rules on `verify-on-bytes` too: most of their tests were made with the tables of a different
program. With the tables for `verify-on-bytes` they were tried by some eighty small changes, one at
a time, to a copy of the modules that the root and the guard file import, each followed by the step
`words`: text that programs Lean, below the root and outside it; a module more below the root; a
change to the pinned file of `Run/Blake2b/` and the loss of the listed line's entry; for each entry
of `ENDS`, what it searches in another definition; changes to the guard file, to a file that defines
its commands, to the file that defines `program` and to the root. Each came out as expected, with
`main` defined by `program` and not by `programFront`, by which the root in this repository defines
it (`OnBytes/Main.lean`); none was made with that root.

Five more changes were tried once each, on copies of a similar library, with the form of the script
that was made for that library: one more definition next to `main` in the root; one more import in
the root; `main_eq` in the guard file turned back to `program`; one byte changed in the file that
defines `programFront`; one byte changed in `OnBytes/Shell/FrontSame.lean`. Each made the step fail;
the last two only because the file's sha256 no longer matched. Such a sum shows that a file has
changed, not that it is right. The script's other steps (`tree`, `imports`, `build`) were not run on
them. No sum holds what `programFront` calls in `OnBytes/ChecksWithHashAsArgument/M/`, and none of
the five changes touched it. Nothing of this was tried with Lean: these rules read text.

The rules on long lines, on "#guard" commands, on the statements at the front of the library, and on
how many lines of `top-theorems.txt` have each kind were tested only on small made-up libraries and
listings. What was tried of the scratch directory is told in `RULES.txt`, "One copy", and what was
tried of the replay by the other call there under "The build" (against a small program in Lake's
place) and on `lean/CHECKING.md` (with Lean). Not all of the whole runs told under "One copy"
printed the account that they ran under, and that no other account was at work rests on one look at
all processes, in one container. A reader cannot rerun these tests.

These pass by design:

- a changed statement whose proof still compiles, of a theorem that has no block in
  `front-statements.txt` (no line of `top-theorems.txt` gives the form of a
  statement);
  of a theorem that has one, if the block and `STATEMENTS_SUM` in `check.py` are changed with the
  statement;
- a changed definition that a statement names, if the proofs still compile: the listing prints it,
  and nothing compares it;
- a change below `OnBytes.Shell.programFront` that keeps clear of the searched words: the three
  rules hold the root's one call, the file that defines `programFront`, the file that defines
  `program`, the guards' files and where a passing outcome is written, not what that text checks;
- no theorem gets a verdict on binders or on `Classical.choice`: every line says `general`;
- macros and elaborators outside the files that `verify-on-bytes` or its guard file imports, the one
  listed line inside them, the macros that define the guards' commands, and notations outside these
  files (inside them `RULES.txt`, "The program's source, (b) to (f)", (e), says which are rejected):
  the audit step counts them and does not assess them.
