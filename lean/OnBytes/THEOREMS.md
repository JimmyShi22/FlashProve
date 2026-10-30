# What is proved about verify-on-bytes

Terms: [TERMS.md](../TERMS.md); this folder's words: [GLOSSARY.md](GLOSSARY.md).

**Which verifier.** This page is about `verify-on-bytes`, the Lean text below `OnBytes.Main`: a hand
translation of `cp_verify` into Lean, from which this repository builds no stand-alone program; one
test (`tools/accepts/`) compiles it and has Lean load the compiled code while it evaluates files of
`lean/Ask/` ([README.md](README.md)). It is not about `verify`, the Lean verifier that is proved
sound in the random-oracle model, at exact match ([lean/THEOREM.md](../THEOREM.md)). Below, "the
program" is a stand-alone program built from that text; this repository builds none, and the calls
told here were made with builds of copies of the sources that differ from this repository's. Below,
`verify`, `verify -key` and `verify -leaf` are commands of `verify-on-bytes`; where the Lean
verifier `verify` is meant, "the Lean verifier" or "of THEOREM.md" stands beside the name. Where a
sentence denies something, the word is meant in its widest sense. This page is for readers who
intend to open the Lean source.

**What there is.** Theorems on the program's low-level routines and on its command-line logic;
theorems that start at the real calls and say which checks said yes; ties from a checking function
to the compiled verifier of one interactive oracle proof (IOP), at fixed parameter strings; and, for
the copy's file alone, bounds over a random oracle on two further checkers, with out-of-domain (OOD)
answers and with proof of work. The table has each with what it does not say.

**What there is not. No theorem bounds the chance that `verify-on-bytes` accepts a false file at its
own fixed hash function, at the default setting ([TERMS.md](../TERMS.md), table 1) or at any other.
No theorem on soundness reaches a call that checks a real proof.** So no theorem says what a yes of
`verify`, `verify -key` or `verify -leaf` is worth. The bounds for the copy's file alone are about
other checkers than this program's own, and no theorem carries them to a call on bytes. This program
is a different verifier from the library's compiled verifiers (terms of the library's Lean theory:
"compiled" there means made by the library's own compiler of protocols). No theorem ties it, without
unproved hypotheses, to the verifier of any soundness theorem of the library, and none ties it to
`cp_verify` ([LIMITS.md](LIMITS.md), point 1).

**For no configuration folder is the way from a command to a compiled verifier closed by theorems
alone.** The ties in `Tie/` end at the compiled verifier of one IOP,
`Compile.Batch.verifyOneProtocol` of `lean/Compile/Batch/Verifier.lean`, not at
`innerCompiledVerifier`, the compiled verifier, in which the Lean verifier `verify`
(`VerifierAndGoals.verify`) ends (`../GLOSSARY.md`, "tie" and "compiler"). The theorems speak of
that term; no run of the whole of it is known to us.

**"Is proved" means here: accepted by Lean's kernel.** How to check it:
[CHECKING.md](../CHECKING.md); what has been run of the checks: `lean/CHECK-RESULTS.md`. The words
of this page for a theorem rest on a reading of its file: what Lean checked is what these files
state. The library has a step that compares the compiled statements of some theorems with a printed
list (`lean/CHECKING.md`); that list holds none of the theorems of this folder that this page names.
What the labels "tested" and "read" mean, and on which programs the tests ran:
[LIMITS.md](LIMITS.md), "Which evidence".

**Which files.** The folder holds further files, whole subfolders among them (`Flat/`, `K/`,
`TypedOracleCompiler/` and others), which these pages do not describe, but for the section "The
copy's file alone" below. Each has a header comment on what it holds; not every one says what the
file does not claim. Where these pages speak of this folder's theorems, count them, or say what no
theorem or file of this folder does, they speak of the files that they describe.

**What holds of all of them.** All theorems concern the Lean source. None covers Lean's compiler and
runtime, the C compiler or the operating system, and none concerns hiding (`Params/Gate.lean` and
`Plan/RangesGate.lean` implement conditions on the public files; that is code, not a theorem; files
under `Dry/` and `Prover/` hold lemmas, and a prover, that the conditional theorem on index privacy
uses, and taken alone none of them is a statement on hiding). Most have the form "if the program
accepted, then ...", so they would hold vacuously if it never accepted. That it accepts honest files
is shown only by tests: at the fixed parameter strings below by build-time tests, and for `verify`
only by runs of the compiled program ([LIMITS.md](LIMITS.md), "Tests"). No build-time test has the
full verdict pass, and none evaluates the check of a key file or of a proof file.

**The OOD answers.** The code that reads them has no soundness
theorem here (the laws of
`Model/VerifyLawsRecord.lean` pin its rule, its flag and the ends of two stages, and claim nothing
on soundness). The theorems that start from a pass say which checks said yes: they speak of a
program that can return 0 where proximity terms rest on the theorem on
codes (Theorem 4.6 of the full version, ePrint 2025/2055, of the paper by Ben-Sasson, Carmon,
Haböck, Kopparty and Saraf published at STOC 2026), which the accounting takes as given: of the
paper's theorem we have verified no proof ourselves ([LIMITS.md](LIMITS.md), point 4). The Lean
library proves the statement that stands in that theorem's place, from files that AI systems adapted
from ArkLib and Mathlib; that this statement follows from the cited theorem rests on reading alone,
not machine-checked, and no theorem ties this program's numbers to it ("The copy's file alone",
below). Whether the program accepts honest files can be seen only from
runs of the compiled program ([LIMITS.md](LIMITS.md), point 11 and "Tests").

**The small test configuration** belongs to the C++ library's test protocols; it is not one of the
small examples in [LIMITS.md](LIMITS.md). It is spelled out in this folder's files. The C++ test
tool in this repository writes two lines of its parameter file differently (by reading of the tool's
source, not machine-checked: the message length of a mask row); the tests, constants and theorems in
this folder are tied to the files as this folder holds them.

**What a build checks.** A build of the program alone checks no theorem that this page lists: all
are in files that the program does not import: the whole of `Tie/`, `Slice/` and `Guard/`, and the
files of theorems in `Chain/`, `Field/`, `Hash/`, `Model/`, `Params/` and `Shell/` (from the import
lines). The same holds of `Iop/TensorLaws.lean` and `Model/HideLaws.lean`. In this repository's Lake
file the library's default target includes this folder, so `lake build` compiles every module of it
and checks all theorems. The library's check script (`lean/scripts/check.py`) asks Lean for the
axioms of every declaration; that is no part of `lake build` ([CHECKING.md](../CHECKING.md)).

Paths on this page are relative to `lean/OnBytes/`, except `Fmt/` and `VerifiableInference/`, which
are the library's (`lean/Fmt/`, `lean/VerifiableInference/`), and paths that begin with `lean/` or
`prover/`, which go from the repository's root. `Hash/` and `Iop/` here are this folder's, not the
library's directories of the same names. "The compiled verifier of one IOP" in the table is a term
of the library's Lean theory, made by the library's own compiler of protocols.

| theorems | what they say | what they do not say |
|---|---|---|
| `readChain_eq` and the field operations (`Field/`, `Chain/`); `hashH_eq`, `queryH_eq` (`Hash/`) | **Low-level routines only.** The fast field arithmetic and byte reader equal the library's plain definitions in `Fmt/`. The format's hash and a chain's hash calls are the library's own fast versions, which the library proves equal to its plain ones | The equality for the hash says little, and the second hash function (a second, fixed hash function, built on BLAKE2b's compression function) has no theorem (header comment of `Hash/HEq.lean`). By the library's own comments, no theorem ties its BLAKE2b with a non-zero salt or personalization to the plain definition of BLAKE2b; only known answers support it there, and that is how the format's hash passes its 32-byte start. Not covered: exponentiation in the extension field, `Field/Mle.lean`, four functions in `Iop/Tensor.lean`. Nothing about the code that tests the protocol's equations, or about how schedules and parameter bytes are derived |
| `program_yes`; `program_said`, `program_within` (`Shell/`) | **Command-line logic only** (stated of `Shell.program`; `main` is one call of `Shell.programFront`, the same checks with the format's hash as an argument, by `main_eq` in `Guard/Program.lean`; that `main` equals `Shell.program` is a theorem, `main_eq` in `Shell/AtMain.lean`). If `main` returns 0, or prints `YES` or a line that begins with `W`, the command was a full `verify` call and its verdict on the call's options and on what its eight file reads returned is a pass | Whether the verdict is right. That a pass needs `-id` or 128 bits: that lies in the verdict. What a shell sees: the theorems speak of the number that `main` returns, and a shell sees it modulo 256 (`LIMITS.md`, point 1). Anything about what the file and output calls do: that a read returns the file's content, or bytes at all, or that a printed line reaches anyone (header comments of `Shell/AtBottom.lean` and `Shell/AtOps.lean`) |
| `said_result`, `said_part`, `said_test`, `call_says`, `call_reads`, `call_cut`, `program_sizes`, `readIO_short` | **Command-line logic only, with arbitrary checks plugged in (`program_sizes`: with the program's own).** Each other passing line (`result-v1 status=0`, `PART PASSED`, `TEST FILES PASSED`) comes only from a check that gave that result. Every line printed on standard output has one of a fixed set of forms. Every read asks for one byte more than one of the three limits on length. A run in which a read came back full passes nothing: it prints only `NO: file-too-long`. So if `main` prints a line that does not begin with `N`, every read returned fewer bytes than it asked for (`program_sizes`) | That a printed string is a single line, and that a run reads only the paths of its command, in order, once each, is not proved in this library. From those lines the only theorem about `main` is `program_sizes`, on how many bytes the reads returned; which check passed is proved in two ways: starting from a printed line, for the command-line logic alone (`Shell/AtTie.lean` lists which commands each theorem covers); starting from an exit code, for `main` itself: 3 for `verify -key` and `verify -leaf`, 0 for `verify` (`main_key`, `main_leaf`, `main_zero`, below). These concern what a read asks for and how many bytes came back, not whether those are the file's bytes or unchanged. That the bytes are the whole file no theorem says; `readIO_short` says only that the real operation's last read came back empty (header comment of `Shell/AtSize.lean`) |
| `product_tiny`, `product_full`, `links_tiny`, `links_full` (`Tie/ToysClosed.lean`) | **Four fixed parameter strings.** A tie (`../GLOSSARY.md`, "tie"), starting from the checking function instead of a command, with the structural conditions proved instead of assumed | No theorem says that a command derives any of the four, so these do not join up with the row above. Tests confirm it. That the four strings are what the C++ programs wrote is stated only in comments. With `product_tiny` and `links_tiny`, the program's own commands reject the files unless `-bits` is lowered. No copy's file of the protocol, small or at full size, has been examined: the four strings are the test protocols' |
| `key_check_oneTime` (`Tie/KeyFile.lean`) | **The function `Key.check`; the first of a key file's three chains.** If `Key.check` accepts a key file, the program has read the file's one-time chain under its own description. If that description meets the structural conditions and the file has at most 2^32 - 160 bytes, the compiled verifier of the one IOP that is made from that description and the program's own decision on that chain (`oneTimeDec`) accepts what was read of that chain | It would also be true if `Key.check` never accepted: no build-time test has `Key.check`, or a command that calls it, accept a file, so an accepted key file and a description that meets the structural conditions are shown together by no theorem and no shipped test. A theorem that leads here from `verify -key` or from a full call's exit code 0 is not in this library. The structural conditions and the bound on the file's size stay hypotheses: shipped tests find the conditions met at the test key's parameters, with made-up data, and at the values of two small examples' parameter files, which are not those in this repository. The one-time chain sends trees that it never opens (two of five at the test key; two of six and two of eight at these two examples' values). Of such a tree that compiled verifier knows the 32 bytes of its root and nothing of what was committed under it; that a later chain opens it is outside the theorem. So this does not say that it checks the key's table: nothing under the table's root is read in this chain. Nothing about the file's other two chains. It ties a function of the program to the compiled verifier of one IOP, and no theorem says what that verifier's yes is worth at such a chain |
| `main_zero` (`Shell/AtWhole.lean`), `main_zero_id` (`Shell/AtWholeId.lean`), `main_zero_same` (`Tie/ZeroNamed.lean`), `main_zero_named` (`Tie/ZeroNamed.lean`); `main_key`, `main_leaf` (`Shell/AtPart.lean`) | **From the real calls: which checks said yes.** If `main` returns 0, then in Lean's model of input and output the program's key, entry and proof checks each said yes on the bytes it read, and the ID behind `-id` among the call's options is the commitment ID it computed from the checked key table; and the parameters of the seven chains, as the program made them from the three configuration files it read and read them back, and under which its key, entry and proof checks said yes, all hold the digest of these three files (the digest that enters the commitment ID), and the five of them that hold a shape of the tables hold the same one. A passing `verify -leaf` or `verify -key` call means, in the same model, that the named check said yes on the bytes read | Not that the proof is correct or the reply the model's. Nothing "checked at 128 bits": the `bits = 128` in `main_zero_id` is the field of the options as read, 128 also if the call names no bits, and `main_zero` has no clause on bits. That the ID binds the proof, the request or the reply: they do not enter it; nothing is proved about the hash, or that equal hexadecimal digits mean equal bytes. Whether the last line was `YES` or `WITHIN LIMITS`. That the entry's number is the number in the proof file's head; that the pair of `-id` and the ID stands among the options only once (by the code, the reader of the options refuses a second `-id`; no theorem). What `planned` tests; the accounting; the policy; which positions are covered; the standard conditions. That the key, entry or proof file is bound to that digest or shape, or that the three files belong to one configuration or one commitment: the clause says what the program derives from the configuration files ("What ties one file to another", below the table); for `verify -leaf` and `verify -key` not even that is stated, the option `-id` is free, and no statement names the commitment ID. A part that passed is a committer's self-test, not a verification; `verify -leaf` takes the key's table on its form alone and does not check the key; the exit code 3 is also that of a test call that passed. The converse; that some files make a call pass. The bytes are the answers of the program's reads in that model, not a file's content. What a shell sees (`LIMITS.md`, point 1) |
| `planned_entryBytes` (`Model/VerifyDerives.lean`) | **Where an entry chain's parameter bytes come from.** The program derives the entry chain's parameter bytes from the three configuration files alone. What is proved is which function gives them: the entry chain's parameter bytes in what `planned` returns are those that `entryParams` gives on what `readLines` reads from the parameter file (by its description, the first 32 lines) and on the digest of the three files | Not that a shipped example's folder yields the bytes that the Lean source stores for it. That the deriving function is the format's or the C++ programs' derivation: it is this folder's own code, and tests alone compare its bytes with theirs, at stored lines and digests. The converse. The other six chains |

**Where the rest is.** For `Tie/`, see the header comments of `Tie/OneChain.lean`,
`Tie/ToysClosed.lean` and `Tie/KeyFile.lean`. Further files of theorems have no
row here, and this page claims nothing from them, among them: `Params/ConfigureLaws.lean`,
`Params/ReadBackLaws.lean`, `Params/IndexLaws.lean`, `Model/VerifyLaws.lean`,
`Model/VerifyLawsWhole.lean`, `Model/VerifyLawsId.lean`, `Model/VerifyLawsOption.lean`,
`Model/VerifyLawsRecord.lean`, `Model/VerifyDigest.lean`, `Model/VerifyShape.lean`,
`Shell/AtOptions.lean`, `Shell/AtOption.lean`, `Tie/LeafCall.lean`, `Tie/KeyRounds.lean` and
`Slice/ChainErrAny.lean`.

**Do not combine these with the library's `lb_sound` and `lu_sound`.** The protocol behind the
compiled verifier of one IOP consists of the chain's schedule and this program's decision function.
Its statement and its index are the one-element type, and its encoding, decoder and honest parties
are trivial ones, which mean nothing. The library proves such protocols "sound" only for the
relation that holds of everything, with error 0, and with a decoder that accepts every string; its
own comments call that true and empty. A sentence that joins those theorems to the ones above would
have a theorem behind every word and mean nothing. The same goes for the library's `lts_sound` and
its theorems named `met...`. For `product` and `links` a meaningful result would need knowledge
soundness for a named relation, which has not been proved; and no theorem in `Tie/` identifies this
compiled verifier with `innerCompiledVerifier`.

**What ties one file to another.** The functions `Key.check`, `Entry.check` and `Proof.check` each
check one file, with parameters and a table that the caller hands in, and so do the theorems about
them: those on fixed parameter strings in `Tie/` (there the parameter bytes are a constant of the
theorem and the table is arbitrary), and `key_check_oneTime` (for any parameters). For a full call
that returns 0, `main_zero` says that all three ran under the chains of one value that `planned`
returned on the three configuration files as read, that the entry was checked against the table that
the key's check returned, and the proof against the table that the entry's check returned.

By `main_zero_same` (`Tie/ZeroNamed.lean`), if `main` returns 0, then in Lean's model of input and
output the parameters of the seven chains, as the program made them from the three configuration
files it read and read them back, and under which its key, entry and proof checks said yes, all hold
the digest of these three files (the digest that enters the commitment ID), and the five of them
that hold a shape of the tables hold the same one. This says what the program derives from the
configuration files; it does not say that the key, entry or proof file is bound to that digest or
shape. A shape here is six numbers, equal after they are read back; that it is the shape that the
planner made is not stated (a number from 2^64 on is spelled modulo 2^64), and it does not cover how
the matrix lies in a table. The key's and the proof's second chains hold no shape (read off the
definition; no theorem); their digest is covered.

The tie is to a root and a shape only: a table is a root and OOD answers, and nothing is said on
what lies under a root. Nor is it stated that the plans which the checks follow are the plans whose
errors the stages account for, or that the entry's number is the number in the proof file's head. So
the three files are not thereby proved to belong to one configuration or one commitment. By
`main_leaf`, `verify -leaf` checks the entry against a table that was read from the key file in the
same run, on its form alone. See [LIMITS.md](LIMITS.md), point 23.

**From one link of a proof to the next.** The soundness of the step that hands a committed matrix on
from one sub-proof to the next is stated by no theorem in this folder, not even for the test
protocols ([LIMITS.md](LIMITS.md), "From one
sub-proof to the next").

**`Shell/` does not combine into a statement on soundness either.** `program_yes` is about `verify`.
Among the files that this page describes no tie to the compiled verifier of one IOP starts from its
exit code 0 (for the copy's file alone, see the section below). And the verdict of `verify` depends
on six other chains as well.

**The soundness theorem on `verify`** (THEOREM.md) is about the verifier written in Lean. No theorem
connects it, without unproved hypotheses, to this program, and none to `cp_verify`. This program
follows `cp_verify`'s source text, so the two programs are not independent: where they agree, that
is not independent evidence ([LIMITS.md](LIMITS.md), point 3).

## The copy's file alone: a pair of statements and a closed check

These stand in files under `K/`, `TypedOracleCompiler/` and `ShellOf/`. The pair speaks of the
copy's file alone, at the small example's and the full size's parameters; a build-time test, decided
by Lean's kernel, holds copies of the first 32 lines of the stored examples' parameter files against
these (`full_says`, `small_says`, `K/Left/TestSaysLines.lean`). The second statement of the pair
below is a bound over a random oracle on a checker of files, with OOD answers and with proof of
work.

**One second checker of files, which reads them through the oracle** (`entry_armO_small`,
`entry_armO_full`, `K/Oracle/ArmOAt.lean`). Lean proves two statements about one second checker
defined in Lean; there is one hypothesis, a theorem on Reed-Solomon codes. The library proves the
statement that stands in that theorem's place elsewhere (`Cb.Gl.bchks46At`,
`lean/Cb/Bridge/GlCodesProved.lean`; that the statement follows from the cited theorem rests on
readings, and no theorem says it) from files adapted from ArkLib and Mathlib (what was taken over,
and how it was adapted: `lean/ThirdParty/README.md`). AI systems alone adapted and built those
files; what Lean checks of them, and what it does not: [lean/LIMITS.md](../LIMITS.md), L15.

What has been run of the checks: `lean/CHECK-RESULTS.md`. Both statements keep the hypothesis in
their text; the fields are the same by abbreviation (`Slice/Draws.lean`); one file lays it into the
second statement of the pair: `lean/OnBytes/K/Oracle/VerdictOnFiles.lean` applies `soundO_full` and
`soundO_small`, which are that statement (the field `sound` of `entry_armO_full` and
`entry_armO_small`), at the proved statement, for a bound on the closed check on the files
(`verifyEntryFilesFull_copyBound_64`, `verifyEntryFilesSmall_copyBound_64`); no theorem lays it into
the other three: the first statement of this pair, and the two statements of a second pair of the
same shape, `entry_arm_small` and `entry_arm_full` (`K/Left/ArmAt.lean`, whose head tells its
limits), which has no paragraph on this page (by a search of the text of the files under
`lean/OnBytes/` and `lean/Johnson/`, which did not cover the files beneath the theorem of
THEOREM.md: of the files that it covered, `lean/OnBytes/K/Oracle/VerdictOnFiles.lean`,
`lean/Johnson/Flat/TwoSizesCodes.lean` and the closed check's
`lean/OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean` name the proved theorem outside
comments, and neither of the last two names one of these statements; the last of them applies at the
proved statement the bound from which the second pair's second statement follows (`full_one_world`,
`small_one_world`), for the closed check's bound below, and not that statement itself).

Further files name the proved theorem outside comments, among them
`lean/Johnson/Goal/Conditions/EntryAtDescV.lean`, which lays it into the row of the copy's file
beneath the theorem of THEOREM.md (`FlashProve.entrySound`).

The checker reads the copy's file by the reader that takes the hash as an argument
(`TwoPort.M.Entry.read`), with the oracle asked in the hash's place, and then runs a verifier made
by another form of the library's compiler; the reader and that verifier put their hash questions to
one oracle, all but one: the digest of the three public files is handed in as the oracle's own
value. That reader is the text that `main` itself runs, there at the program's own hash. At that
hash Lean proves it equal, on every file, to the reader without the argument, of which the theorems
on this program are stated (`twin_at_port`, `K/Oracle/ReaderAt.lean`). Between the reader and that
verifier stands a hand-written step for the seeds. The checker is not `innerCompiledVerifier`, the
compiled verifier (the theorem on `innerCompiledVerifier`, `innerCompiledVerifier_sound`, holds
under 16 named hypotheses, of which four are left in general at the two IOPs of
`lean/Johnson/Flat/TwoSizes.lean`), and not this program's own check: it shares that reader with the
program, and nothing behind it.

The first statement: whenever this program ends with exit code 0 on a call whose parameter file has
that setting's lines, this checker, with the real hash as its oracle, accepts the same key file and
copy's file, with the program's own two tables and the user's commitment ID (of the key file it only
parses the table; without the key file's part nothing follows from that of the copy's file). No call
is shown in Lean to end with exit code 0. Exit code 0 is given for `YES` and for `WITHIN LIMITS`
alike.

The second statement: for public files fixed beforehand, and with an ideal random hash as the
oracle, whoever puts at most 2^64 questions to it gets this same checker to accept a copy that does
not match a well-formed first table with probability at most 2^-61: about 5 · t, for t questions,
times a ceiling of 2^-128 on every round's error, plus collision terms; at the rounds that have
proof of work (6 of 41, which the plan labels LINK, CS, four times, and BASE; 4 of 24 at the small
example; no theorem of this library states these counts) that ceiling counts 32 bits of work at one
question a try, an allowance in how the library counts a round's error and in header comments,
stated in no theorem (without it the worst of those rounds stands near 2^-96). The figure is a
ceiling of this one bound and no security level of any program.

"Copy" and "first table" are what is read off the maker's questions under the two roots, not a
file's bytes; a first table is well-formed if it decodes with its OOD sample and the OOD sample
singles one table out; a copy matches it if the copy, too, decodes with its own OOD sample, which
singles one table out, and the two decoded tables agree before the pads. The commitment ID stands in
the first statement alone: that an ID binds a table is in neither.

Between the two statements lies the usual gap of the random-oracle model: no theorem carries the
probability from the ideal hash to the real one, so Lean states no probability of the program's own
yes; and that this checker accepts honestly made files under an ideal hash is not proved: Lean
proves that its reader and its verifier use one parameter digest under every oracle, and a search by
program through its definitions finds nothing of the real hash inside it, which is evidence, not a
theorem (the search cannot see data, such as that digest, nor a second writing of the hash); that a
string with an OOD sample that is well-formed in this sense exists, and that, of two honestly
encoded tables that differ in an entry before the pads, the second does not match the first, is a
theorem (`K/Oracle/Decodes.lean`, `K/Oracle/DecodesAt.lean`); that the checker accepts any files is
not. There each table goes with its own OOD sample; "differ" is read in the field; "before the pads"
means an index below l − 3 s, and that the format's pads begin there is not asked; and "honestly
encoded" means Lean's table made with the format's symbol function, which no Lean file compares with
what the programs write. These are strings and OOD samples written down in Lean, at any seed: no
theorem says that one of them is read off any maker's questions under a root, or that its OOD sample
is the one in a value that the checker returns.

**A closed check of the parsed value of the copy's file, with the hash function as an argument, and
a bound about it** (`verifyEntryFull`, `verifyEntrySmall`, `runEntryFull`, `runEntrySmall`,
`lean/OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean`; `verifyEntryFull_copyBound`,
`verifyEntrySmall_copyBound`, `lean/OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean`). At
both sizes. It is a further check, beside the one above; this program does not call it, and it is no
part of the verifier of any soundness theorem: its numbers bound nothing there.

*The check.* It takes the three public files, a parsed value and a hash function g, and no other
letter is left. The parsed value is plain data that a parser is to read off the key file and the
copy's file: two roots, both tables' answers, the seeds and the chain's strings. The check does not
parse the public files' text: it asks g at the string made of them and uses that answer alone; the
description, the sizes, the radii and the decision are typed into Lean, and no part of the check
compares them with the parameter file's lines. It is not the compiler's output by its text. It is
written by hand: tests on the parsed value, a test of pins, the typing of the chain, a comparison of
seeds, and a form of the lax verifier of the link out of another form of the library's compiler.
What ties it to that compiler's output is a theorem on its yes (`verifyEntryG_iff`,
`lean/OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean`): at every function it says yes, the
tests on the parsed value apart, exactly if the pins fit and the checker of the entry's part, handed
the parsed value, returns a value. A form with code (`runEntryFull`, `runEntrySmall`) is proved
equal to it, on all arguments, at the functions made of a hash on bytes, and at these alone
(`runEntryFull_eq`, `runEntrySmall_eq`). No run of either form is told on this page.

A shell around the form with code is written in Lean (`entryMain`, `ShellOf/EntryProg.lean`; no
executable is built of it): it takes a size, a commitment ID, the folder with the three public
files, a key file and a copy's file; it tests that the parameter file's first 32 lines are that
size's setting's and that the three files are short enough for one call of the hash; this program's
own reader of a copy's file makes the parsed value, and is trusted for nothing; then the form with
code runs at the format's hash, and the commitment ID that this hash gives of the three files and
the value's first table is compared with the caller's. That this is the ID which the format
publishes is no law (the head of `ShellOf/EntryProg.lean`). Lean proves that exit code 0 of that
term says that both tests passed, that the reader returned the value, that the closed check says yes
on it and that the two IDs are equal, and that the lines of a yes were written (`entryMain_zero`,
`ShellOf/EntryProgLaws.lean`): in Lean's model of input and output, at that one fixed function, and
in one direction only: from exit code 0 to these facts. By the check itself the commitment ID is not
looked at. That honest files' parsed values pass the tests is not shown in Lean.

*The bound.* For all three public files that are fixed before the function is drawn, and for every
maker that puts at most t questions to a function drawn at random and then puts out a parsed value
(a prover with its parser as its last step, their questions counted together): the check says yes,
while the entry's language fails of the two strings that are read off the maker's list of questions
under the value's two roots, with a probability of at most 2^-85 for t up to 2^40, 2^-61 up to 2^64
and 2^-45 up to 2^80 (`verifyEntryFull_copyBound_40`, `_64`, `_80`, and the like at the small
example). No hypothesis stands in these statements: the statement that stands in the place of the
theorem on codes is put in, so they rest on `lean/Cb/Bridge/` over `lean/ThirdParty/`, with what is
told above of the adapted files. The assumption that every proof in the random-oracle model leaves
open stays: no theorem carries the probability from the random function to the format's hash.

*What it is worth, and what not.* What is bounded is not a yes on a false statement. "The language
fails" means: the first string decodes with its OOD sample, which singles one table out, and yet the
second does not decode with its own OOD sample to a table that agrees with the first's before the
pads, or its OOD sample does not single one out. Where the first string does not decode, or its OOD
sample singles none out, nothing is said: so without the key file's part nothing follows, and under
a root of which the list holds nothing the reading is a table of zeros. One maker makes the whole
value: nothing is said of a committer who is bound before a prover moves, and this promise does not
chain with the key file's and the proof file's parts. Public files that are picked after asking the
function are not covered. The numbers are ceilings of the written bound and no security level of any
program: at the rounds that have proof of work (6 of the 41; 4 of 24 at the small example) they
count 32 of the 128 bits as proof of work, at one question a try; without that allowance, by
arithmetic outside Lean (the head of `lean/OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean`),
the bound would read about 2^-53, 2^-29 and 2^-13. That the check says yes on anything is not shown
in Lean: if it never did, the event would be empty. That the language can fail at all at these sizes
is a theorem (`guard_full`, `guard_small`, `K/Oracle/Decodes.lean`). The events are not shown
measurable, and the probability is a lower integral. One file of three; nothing on tokens.

*Two tests.* These are tests on the public files that some theorems take as a premise and that this
program does not run: `Flat.sizesRefB` and `scalesRefB`, each at the example's public files as they
are typed into Lean (`zStoredFull`, `lean/Johnson/Top/Own/OwnStoredFull.lean`): closed terms of type
Bool. They are hypotheses wherever they are used: by the head of
`lean/Johnson/Top/Own/OwnStoredFullRun.lean` a test that passes there "stays a hypothesis wherever
it is used". The two are evaluated by Lean's evaluator whenever the library is built
(`lean/Johnson/Top/Own/OwnStoredFullRun.lean`); the kernel has checked neither.
