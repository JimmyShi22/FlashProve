# Limits of verify-on-bytes

Terms: [TERMS.md](../TERMS.md); this folder's words: [GLOSSARY.md](GLOSSARY.md).

**Which verifier.** This page is about `verify-on-bytes`, the Lean text below `OnBytes.Main`: a hand
translation of `cp_verify` into Lean, from which this repository builds no stand-alone program; one
test (`tools/accepts/`) compiles it and has Lean load the compiled code while it evaluates files of
`lean/Ask/` ([README.md](README.md)). It is not about `verify`, the Lean verifier that is proved
sound in the random-oracle model, at exact match ([lean/THEOREM.md](../THEOREM.md)); the limits of
that theorem and of the library are on [lean/LIMITS.md](../LIMITS.md). Below, "the program" is a
stand-alone program built from that text; this repository builds none, and the calls told here were
made with builds of copies of the sources that differ from this repository's. Below, `verify`,
`verify -key` and `verify -leaf` are commands of `verify-on-bytes`; where the Lean verifier `verify`
is meant, "the Lean verifier" or "of THEOREM.md" stands beside the name. Where a sentence denies
something (no theorem on soundness, nothing on hiding), the word is meant in its widest sense. This
page uses the programs' words. In TERMS.md's terms the key file is a part of the proof, the copy's
file (in Lean names and in the program's commands: entry; outside lean/: leaf file) a further
encoding of the index, the commitment ID the index verification key, a request an instance, the
weights the index, and hiding index privacy; the default setting is defined there, in table 1.

**Which files.** This page describes the files that the program imports and the theorems that
[THEOREMS.md](THEOREMS.md) lists. The folder holds further files, whole subfolders among them
(`Flat/`, `K/`, `TypedOracleCompiler/` and others), which these pages do not describe, but for the
section "The copy's file alone" of THEOREMS.md. Where this page speaks of this folder's theorems,
counts them, or says what no theorem or file of this folder does, it speaks of the files that it
describes. In the comments of this folder's Lean files, a path or a name that bears the mark "[not
in this library]" names a file or a declaration that is not in this repository: wherever a comment
says that such a file or declaration proves, shows, derives, holds or tests something, read it as
not proved (not tested) in this library.

**Which evidence.** Where evidence applies, a point is labeled with it: **tested** (a program was
run; build-time tests run whenever these sources are built), **read** (by reading of the source, not
machine-checked: nothing was run, and the reading has not been independently reviewed) or
**untested**.

**Which programs were run.** Build-time tests apart, no call told on this page was made on a build
of this repository's sources: the runs were made on builds that differ from this repository's in
what they hash and admit, and most of them in further code ("Tests", its first item). Their records
are not in this repository.

What has been run of the checks of the Lean proofs: `lean/CHECK-RESULTS.md`. The list holds the
limits of this program that are known; it may not be complete.

## What a passing result is worth

1. **`verify-on-bytes` follows the default setting as a program (point 11): no theorem bounds the
   chance that it accepts a false file at its own fixed hash function, at this or any other setting.
   No soundness theorem covers this program's answer on a key file, a copy's file or a proof file,
   and no security level is claimed for it.** No soundness theorem covers `cp_verify`'s answer
   either, and no security level is claimed for it. See [THEOREMS.md](THEOREMS.md). The theorems
   there on exit codes speak of the number that `main` returns. An operating system's shell sees
   that number modulo 256. By the two tables in the source, every exit code of this program is one
   of 0, 1, 2, 3, 4, 5, 14, 15 (read). Two theorems say that the number which `main` returns is
   below 256 (`status_small`, `main_small`, `Shell/AtMain.lean`); they speak of Lean's model of
   input and output, not of the operating system. That `innerCompiledVerifier`, the compiled
   verifier, in which the Lean verifier `verify` ends, agrees with the programs (for example, at the
   OOD sample's code in a chain's first query) is not proved: no theorem ties the released programs
   (the C++ verifier and committer and the CUDA prover) to the protocol that `verify` checks
   ([lean/THEOREM.md](../THEOREM.md)). The theorem on `innerCompiledVerifier`
   (`innerCompiledVerifier_sound`) holds under 16 named hypotheses, of which four are left in
   general at the two interactive oracle proofs (IOPs) of `lean/Johnson/Flat/TwoSizes.lean`; on what
   it rests, and that Lean gives no number for its bound: [lean/LIMITS.md](../LIMITS.md), V2, V3, V8
   and V9. For the copy's file alone the library proves further statements, each about a check of
   its own; no probability is stated of this program's own yes ([THEOREMS.md](THEOREMS.md), "The
   copy's file alone"). Exit code 0 covers `YES` and `WITHIN LIMITS`. Nothing here is about
   `cp_verify` or about compiled code.
2. **A passing result says nothing about hiding.** No verifier can test how the provider created the
   commitment or generated its randomness, so no result from either program says anything about
   hiding. The theorems that THEOREMS.md lists say nothing about hiding either. Files under
   `lean/OnBytes/Dry/` and `lean/OnBytes/Prover/` hold lemmas, and a prover, that the conditional
   theorem on index privacy uses (which theorem that is, and what it says:
   [lean/LIMITS.md](../LIMITS.md), L64). Taken alone none of them is a statement on hiding.
3. **The two verifiers are not independent.** This program follows `cp_verify`'s source text: where
   the two agree, that is not independent evidence, and neither program will reveal a design flaw or
   a copied mistake.
4. **The printed bits are an accounting, not a security level** (read). Each round must meet the
   target by itself. The overall error is larger, because a proof has thousands of rounds and an
   attacker can try many times; nothing here computes it from the printed figures. No theorem says
   that the accounting's integer bounds are correct: the accounting is a calculation, not a theorem.
   The printed bits rest on the accounting alone. It rests on these, none of which this folder
   proves, among others:
   - a lemma ("the proved lemma"; `../GLOSSARY.md`; the main library proves a statement of its own
     of that kind (mutual correlated agreement within a third of a code's distance, for any code
     that is linear as the protocol reads it), `Cb.ld_mca_third`, which this folder applies at its
     own rendering of the format's codes; as far as we know, it has not been compared with the
     paper's lemma clause by clause, and nothing ties it to the C++ programs' count), for proximity
     terms within a third of the distance: none at the default setting; no theorem ties the
     planner's number to it;
   - that w bits of work divide a round's error by 2^w for these hash chains;
   - the theorem on codes (Theorem 4.6 of the full version, ePrint 2025/2055, of the paper by
     Ben-Sasson, Carmon, Haböck, Kopparty and Saraf published at STOC 2026), which the accounting
     takes as given: of the paper's theorem we have verified no proof ourselves (it is not in the
     proceedings; the full version gives an outline of its proof; `docs/limits.md` has the footing
     whole; that our parameters meet the theorem's conditions is our own reckoning, with no bits to
     spare; the Lean library proves the statement that stands in that theorem's place, from files
     that AI systems adapted from ArkLib and Mathlib; that this statement follows from the cited
     theorem rests on reading alone, not machine-checked, and no theorem ties this program's numbers
     to it: `THEOREMS.md`, "The copy's file alone"), for every proximity term, a request's, a
     batch's and the committer's (by the eight group lines of `policy.txt` of `target_full_f2`,
     `target_small_f2`, `target_small_f2_gap` and `target_small_f2_roomy`); and in the small test
     configuration of `THEOREMS.md`;
   - that combining the rows of an interleaved word costs no more than a line through two words,
     however many rows there are (`rowcost 1`). It is argued on paper, in a technical report on this
     protocol that is not public and is not in this repository, after a statement in the abstract of
     a preprint, at the theorem's M = 1 (`docs/limits.md`, its entry on the theorem on codes); that
     argument is not machine-checked and has not been independently reviewed. Nothing in this folder
     checks it or ties the programs' `rowcost 1` to it, and no theorem of this folder covers it. The
     only other support is a comment in the C++ source. At the default setting it affects the
     proximity terms of a proof and the committer's (`docs/limits.md`);
   - that some numbers supplied by other parts of the verifier fit the round they are used for. No
     check ties them to it, so a mistake would give the round a wrong error term in both programs
     alike;
   - that the errors of four tests of the sub-proofs (one of a layer sub-proof with routed experts,
     one of attention, two of the head), none of which has a round of its own in a plan, are carried
     by the rounds that draw the point at which each is tested, and those of the range check's
     equations (in the Lean comments: the smallness test) by the round of the sub-proof's batching
     element. The conditions on which that rests are argued, not proved, in comments of the C++
     source (`plan_rounds.h` under `prover/prover/`, `prover/attn/` and `prover/head/`); nothing in
     this folder tests them, and the first of these comments says of its own that no code checks
     them (`Params/SubRounds.lean`, its head and the comments at `planLayerOwn`, `planAttentionOwn`,
     `planHeadOwn` and `planSmall`; `docs/format/FORMAT.md`, 13.6; row SO-12 of
     `docs/limits-all-rows.tsv`).
5. **Both programs depend on two properties that are not proved** (read): that their inequalities
   against wrap-around in the field are sufficient, and that the four equations of an acceptance
   policy (group 9 of `docs/format/11-4-output-head.md`) guarantee what the policy promises (the
   paper's definition of the acceptance policy), for which the only argument is in code comments
   (the Lean library has theorems on such a policy for an integer model of its own, which has not
   been compared with these programs). Exact match is a special case of those equations.

   A policy that passes the test for empty policies can still bar no token. That test
   (`policyEmpty`, `Model/Config.lean`) finds four kinds of policy by their numbers (read). In a
   whole call a checked token's cost is 2^sh plus its logit gap (`docs/model.md`, section 8). If
   theta is at least 2^sh plus the largest logit gap that weights within the ranges a key states can
   give (output matrix -4096 to 4095; embedding: "What the key states about the embedding"), every
   cost is at most theta, and theta is at most C. Both conditions of a clipped-gap policy (the
   costs, each clipped at C, add up to at most theta times their number; at most cap of them exceed
   C) then hold for every choice of the request's checked tokens, whatever C and cap are (reckoned
   from the sources, not tested). Such a policy is of none of the four kinds as long as theta is
   below C or the request has more than cap checked tokens. No other test on the lines `C`, `theta`
   and `cap` refuses it for a large C or theta (read). A call that names such a policy, checks at
   least one token of the request and passes every other check ends in `WITHIN LIMITS`. No such
   proof and no such call has been made (untested).

   A line of the parameter file holds a value below 2^32. At the sizes of the small examples
   `target_small_f2`, `target_small_f2_gap` and `target_small_f2_roomy`, some such theta is below
   2^32, by a bound on the gap that follows from the last normalization (reckoned from the sources,
   not tested). Below such a theta, which tokens a clipped-gap policy bars depends on the committed
   weights: an output matrix of zeros gives every token a gap of at most 1 (reckoned from the
   sources, not tested).

   The answer token has no cost, and the lines `C`, `theta` and `cap` do not enter its check: where
   a request runs to the last position, the equations are meant to make the answer the model's top
   choice there, ties to the lowest token id, under every policy (read). The first sentence of the
   comment at `policyEmpty` (`Model/Config.lean`) reads as if the test found every policy that bars
   no token; the comment's end says that a policy that passes can still let every token through. On
   policies that pass that test and bar no token, `docs/limits.md` and
   `verifier/docs/parameter-file.md` ("The acceptance policy") say the same.
6. **Tests cannot show that the two programs compute the same thing.** In none of the calls listed
   under "Tests" did only one of the two programs pass (where `cp_verify` alone can pass: point 18),
   calls in hostile environments (point 21) apart; in some the exit code or the last line differed
   (points 11 and 20). The differences known from reading are listed under "Known differences";
   comments in the source name further places where a function here asks less than its C++
   counterpart. That the decision functions test *all* of the protocol's equations rests on reading,
   not machine-checked. A file altered within the distance that the protocol tolerates can pass in
   both programs where no drawn position meets the alteration: the protocol promises nothing about
   such a file (reasoned; not run at the default setting).

**From one sub-proof to the next.** Where one sub-proof hands a committed matrix on to the next (the
request matrix to attention; the residual stream from group to group and to the head), the tie is
the code switch with kept members: the old code words are spot-checked at drawn positions against
the message sent anew. Its soundness rests on written arguments: that of the technical report, which
is not in this repository (`lean/CREDITS.md`), and the source's own five steps, which have not been
refereed. No Lean theorem is about the C++ programs' switch; the library (the rest of `lean/`) has a
code switch of its own beneath the Lean verifier `verify` (the kind K2), not shown to be the
programs' switch; this folder's theorems on its own program's switch treat the case without kept
members.

**The causal mask.** A position must attend only to itself and to earlier positions. Attention
handles the T positions in blocks of equal size. For a position in a later block than the query's,
the committed matrix of softmax weights has no cell. Within the query's own block the later
positions have cells, and the sums for the denominator and for the weighted values run over the
whole block. For these cells a lookup is meant to force the weight 0: the value that is looked up
packs the weight with the gap between the largest score of the query's row and the cell's score, and
for these cells both verifiers add a public constant to that gap, so large that only table rows with
the weight 0 can match. A second lookup is meant to keep the position of the row's largest score at
or before the query. Both programs form these two values from the same terms (read). The constant is
large enough only if every entry of the queries and keys lies within the bound at which the integer
model cuts it off, at all T positions of the request. The layer checks, not the attention checks,
test that, by lookups that bound each entry's value; the attention checks other than the range check
read each entry as that value (read, in both programs: no position, line of the parameter file,
range of a request or padding rule was found by which an entry escapes; the range check, which reads
single cells, was not read for this). The causal mask also depends on the step from one sub-proof to
the next (above), on the soundness of the lookup, the sumchecks and the range check, and on the
inequalities against wrap-around (point 5). No theorem covers these for either program (point 1). If
one of them failed, a later token could enter an earlier position's attention output.

Eleven proofs from a prover that breaks the causal mask try it (by their lists' own labels; by
these, in the three small ones the lie stands inside the computation and the statement stays true;
of the eight larger ones the lists do not say): ten put a weight from 1 to 65,535 on one to all of
the later positions of a row's block, in two layers; one puts a row's largest score at a later
position. Both programs rejected all eleven (tested by this project, on a test prover that does not
ship, so a reader cannot repeat it; each call once; not on builds of this repository's sources). All
are at small configurations of 64 tokens, on synthetic weights; none is at full size and none at the
default setting. Each request covers the last position alone, so no token comes after a position
that it covers, and in all eleven the false value stands in the row of a position that the request
does not cover. By the programs' output all eleven fail at the final linear test, in the one program
as in the other; that does not say which check was violated.

**What the key states about the embedding.** Both verifiers, alike, accept a key whose embedding
entries are wider than the 21 bits the parameter file states: the key's range proof covers each
embedding entry only within four signed bytes, so a committer that uses the wider range commits
another lawful model, and its key, entries and proofs are honest proofs of that model. What a key
file is meant to state of an embedding weight is only that each of its four digits is a signed byte
(format specification, section 18, the list "What ties the inputs of one chain or file to
another's", its item "The width of a weight"). Measured against that, such a proof is not of a false
statement (by reading, not machine-checked); the stated width is the honest committer's own limit.
See also `docs/limits.md` on the embedding's width.

## What has not been tested

7. **In one experiment, for most model checks (263 of 378), removing the check changed the result of
   no full call.** Altered files fail at a hash, a Merkle opening or a proof of work first. Two
   experiments damaged copies of the program, to see what the tests would notice:
   - *Checks disabled.* (not on builds of this repository's sources) In copies of 48 model files the
     question was put for each of 378 checks, one at a time: what changes if it is removed? Over
     4,860 full calls at the small examples' size, with made-up weights (9 honest, 4,624 with an
     altered public file, 227 with other command lines, other altered files or files of two examples
     mixed), the removal changed the exit code or the last line of at least one call for 115 checks
     and of none for 263 (128 of the 378 were run on calls with the check removed, not always on
     every call; for 245 a run of each call with nothing removed, made with a counter at each check,
     found the check's condition false in no call, so that its removal computes the same: reasoned,
     not run; 3 are reached by no call; 2 could not be removed). Seven of the 115 are choices, not
     rejections. In the runs that were made (890 of the 6,089 pairs of a check and a call in which
     it is false), for 98 of the 115 every changed call was a rejection that stayed a rejection, for
     2 a rejected call ended in `YES`, and for the other 15 the changes were of other kinds; more
     runs could only raise the 2 and lower the 98. For 121 checks nothing at all noticed the
     removal: no call, no build-time test, and none of the experiment's other alterations made the
     check fail. A check that changed no call is not thereby idle or wrong: no file among these
     calls makes it fail. No cheating prover ran in this experiment, and its entry point was a copy
     of a test program's, not the command-line program that users run.
   - *Single faults.* In a second experiment 2,252 single faults were introduced into eleven source
     files: build-time tests noticed 2,098. Of the others, 120 were each run on all of seven calls:
     honest calls on five small sets at the default setting (six end in `YES`, one in `WITHIN
     LIMITS`). Every ending stayed, so nothing noticed them there. The other 34 were noticed at the
     first of the seven calls, the only one to which they were put. An honest call passes every
     test, so it cannot notice that a test was removed (tested).
   - *The 120 that nothing noticed.* Of the 120, 41 remove a test, a part of a test or a step. By
     reading, none of these 41 reads the value of an element that a prover sends: 34 are on public
     numbers, on counts (three of them on how many elements were received) or on the order of the
     program's own steps, and 7 are on weights that the verifier computes from its own draws. The
     other 79 alter a term of the arithmetic. The one step is the call of a test on a public file's
     length; a later routine refuses under the same condition and the same name, so its removal
     changes no outcome.
   - *Why they go unnoticed.* For each of the 120 a reason is written down why it goes unnoticed. On
     a second reading the reason holds plainly for 101, with a remark for 7, for another reason than
     the one written for 9, and for 3 only because of how the function's callers call it. These are
     reasons and readings, not proofs, and the readings were made on another text than the one into
     which the faults were put.
   - *What the second experiment did not do.* It altered nothing that the verifier draws or reads
     inside a run, and introduced no fault at 53 of 2,305 places. Its entry point was a copy of a
     test program's, not the command-line program that users run, and no `cp_verify` ran in it: a
     fault's call is compared with the unaltered Lean program's own ending. The seven calls are
     honest ones alone: no altered, swapped or refused file at the default setting was put before a
     fault, the 2,098 faults that a build-time test notices were not put to them, and no counting
     run was made on them, so it is not known which of the 120 altered places they evaluate. None of
     the eleven files holds the code that reads the OOD answers: no fault was introduced into that
     code. All calls are at the small examples' size.
   - *The standard conditions.* One function of this program (`servedOf`, `Model/VerifyStages.lean`)
     sets the values of the twenty-one conditions of the standard parameter form that the stage
     request tests, which decide between a pass and `NOT-A-VERIFICATION`. `cp_verify` has eighteen
     of them: `attention`, `reading-as-printed` and `record-one-answer` are no conditions there: it
     refuses such a parameter file outright (point 16), where this program ends without a pass
     (read, in both sources; not run).

     Build-time statements pin each of the twenty-one fields (`Model/TestVerifyPlan.lean`). Beside
     those on exact match and on a named policy, ten set values at which the condition is met and
     values at which it is missed; these values alone are tried. Eight statements, and half of a
     ninth, repeat the function's own text: they show which value or function a field is and that
     its inputs are passed on, not that the condition is right. Two of the functions so named
     (`oneShift`, `normShifts`) have no other test, and the numbers 12 and 8 of the condition on the
     softmax table are tried at no value. That a missed condition gives its name is tested for each
     of the twenty-one (`Model/TestStages.lean`); what the stage then does, a run of `cp_verify` and
     soundness it does not test.

     That each of the three stages hands its list of missed conditions on to the function that makes
     the stage's result (`lastLine`) is tested by no build-time test. For the stages key and leaf
     two laws (theorems that restate a line of the program's own text) state it, of a stage that
     refuses nothing (`Model/VerifyLawsRecord.lean`; point 11); for the stage request no theorem
     does. (Tested, on code without these two laws: with the list emptied at each of the three
     places, every build-time test and theorem file that imports the file still built.) For the
     stage request two calls on files, run beside `cp_verify`, would notice if it did not, at one of
     its twenty-one conditions. No build-time test pins the stages key's and leaf's mark for a
     profile below 4; the same two laws state it. Only a call on one file would show a fault there,
     and none has tried it. Each statement is about its one field alone: none says what the stage
     then does, none compares with a run of `cp_verify`, and none says anything on soundness
     (tested).
8. **Checked tokens have faced no lying prover's proof at the default setting.** No lying prover's
   file has been run there; at a test's own pinned set 200 calls ran on such files (point 11, "The
   lying prover"); the false files at the default setting are a cheating committer's, at small size
   (point 11). Honest proofs with checked tokens have passed in both programs, at small size and, in
   one request, at full size (point 11). Where a changed checked token was rejected at full size, it
   was because the request is bound to the proof, not because the policy check said no.
9. **Proofs have been tested at few combinations of model options:** those of two small examples
   (`target_small_f2_roomy`, `target_small_f2_gap`), `target_small_file_f2` (not at the default
   setting) and of the full-size example at the default setting (by the examples' parameter files;
   whether the tested files had the same lines was not checked), and of fourteen small sets of files
   in each of which one model option is changed (honest calls only; not on builds of this
   repository's sources). "Model settings" lists twenty-six settings, three of them tested with a
   proof. At least twenty can pass in both programs, so a mistake in such a branch could, at worst,
   accept a false proof; five cannot pass, nor can a model without routed experts; for one it is not
   settled (read). For twenty-two of the twenty-four in the table, both programs derive the same
   schedules (tested; not on builds of this repository's sources); for the last two passing rows no
   such comparison is known. The list may not be complete.

   How a model file stores its weights (4-bit kinds, 8-bit, 16-bit floating point) is seen by
   neither verifier: the storage type stands in no public file. The widths that the parameter file
   declares are constants of the format, 13 bits and 21 for the embedding, and both verifiers refuse
   another value under the same names (`policy-weight-kind`, `policy-weight-width-emb`); what a key
   states of an embedding entry is wider than its declared width (see "What the key states about the
   embedding") (read). Files from the wider types have been tested, not proved, and not on builds of
   this repository's sources.

   On twelve sets of public files made from made-up weights stored in 4-bit, 8-bit and 16-bit forms,
   `cp_verify` and this program ended with the same exit code and the same last line in all 248
   different side-by-side calls. They accepted each set's own files (36 calls: 12 whole, 24 of a
   part) and refused everything else that was tried (212 calls): one bit turned in the proof, the
   request, the answer, the key, the entry or a configuration file; another token as the answer; an
   ID, key or configuration that did not match; another set's proof; a proof one byte short, one
   byte long or empty. What the programs print above the last line was kept for 104 of the 212
   refusals. In 56 of them it was the same to the byte. In 48 it differed only in the words for the
   fault, a sentence in one program and a name in the other, which fit each other by reading, not
   machine-checked. No weight outside its declared range and no well-formed weaker policy was tried.
   These forms were checked under one and the same configuration, once without and once with proof
   of work. Four of the twelve sets are of a small synthetic model.
10. **How much has been run at the default setting, and at full size.** The calls told on this page
    at the default setting are these: 2,377 calls at the parameter files of the small and full-size
    configurations under `prover/examples/`, 706 of them at full size (point 11); eleven calls, in
    no sum, at a parameter file of the set's own which is reported to have the default setting's
    protocol lines (OOD answers, counted proof of work), with a clipped-gap policy in place of the
    default's exact match, and whose other lines were not looked at ("Tests", the row on real
    weights); the eight rounds at the stored small example in point 24 and the calls in the item
    "These sources" under "Tests", in no sum; one run of Lean's interpreter on one small set ("Do
    the checks ever say yes?"); the seven honest calls of point 7's second experiment, with their
    runs on altered copies of the program; and trials of the planning code in point 11, which read
    no key, entry or proof file. At full size no false proof has been tested, and real weights in
    eleven calls only, each once: every rejected file at full size is a damaged or swapped honest
    one. Where the refused calls end was not examined; none is known to reach the protocol's
    equations. Of the calls of points 18, 20, 21 and 24 the records do not show the parameter file;
    the protocol's parameters have no bearing on what they test. The 200 calls of "The lying prover"
    (point 11) are at a test's own parameter file. The calls that bear "not on builds of this
    repository's sources" are none of the calls listed above, and are in none of these sums.
11. **The OOD answers (the line `record 1`).** The protocol
    publishes OOD answers: proximity tests up to the Johnson radius, with proof of work, for a
    request's, a batch's and the committer's files. `prover/examples/TARGET-KITS.md` tells its
    lines.

    - *The rule, and what is printed* (read; the C++ library's files that check a key and an entry
      were not read for it). Of the accounting's two sources for a proximity term (point 4), the
      standard condition on the committer's files admits proximity terms that rest on the proved
      lemma or on the theorem on codes (`Model/VerifyAccount.lean`). The printed line `commitment:
      ...` ends with `cp_verify`'s clause "; the table has a record: the binding of the weights
      rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given", and the line
      `result-v1` has `record=1`. "The binding of the weights" is the programs' own printed word:
      nothing of it is proved in Lean of the programs. These are a full call's lines: `verify -key`
      and `verify -leaf` print neither, so nothing in their output names the OOD answers or shows on
      which source the file's proximity terms rest; `cp_verify`'s report on the stage does. This
      program prints none of the stages' reports, so not `cp_verify`'s lines `accounting: one-time
      files: ...`. This code was written after `cp_verify`'s, so the two programs are no more
      independent here than elsewhere (point 3).
    - *No soundness theorem of this folder is stated at the default setting, and no tie from a call
      to the compiled verifier of one IOP (`verifyOneProtocol`) reaches a file of that setting.* The
      theorems that start from a pass speak of a program that can return 0 where proximity terms
      rest on the theorem on codes, which this folder takes as given; the library proves the
      statement that stands in its place (`Cb/Bridge/CodeListRSProved.lean`; point 4), tied to no
      program. The truth of an accepted request and the binding of the weights both rest on the
      theorem on codes, and, at the default setting, both lean on counted proof of work in the
      rounds that draw positions. The work of the committer's files is done once for a commitment,
      by an honest and by a cheating committer alike; the proof file's for each request or batch
      (read). `Tie/LeafCall.lean` leads from the exit code of `verify -leaf` to a yes of
      `Entry.check`, and `Tie/EntryRecord.lean` from such a yes, at parameter bytes written out in
      Lean for the full size, to an accept of the compiled verifier of one IOP. No file proves of
      any files that the bytes of a call are these, and that the check says yes on some file at
      these bytes is not shown. So no such tie reaches a file of the protocol; of the IOP inside
      that compiled protocol, at the decision and the keys that the program makes, soundness is
      stated round by round, for a language that is a disjunction of four clauses, at three of which
      it says nothing, under the one hypothesis on codes (`Slice/FullRecTable.lean`,
      `fr_link_sound_own`; the counts: `Slice/FullRecNum.lean`, `fr_err_below`), and no theorem that
      this folder names joins that statement to this yes or to a call's bytes (read). That our
      parameters meet the conditions of the theorem on codes is our own reckoning, with no bits to
      spare (`docs/limits.md`; point 4). Nothing in this folder checks any of that.
    - *The laws pin the program's text, not a call's decision.* The laws of
      `Model/VerifyLawsRecord.lean` pin the rule, what is handed to it, the flag, the condition
      `record-one-answer` and the ends of the stages key and leaf. They restate the program's own
      text and claim nothing on soundness. Four altered copies of the program, each of which
      switches the condition on the committer's files off (`keyStage`, or `leafStage`, asks for its
      accounting with `false` in the place of `true`, so that the condition is never asked of that
      file; both hand `false` to the list of conditions; that list lacks its last line:
      `Model/VerifyStages.lean`), and a fifth on `record-one-answer`, each stop that file from
      compiling (tested; such a stop shows that a line is pinned, not that a behaviour was held
      against anything independent). Of what was tried, the laws alone hold the four copies' lines:
      the four passed the five test modules that were tried (the other test modules were not tried),
      and none of the calls told below would notice them, since none ends at that condition. By the
      file's own head a change of what `Common.acct` does with three of its arguments does not stop
      it.
    - *What a stage hands on.* No build-time test evaluates what the stages key and leaf hand on
      besides their ending (the accounting's counts, the work). Two laws state the whole value that
      a stage hands on (`keyStage_end`, `leafStage_end`); whether they catch what follows has not
      been tried. A copy that zeroes one count passed sixteen of the laws, these two not among them,
      and every test of this folder. The like holds of what the stage request hands on, and no law
      of `Model/VerifyLawsRecord.lean` states that stage's whole value: a copy that adds 32 bits to
      the least round's figure passed the same laws and tests too (tested: one run each, known from
      a report alone).
    - *What no build-time test does.* None runs a stage or a whole call, and none shows well-formed
      but lying OOD answers ending in a refusal (read). By the head of `Model/TestRecordWork.lean`
      no test holds the term for the OOD sample's own round (`sizeRecordedTable`,
      `Params/Group.lean`) to `cp_verify`'s: every file with OOD answers that a test has carries
      `work sample 0 0 0`. That the OOD sample's own round counts no work has no build-time test
      either. A copy with a laxer term for the OOD sample's own round (`Params/Group.lean`) passed
      every module that was built (tested: one run, known from a report alone).  With `record 1` and
      `answers 2` the condition `record-one-answer` alone stands between a file and a `YES`: laws
      and a build-time test pin it; no call on files has tried it (read).
    - *The planning code.* Trials of both programs' planning code (this program's run by scripts
      that are not in this repository) found, at the one parameter file that ships among those
      tried, the same digest of the files, the same number of rounds, the same stages, columns and
      batches, the same counts by source, and the same error terms with the same counts; counts were
      compared, not round by round (tested: one run). Six places of the planning code choose between
      the one-time and the later distance; the two are equal in every parameter file that ships or
      that a build-time test has, so no such test and no run on files can tell a swap.
    - *What has been run side by side,* with made-up weights (tested; each call once): 2,377 calls
      at the default setting. In none did only one program accept or pass; both did in 174, neither
      in 2,203. The exit code was the same in all; where the whole last line differs, both refuse,
      `cp_verify` as `chain-refused` and this program as `proof-refused` (point 20). Wherever they
      are printed, the lines `commitment: ...`, `covered: ...`, `the call: ...` and the line on
      proof of work were the same byte for byte in both programs, and in the lines `result-v1` only
      `build=` differs (on the builds that were run; for builds of this repository's sources, see
      point 20). The calls by parameter file and by kind of files (nothing in the files shows which
      program made them):

    | parameter file (the `policy.txt` of a folder under `prover/examples/`, or what it is) | files | calls | both accept or pass | neither |
    | --- | --- | --- | --- | --- |
    | `target_small_f2_roomy` (default setting, small) | six honest sets | 1,307 | 76 | 1,231 |
    |  | a cheating committer's, made by a program that is not in this repository (three sets) | 104 | 40 | 64 |
    | `target_small_f2_gap` (default setting, small, clipped-gap policy) | two honest sets | 260 | 18 | 242 |
    | `target_full_f2` (default setting, full size) | three honest sets, two of them three requests of one batch | 706 | 40 | 666 |
    | all |  | 2,377 | 174 | 2,203 |

    - *The calls in detail.* 706 of the calls are at full size and 260 under a clipped-gap policy.
      Of the 174 passes 54 are whole calls, 10 of those at full size: seven honest calls and three
      controls of a test, each of which repeats one; the other 120 are calls on one file (`-key`,
      `-leaf`). Among the passes are `-leaf` calls beside a key file altered or cut behind its OOD
      answers: of a key file `-leaf` reads the head, the root and the OOD answers alone. On the
      cheating committer's sets both programs refused every whole call on a lie; calls on one file
      passed in both where the lie is not in that file's own test, and the other passes there are
      honest calls and controls. The table counts a call under its set's parameter file also where
      the file handed over was an altered copy (all refused by both). But for the cheating
      committer's, the refused files are altered, cut or exchanged honest ones, honest ones under
      another ID or an altered parameter file, or honest ones in a whole call that does not qualify.
      Of the calls with `-no-proof-of-work`, each on honest files, 11 at the default setting, 3 of
      those at full size, ended in `NOT-A-VERIFICATION` in both programs. At full size one request
      covers tokens 24 to 1,023, and under a clipped-gap policy two small requests cover tokens 16
      to 47; every other request at full size covers the next token alone.
    - *The lying prover.* At a test's own pinned set of files, under OOD answers and counted work,
      whose parameter file is none of the configurations under `prover/examples/`, 200 calls ran on
      files of a prover that lies; they are in no sum of this page. Both programs ended every call
      with the same exit code and the same last line. All 96 lies were refused by both
      (`proof-refused`): by their names 74 are on a value of the computation, 17 on a weight's code
      and 5 on a policy's bounds. The 96 are reported to be 95 different false proofs: two of the
      lying cases bear one proof. Both accepted or passed the other 104 (100 `YES`, 4 `WITHIN
      LIMITS`): by their names 91 controls (the lying program with a lie of zero) and 13 honest
      runs. The measure of these calls: small size; made-up weights; one shape of request in 191 of
      them (the next token alone) and two more in the 9 on a policy's bounds; each lie a fixed one
      at one named place, so no prover that searches; the lying program and both verifiers come from
      one tree; a refusal prints no line on the OOD answers or on work, so that the 96 stand under
      both is shown by nothing but their controls' like files; `cp_verify`'s half repeats a run that
      was made when the files were made, and this program follows `cp_verify`, so "refused by both"
      is one witness, not two (point 3); whether a lie makes the statement false was not looked at
      (tested; each call once side by side). Both programs in these calls were built from copies of
      the sources that differ from this repository's; neither from this repository's.
    - *What no run has covered.* At full size at the default setting, apart from point 10's eleven
      calls at a file reported to have that setting's protocol lines: no clipped-gap policy and no
      cheating program's file, and one honest request alone that covers more than the next token.
      Under a clipped-gap policy at the default setting: honest sets within their limits alone; no
      call beyond the limits, and none that states another policy than the file's. At the default
      setting, no set under the `policy.txt` of `target_small_f2` or of `target_small_file_f2`. At
      `target_small_f2`, `cp_commit` is expected to make no commitment (its worst-case check ends
      with status 7 under a drawn seed, since that folder's scales leave places short of room:
      reasoned from the pages on that folder, not run), so `target_small_f2_roomy` and, with a
      clipped-gap policy, `target_small_f2_gap` are the small examples that can be run at the
      default setting. No file of a lying prover at the default setting: the false files there are a
      cheating committer's (the 200 calls of "The lying prover" are at a test's own parameter file).
      As far as we know, no first table or copy that is no code word near the Johnson radius has
      been made or played at that setting by any program of ours, and on real weights at that
      setting's protocol lines only the 11 calls of one row of "Tests" have been made: three honest
      requests under a clipped-gap policy and eight damaged inputs, none under an exact match and
      none from a cheating program. By reading of its source, not machine-checked and not run,
      `cp_commit` refuses to commit under a parameter file that misses a standard condition.

12. **The schedules** come from this program's own version of the C++ planner. Trials of both
    programs, not a theorem, show that the two agree at the one parameter file that ships among
    those tried (point 11, "The planning code"). A parameter file with more than one answer per
    sample is untested. The build-time tests in this folder run no C++ program and read no file:
    where they compare with C++ output, they compare with constants stored in the Lean source, and
    where those came from is stated only in comments (read).
13. **Coefficients.** On fifteen honest proofs, checksums over the coefficients of the layer checks
    match `cp_verify`'s at 390 places (not on builds of this repository's sources); the comparison
    stops before the closing steps of the range check. For attention, on one honest proof the
    verifier's state after the first 278 of a sub-proof's 1,191 claims matches `cp_verify`'s (not on
    builds of this repository's sources). The build-time test compares each vector by its length and
    one checksum; an entry-by-entry comparison was made once, by a program that is not in this
    repository (tested). Nothing else compares coefficients.
14. **Two internal self-checks are weaker than their names suggest,** in both programs (read): one
    on the padding, one on the indices into the prover's tables. An indexing error in the verifier's
    own formulas could go unnoticed. `cp_verify` has six further self-checks that this program
    lacks: they compare a block's numbers with what its plan says beside a round (the comment at
    `Chan.settled` in `Iop/Ground.lean` names them). Both sides of such a comparison come from the
    configuration files, so no key, entry or proof file can trip one; where `cp_verify` would stop
    there, as at a mistake of its own, this program would go on (read).

    **One rule of the format is kept file by file, in both programs** (read). This program, like
    `cp_verify`, keeps its list of the tree vertices that it has met file by file, not across the
    files of one verdict as the format's rule R7.14 asks (`docs/format/FORMAT.md`, R7.14; 17.2, item
    4, which does not name this program). It is one process and starts each file's check from the
    empty list (`Session.start`, `Chain/Session.lean`; `Reading.fromStart`, `Proof/Reading.lean`).
    The two ways differ only on files that show two values at one vertex under one root, that is a
    collision of the hash. No bound depends on it.

## Known differences from cp_verify

15. **Lookup tables: this program could accept what `cp_verify` rejects.** It computes the model's
    four lookup tables in integer arithmetic; `cp_verify` uses floating point and the platform's
    math library. On one platform (x86-64, glibc 2.39), two tables were compared entry by entry for
    every accepted parameter, the rotary table for the parameters in use and 70 others, and the
    table of exponentials by digest for one pair of parameters (tested). Another math library is
    untested. Without digest lines in the parameter file, nothing compares the tables; such a file
    cannot pass in either program (point 19; read, untested).
16. **Public files: this program could accept what `cp_verify` rejects.** Two of `cp_verify`'s
    checks on the public files, both in its planner and both on how a tree that holds a mask is
    opened, are not implemented here (read). Whether public files can fail one of the two without
    also failing one of the conditions below is not settled. One of the two rules (no second list of
    positions) is asked again at the run, in both programs; the other (no reading in another chain)
    `cp_verify` asks again at the run too, and in this program no like place was found (read: one
    search for one name). `cp_verify` also compares, while it runs, the shapes on which a stage runs
    with those from which the plan's errors were computed, and ends the process if they differ; this
    program does not (header comments of `Iop/Prox.lean` and `Iop/Link.lean`): in every call both
    come from one value, so no file is known to tell the difference (read).
    - *The ten hiding conditions.* Ten conditions on the public files (the *hiding conditions* of
      `../GLOSSARY.md`), such as mask sizes, are needed for the design's hiding argument to apply.
      They are necessary, not sufficient: files that meet them are not thereby shown to hide
      anything. Both verifiers ask all ten, and this program asks the same inequalities as the C++
      source (read, line by line). Each is tested once at its boundary, and two violating sets of
      files were rejected in full calls (tested; not on builds of this repository's sources).
    - *The number 129.* One number in them, the bound 129 on the cells of a request's range-check
      matrices, is not in the public files: it is written in both verifiers' sources. Each verifier
      reads it at one place only, the yes-or-no test of these conditions; it enters no equation,
      bound, wrap-around margin or schedule of the checks on a key, an entry or a proof (read, by
      search in both sources). Neither verifier tests that an honest prover's cells stay within it.
      Another value could turn that test's yes into a no or its no into a yes, that is, admit or
      refuse a configuration. No check on a key file, a copy's file or a proof file reads the
      number, so with the public files admitted these checks come out the same whatever it is. This
      rests on a reading of the sources; nothing is proved about it.
    - *The provider's own programs.* The provider's own programs, `cp_commit` and `cp_prove`, also
      form a configuration only if all ten conditions hold, so a provider that uses them cannot
      serve under files that miss one of them (read); a verifier does not see whether they were
      used.
    - *For a false proof file.* No way was found in which a false proof file gains from any of this.
      That is a reading's finding, not a proof.
    - *Which tree an opening belongs to.* This program goes over a chain of a key file or a proof
      file twice: once without the file, to lay out from the public numbers what the chain must
      hold, and once on what was read from the file. Where a file's second chain opens columns of
      trees that it takes over from an earlier chain, the run on the file tests each opened column's
      position and width, and their total, but not to which of the taken-over trees the opening
      belongs: several trees share one number there (a tree's number less the chain's first own
      tree's, cut at 0): those taken over, and the chain's own first tree (`Iop/Ground.lean`). That
      the two runs cannot differ in this rests on a rule for whoever writes this code (stated in
      that file's header comment); no type, no theorem and no build-time test enforces it. Two
      readings found no way for a file to make the two differ. One place was not traced to its end:
      which taken-over trees a proof file's second chain opens is steered by a list that comes from
      `Model/`, whose making was not read for this (`Iop/Lin.lean`); a key file has the same two
      uses (`Key/File.lean`). The program does not make the four tests for which this folder has a
      function (`openedByPlace`, which the program does not import). `cp_verify`, whose source this
      program follows, does not have this gap: there each opening is checked against the root that
      the verifier received for that very tree, in the verifier's own order, and no field of a file
      selects a tree among those sent in it (the proof's head names the copy's file, whose own check
      ties its table to the key by the LINK proof). (Read; nothing was run.)
    - *What a parameter file's lines may say.* `cp_verify` also refuses, as `parameter-range
      (policy)`, a parameter file whose line `reading`, `rowcost` or `answers` is not 1, or whose
      line `listed` is not 0; this program's reader admits `reading` and `rowcost` 1 or 2, `answers`
      1 to 4 and `listed` 0 to 8 (`Params/File.lean`). It refuses a line `prof` other than 20 too
      (`policy-profile`); there this program does not pass either (point 19; the condition
      `attention`). At `reading 2` and at `answers` 2 to 4 a standard condition keeps a call here
      from passing (`reading-as-printed`, `record-one-answer`); none of the twenty-one reads
      `rowcost` or `listed` (`servedOf`, `Model/VerifyStages.lean`): under such a file, if its
      rounds meet their target at the count that gives the larger error, this program could pass
      where `cp_verify` refuses. An accept of this program at such a file is no evidence about a
      proof: the parameter file lies outside what `cp_verify` and the released provers admit, so no
      honest file is made there (read, in the sources; not run). The Lean verifier `verify` is not
      touched by this: its scope fixes these four lines at `reading 1`, `rowcost 1`, `answers 1` and
      `listed 0` (`VerifierAndGoals.InScope`, `lean/Ladder.lean`; `lean/Ladder/Stored.lean`).
17. **Printed proof-of-work figures.** `cp_verify` computes them in floating point, this program
    exactly. There could be public files for which one program passes and the other prints `NOT
    CHECKED`; none is known (read). The figures in bits that the line on proof of work and the
    fields `least-round=` and `least-round-without-work=` of `result-v1` show can differ by one
    hundredth between the two programs. Where a round's bits lie less than a millionth above a whole
    hundredth, `cp_verify`'s figure can be the lower one. Where they lie within the rounding error
    of a floating-point logarithm of a whole hundredth, either program's can be the lower (reckoned
    from the sources, not tested). Where two rounds' errors agree in their leading 64 bits,
    `cp_verify`, which compares rounded numbers and then names, and this program, which compares the
    exact bounds, can name different rounds as the weakest without its work; the two printed numbers
    are the same (header comment of `Model/VerifyAccount.lean`, "What differs from the C++", items 2
    and 3). That has been seen at made parameter files, and not at the one parameter file that ships
    among those tried in the trials of both programs' planning code (point 11) (tested). These
    trials make no call's decision. By the same header comment more can hang on that order: where
    the two programs take different rounds as the largest, the printed bits of work can differ too,
    and so can the one decision that this point's second sentence tells, in either direction; what a
    proof of a false statement could gain from this difference is not claimed or proved there
    (read).
18. **This program refuses more, and costs more.**
    - *Limits on length.* A file longer than 268,435,456 bytes, a parameter or layout file longer
      than 1,048,576 bytes, or a test command's file longer than 4,194,304 bytes gives `NO:
      file-too-long` (read). The stored full-size example lies far below the first limit: its proof
      file has 18,779,540 bytes, about 7 % of it, its key file 3,290,496 and its copy's file
      2,942,944 (`examples/full-size/`; counted). `cp_verify` rejects such a parameter file, and a
      request or y file above the first limit, under another name (read). That every admissible
      parameter file is far shorter (at most 46,329 bytes) rests on a count, not a proof.

      A layout file above the limit can be valid, since `cp_verify` skips blank and comment lines: a
      commitment made over such a file verifies there and is rejected here, so a whole call could
      end in `YES` there and in a refusal here; no such call has been tried. The full-size example's
      layout file has 0.2 MB (read). Beside a key file above the first limit `cp_verify -leaf`,
      which reads of it the head, the root and the OOD answers alone, can pass where this program
      refuses the call (read). In one kind of call, counted in none of this page's sums, that was
      seen: on an honest example whose key file had been padded with zero bytes to one byte above
      the first limit, `cp_verify -leaf` ended in `PART PASSED` and this program refused the call
      with `NO: file-too-long`: it is the key file that is too long. Nothing false was accepted:
      these parts were honest; a call on one file never ends in a yes; and `-key` and the whole call
      refused the padded key file in both programs, at every padded length.

      With one byte of padding, and at exactly the limit, `-leaf` passed in both programs (tested:
      in that call and 36 further ones on key, entry and proof files padded to one byte below, to,
      and one byte above the limit, in which the two programs ended differently in that one kind of
      call alone, by that run's own table, and then in nine calls on a stored example; each call
      once; neither run's table has been checked a second time). The routine with which `cp_verify`
      reads these files has no limit on length (`readWholeFile`, `verifier/src/vf_common.h`); this
      program's limit can only turn a pass into a refusal (read).
    - *A slow layout file.* Below the limit, a valid layout file that cuts an array into many small
      blocks is slow here, because this program compares each pair of block lines: with 2,048
      one-element blocks the `plan` command took 2.0 s here and 0.45 s in `cp_verify`, and with
      26,624 (1.04 MB, the most under the limit) 132 s and 1.7 s (tested at six sizes; one call
      each, on a busy machine).
    - *Memory and time.* A full-size call needed about 1.5 times the memory of `cp_verify` and more
      than 5 times its CPU time (tested, on builds of copies of the sources that differ from this
      repository's; not on a build of this repository's sources; the figures of a further full-size
      call beside `cp_verify`: "Tests", "These sources").
    - *Public files outside the standard conditions.* Public files outside the standard conditions
      can keep a call busy before it ends without a pass: at the largest admitted size, one routine
      in the attention checks takes about 27 s per group of layers before the proof's chain is read
      and 54 s on the proof; within the standard conditions, at most 0.15 s per attention link (one
      measurement of the routine alone; the counts by reading).
    - *Deep recursion.* The source lists seven functions that the program reaches as having no known
      bound on the depth of their recursion at every caller ([Guard/README.md](Guard/README.md),
      last section). For six of them none is known; the seventh, `Fmt.Dr.times`, is bounded at 64
      (by reading, not machine-checked). A file that drives one of the six deep enough ends the
      program with a stack overflow; it cannot turn a rejection into a pass (read). In runs on files
      made for the purpose, the runtime printed its own message and the process ended with exit code
      134, which is none of the program's own (tested).
    - *A panic.* In Lean's logic a read of an array out of range (`a[i]!`, `get!`) is the type's
      default value, and a write out of range (`set!`) leaves the array as it was: to that extent
      the theorems on `main` cover such a step. Compiled code reports a panic there and, unless the
      environment variable `LEAN_ABORT_ON_PANIC` is set, goes on; that it goes on with the logic's
      value is trusted, and no file here shows it (reckoned from Lean's behaviour). In the code of
      the 200 modules of which the program is built a search finds such reads at some 90 places, all
      in three files of BLAKE2b (`lean/Run/Blake2b/`), such writes at some 100 places in nine files
      (theorems' texts among them), and no `panic`, `unreachable!` or `toNat!` (searched by
      program). Whether one of them can be out of range was not looked at. In the twelve pairs of
      whole calls of "These sources" ("Tests") nothing was written to standard error, where by
      Lean's behaviour a panic's message would stand (tested).
19. **Unsupported parameter files.** This program supports only parameter files whose profile
    includes the attention proofs, that use routed experts, and that have the 32 digest lines. For
    any other file it prints `NOT CHECKED`, where `cp_verify` reports `NOT-A-VERIFICATION` or `NO`
    (read, untested).
20. **Names and output.**
    - *The name after `NO:`.* The name after `NO:` can differ, and `cp_verify` can print `NOT
      CHECKED` where this program prints `NO`: this program reads all chains of a proof file before
      it tests any equations, some checks have no name here, and files with two errors can fail
      under either name (read). At a file whose version word is not this format's both refuse, and
      the names part: this program has four names (`version-of-an-earlier-format`,
      `version-of-another-field`, `version-of-another-hash`, `version-unknown`), `cp_verify` the
      last alone (read, in both sources; not run).
    - *The names that this program can print.* A program compared the two programs' lists of names
      (over copies of the sources that differ from this repository's; not over this repository's):
      of the 1,075 names that this program could print there after `NO:` or `NOT CHECKED:`, 799 are
      `cp_verify`'s own names (19 of them without a word that `cp_verify` appends), 174 occur in the
      C++ sources only as a file reader's reasons, which `cp_verify` never prints as a name, and 102
      are this program's own, 85 of which a full call shows only in its closing line on the stage
      that rejected. One name that is not among the 1,075, `internal-f-read-weights`, `cp_verify`
      has too. That does not show that a name stands at the same check in both programs. No
      build-time test holds the two lists of names `Tail.names` and `Heard.names` against the names
      under which these files refuse, but for that last name (read): a name that begins with
      `internal-` and is missing from every list would turn `NOT CHECKED` into `NO: proof-refused`.
    - *Exit codes.* The exit code differs in several of the cases of points 15 to 21. One more: a
      request or y file of a wrong length that cannot be opened, for example for lack of read
      permission, gives `NO` with exit code 1 in `cp_verify`, which asks the operating system for
      the length first (for the request, only if the parameter file has a line `lt` of at most 20,
      as every admissible one has), and `input-unreadable-...` with exit code 2 here (tested).
      Neither program passes.
    - *Other lines.* This program prints `cp_verify`'s closing lines, with the exceptions listed in
      the header comment of `Shell/Lines.lean`, but not its report on each stage. One exception
      more, which that comment does not list: in the line `commitment: ...` this program prints "the
      proved lemma" where `cp_verify` prints "the bound within a third of the distance"; and where
      no proximity term of the committer's files rests on another source it prints "every closeness
      round of the one-time files rests on the proved lemma", where `cp_verify` prints "0 closeness
      rounds of the one-time files rest on another source than the bound within a third of the
      distance" (read, in both sources; not run). Of the causes of a `NOT-A-VERIFICATION` it prints
      two (no `-id`; `-no-proof-of-work` where work is counted), not those that `cp_verify` repeats
      from its stages: a call without `-no-proof-of-work` that names an ID, asks for fewer than 128
      bits and fails no check ends in `NOT-A-VERIFICATION` without a cause here (read). The option
      has been run in 178 calls beside `cp_verify` (tested). In one comparison line by line,
      something differed in 10 of 150 calls, including the exit code of one `plan` call (tested).

21. **Hostile environments.** If standard output is closed, if memory or file descriptors are
    starved, or if a file is overwritten during the call, the two programs can end differently, and
    one alone can pass: for example with exit code 2 here where `cp_verify` rejects, with exit code
    1 and no `NO:` line when the Lean runtime fails, or with a signal under a small stack. In one
    series of tests 125 such calls passed in one program only: 117 honest calls, and 8 in which a
    true file was overwritten 20 ms after the start. In three of those 8 this program passed and
    `cp_verify` did not, in the other five the reverse; that the program that passed had read the
    true bytes first is inferred in all eight, not shown. Those eight apart, no false or damaged
    file was accepted (tested).

## Other commands, and direct calls

22. **The five test commands are no verification of a model's files.** `product`, `links`, `key`,
    `entry` and `toy-proof` check files from the C++ library's small test protocols and never print
    `YES`. Their pass, `TEST FILES PASSED`, has exit code 3, like the pass of `verify -key` or
    `verify -leaf`, and only the last line tells the two apart. They accept any `-bits` up to
    1,000,000, even 0. `entry` does not check the key file's own proofs; `toy-proof` does not check
    the file that identifies the table, and reads the form of the claims from a file that no hash
    binds (read).
23. **The three checks take their parameters and their table from the caller.** That holds of the
    checks of a key file, a copy's file and a proof file alike. Every `verify` call, full or on one
    file, derives the parameters of all seven chains from the three configuration files in one step
    (`planned`); only the full call's yes covers all three files. In a full call that returns 0, in
    Lean's model of input and output, the three checks ran under one planner call's parameters, each
    later one against the table that the earlier one returned; and the parameters of the seven
    chains, as the program made them from the three configuration files it read, all hold the digest
    of these three files, and the five of them that hold a shape of the tables hold the same one
    (`main_zero`, `main_zero_same`, proved for the Lean source; `THEOREMS.md`, "What ties one file
    to another"). That says what the program derives from the configuration files, not that the key,
    entry or proof file is bound to that digest or shape. Beyond that nothing proves that the three
    sets of parameters fit each other, and no type keeps a caller from handing a proof's check a
    table whose key was never checked. So if you call `Key.check`, `Entry.check` or `Proof.check`
    directly, you must guarantee what the command line guarantees: schedules that are derived from
    the public files and meet their target, a table that has passed the checks on its key and its
    entry before a proof is checked against it, and one source for a chain's description, statement
    and shapes (read).

    The reader of the one-time chain's plan does not itself check R13.15's RECORD entry nor the
    salt; it relies on the planner that wrote the plan. The reader is `KeyChains.read`
    (`Params/Chains.lean`). The format's rule R13.15 asks that this plan have an entry `RECORD`, for
    the table's own OOD sample: that the reader accepts a plan without it is tested at build time
    (`Params/TestChainsTogether.lean`); that it does not compare the tables' salt length with the
    plan's is read, and likewise `Declared.keyFormOk` (`lean/Fmt/Parsed.lean`, which this program
    does not import, and which does ask for the entry) does not compare it with its setting's. No
    parameter file that the parameter reader admits yields such a plan: the planner writes the
    RECORD entry unconditionally (`Plan/KeyOneTime.lean`; `Params/Planner.lean`); the limit is of
    plan bytes fed by hand, as at `Key.check` (read).

## The text that `main` runs

24. **`main` runs a second writing (the same checks written out once more, with the hash as an
    argument) of four of the seven fields of the program's record of checks (`Checks`).** `main`
    (`Main.lean`) calls `Shell.programFront` (`Shell/Front.lean`). There the whole call, the call on
    a key file, the call on a copy's file and the plan are taken from the text under
    `ChecksWithHashAsArgument/M/`. That text takes the format's hash as an argument, and at one call
    (the request file's digest) the second hash function too (a second, fixed hash function, built
    on BLAKE2b's compression function; `Hash/SecondHashFunction.lean`); `main` hands it the
    program's own two hash functions. The first argument is the format's hash of five arguments
    (three numbers and two byte strings), not BLAKE2b and not an oracle on strings. No theorem says
    that it reaches every call of the format's hash: the shell's lines on a plan call the program's
    hash by name. But for that one call the second hash function is called by name, whatever the
    second argument is (header comments of `Shell/Front.lean` and
    `ChecksWithHashAsArgument/M/AtPort/Spine.lean`). The list of names, the list of places and the
    first tests of a call are those of the first writing (`Shell/Checks.lean`, `Model/Verify.lean`).

    What ties the two writings. The theorems on the program are stated of the first writing
    (`Shell.program`). That `main` equals `Shell.program` is a theorem (`OnBytes.Shell.main_eq`,
    `Shell/AtMain.lean`; it rests on four equations of
    `ChecksWithHashAsArgument/M/AtPort/Spine.lean`), not the unfolding of a definition. It is an
    equation between Lean's terms at these two hash functions. It says nothing of compiled code, and
    nothing at another hash function. `main` itself takes no hash function as an argument: it is not
    a function of (files, hash).

    What that means for the compiled program. Eighteen modules stand below `main` for the second
    writing alone (read: by the import lines; tested: the guard's commands (`Guard/README.md`)
    passed over them with no exception added). The first writing's four functions are named in a
    record that `main` uses, so they may be in the executable too. In the second writing a round's
    message is put together and hashed anew for each call of that round, where the first writing
    hashes the part that the calls share once (read).

    The calls told in this item were made on copies of the Lean files that differ from this
    repository's; none of them has been made on this repository's. Tested: a build in which `main`
    calls `Shell.program` and a build in which it calls `Shell.programFront` were run on eleven
    kinds of call at each of two examples, a small one and a full-size one (an honest call; the same
    with `-show-stages`; no `-id`; another ID; one bit turned in the proof file, in the key file, in
    the copy's file; `-key`; `-leaf`; `plan`; no argument). On all 22 calls both gave the same exit
    code, a standard output of the same length and checksum, and a standard error of the same
    length. Each call once. This is a test of 22 calls, not a theorem on compiled code, neither
    build hashes what these sources hash ("Tests", its first item), and no such comparison has been
    made on builds that do.

    Time and memory (tested; honest whole calls alone; the two builds in turn, the order swapped
    from round to round, on shared machines with most cores idle (load 4 to 15 on 64 or 96 cores);
    no refused call was timed this way; ± is the sample's standard deviation). At the full-size
    example, four rounds a build: 112,104 ms ± 649 with the first writing, 112,088 ms ± 1,917 with
    the second. At the small example, sixteen calls a build, eight with `-j 8` and eight with `-j
    1`: 6,020 ms ± 59 and 6,090 ms ± 122 (with `-j 1` alone 5,991 ms ± 63 and 6,113 ms ± 159, 2.0
    per cent more). At the stored small example, eight rounds a build (the first a build without the
    second writing, the second the build of the item "These sources" below; the two differ in more
    than the second writing): 6,627 ms ± 35 and 6,645 ms ± 63. By the means the second writing took
    0.0, 1.2 and 0.3 per cent more time, which is within about the spread from call to call. The
    greatest memory in use was alike: 5.2 GB at the full size, 0.27 GB at the small one.

## Tests

**Two programs that agree on these calls prove nothing about either.** Which calls were made at the
default setting: point 10. All weights are synthetic ("made-up weights" on these pages), except in
one row, of eleven calls. That weights are synthetic or real, and which program made a file, is
shown by nothing in the files, and no run told here has checked it. Each call was made once, except
the seven small pairs of the item "These sources", which were made twice.

- *The programs that were run differ from these sources.* Both programs in the calls told in this
  bullet were built from copies of the sources that differ from this repository's; neither from this
  repository's. Every call told on this page was made with builds of both programs, and on files,
  that differ from this repository's in what is hashed or admitted, in four places. In this
  repository a proof's first hash call also takes the request file's own bytes; a proof file's
  shared and second chains have labels of their own; a plan with proof of work at a seal (a round of
  the kind `sealed`; the format's rule R5.3) is refused; and the string whose hash is the commitment
  ID also holds the OOD seeds and a closing list, empty in this format. This repository's
  `cp_verify` differs from those builds in a fifth, in which this program does not follow it: what
  it admits of a parameter file (point 16), with the names and one printed line of point 20. `main`
  runs a second writing of four checks (point 24), which those builds did not. By the rules' text no
  commitment ID and no proof file of those runs passes this repository's programs, and none made by
  these passes those builds (read; tested at the stored examples alone: the next item). Of a key
  file or a copy's file by itself that does not hold: none of the four places touches what a key's
  or an entry's chains hash, so by the Lean text `verify -key` and `verify -leaf`, which need no ID,
  pass such a file alike (a plan with proof of work at a seal apart), and a whole call refuses it
  under the other ID (read: by the difference of the Lean files alone, not of the C++ sources; no
  such call is told here). Of the Lean files that the build of the next item imports, some differ
  from this repository's in code, and this repository's program imports more (compared by program,
  by the import lines). The C++ sources differ in code as well. **So every "tested" on this page
  that rests on such calls is about those builds, not about builds of this repository's sources.**
- *The build nearest to this repository's sources ("These sources").* A build of `verify-on-bytes`
  was run beside a `cp_verify` that is not a build of this repository's C++ sources. Both were built
  from copies of the sources that differ from this repository's; neither from this repository's. The
  builds were made with Lean 4.29.1 whose `leanc`, where it was looked at, calls GCC 15.3.0 in the
  place of the clang 19.1.2 that Lean's own release brings ([CHECKING.md](../CHECKING.md), "Before
  you start", "Which C compiler."); with Lean's own compiler, or with another, expect other bytes
  (inferred: not tried). All files are on made-up weights; the expected results were written down
  before each run, and all are reported to have come as expected (tested).

  At the three stored examples (`examples/accepted-proof`, `examples/accepted-proof-clipped-gap`,
  `examples/full-size`): 12 pairs of whole calls. Both programs passed three (`YES` at the first and
  the third, `WITHIN LIMITS` at the second with its `-policy`) and refused nine, each under the same
  name in both: the second example without `-policy` (`NO: policy`); an example under another
  example's commitment ID, once small and once at full size (`NO: model-statement`); and one bit
  turned in the key file, the copy's file or the proof file, small and at full size. The last lines
  were the same in all 12. The seven small pairs were made twice, the five at full size once;
  nothing was written to standard error in any of these calls.

  At full size, on a busy machine, one call each: the honest call took this program 120.8 s and
  5,192,596 kB of memory, `cp_verify` 25.0 s and 3,439,608 kB; the call with one bit of the key file
  turned took this program 309.6 s, `cp_verify` 22.3 s (point 18). Across the four places of the
  item above: a build that hashes the other strings refused the stored small and full-size examples,
  and this pair refused a small and a full-size example made for such a build, each as `NO:
  model-statement`. Eight honest small calls of this program were timed (point 24). **Not run on
  that build either, as far as we know:** false proofs from cheating provers or committers; the
  calls of point 11; anything at full size beyond these ten calls and the calls across the four
  places; any file on real weights; a stack below 10,240 kB, the limit in the two runs that show one
  (the timed small calls; the run at full size), so not 8,192 kB, a common default.
- *The stored examples.* The three stored examples have synthetic weights, by their own pages; the
  full-size one's page says that a few constants in its `config/` go back to work on real models.
- *The largest series.* One pair of builds was put side by side on the 2,377 calls of point 11, each
  call once, with made-up weights. In no call did one program alone accept or pass. No soundness
  theorem reaches any of these calls, no theorem bounds the chance that the program
  accepts a false file (`THEOREMS.md`), and the two programs are not independent (point 3).

- *The records.* The lists of calls, their labels and the runs' records are not part of this
  repository.
- *The files.* Small examples: `target_small_f2_roomy` and `target_small_f2_gap` (64 tokens, 8
  layers) and `target_small_file_f2` (256 tokens). Full size: the 400B model's shapes, 1,024 tokens.
- *What was compared.* In none of these calls did only one of the two programs pass; for calls in
  hostile environments, see point 21, for one call beside a key file above this program's limit on
  length, point 18. What was compared is the exit code and the last line of standard output.
  Standard error was not compared.

| input | calls | result in both programs |
|---|---|---|
| the 87 altered copies of a small accepted proof that this repository's script `examples/rejected-proofs/try_altered_copies.py` makes from its two tables (10 and 77) (not on builds of this repository's sources) | 87 | each program by itself (this program through a wrapper that does not ship): neither accepted any. The tables are the expected results. `cp_verify` rejected all 87 under the names that they expect; this program rejected 86 under those names and one under another: a word of the proof written as the field's modulus, which encodes no element, is `chain-refused` there and `proof-refused` here, with exit code 1 in both. That word stands at byte 204 of the proof. Each call once |
| proofs reported to be made on real weights at full size, under a parameter file of the set's own that is reported to have the default setting's protocol lines (OOD answers, counted proof of work) and whose other lines were not looked at, with a clipped-gap policy whose limits lie in that file: three requests of one batch, each covering its whole reply, and eight altered inputs built from the first request | 11 | one run: both passed the three (`WITHIN LIMITS`, under the limits in the set's own parameter file) and rejected the eight, each under the same name in both: `proof-refused` 5 (one bit of the proof; token 0 of the request; the first covered token of the request; the range's start lowered by one; another request's proof), `statement-range` (the answer token), `key-refused` (one bit of the key file), `model-statement` (the last digit of the commitment ID). Only exit code, the start of the last line or the name after `NO:`, and an empty standard error were compared, so not the figures behind `WITHIN LIMITS:`. `WITHIN LIMITS` is not `YES`: it says that the checked tokens' costs meet the policy's limits, not that a token is the model's first choice. The commitment ID, the key, the configuration and the policy's limits came with the files, so a pass says only that a proof fits the ID and the limits beside it. One set, one run, each call once. No honest reply outside the limits, no altered policy, no proof under an exact match and no false proof from a cheating prover or committer was among them: the rejected files are damaged or swapped honest ones. This program follows `cp_verify`, so that the two agree is one witness, not two (point 3) |

**Do the checks ever say yes?** No build-time test has `Key.check` or `Entry.check` accept a file of
a small example: such files have megabytes. At the default setting Lean's interpreter, on one honest
small set, said yes of `Key.check` and `Entry.check` (tested: one run, by a function that is not in
this repository; on a copy of the Lean files that differs from this repository's, not on this
repository's; one set; no altered file beside it). The run does not ask whether `main` returns 0 or
3, from which the theorems on calls start. This is an evaluation by Lean's interpreter, and no
theorem: Lean's kernel checks none of it, and the compiled program is not involved. A `yes` is no
verification of a model: no commitment ID is compared, the call's bits are not accounted for, and no
proof file is read. It shows nothing on false files, and nothing on soundness.

## Model settings

Each row is one change to the public files of a small example of `target_small_f2`'s shapes, not at
the default setting, with the best possible result for an honest proof (read, in copies of the
sources that differ from this repository's; not in this repository's). Whether the results hold of
the like change at the default setting, or for this repository's sources, was not examined. Three
rows have been tested with a proof: the third and the eighth on `target_small_file_f2`, whose
parameter file has `ll` 1, `KF` 32 and `MF` 46, and the eleventh in one honest set of files. That
example and the full-size one also have `G` 8, and the full-size one `NHf` 4 and `lmhf` 16: other
values than the rows' (all this by the parameter files; see point 9).

| lines changed | effect | best result |
|---|---|---|
| `hq`, `hv`, `ho`, `hgD`, `huD`, `hdD`, `hr` all 0 | no rounding step has high remainder digits | `YES` |
| the same lines all 2 | every rounding step has two bytes of high remainder digits | `YES` |
| `ll` 2 to 1 | one sub-proof covers two layers instead of four. Tested on another example that has this setting (`target_small_file_f2`, 256 tokens): all 41 calls on it ended alike in both programs: 32 passed, four requests on each of 8 commitments (by the list's own labels, 8 calls on honest files and 24 on "another well-formed matrix"; which is reported to be an embedding with wider entries than stated; see "What the key states about the embedding"), and 9 on altered files were rejected | `YES` |
| `V` 512 to 510 | the vocabulary does not fill its last storage block | `YES` |
| `NHf` 1 to 2, `lmhf` 14 to 13 | the output layer's largest table is committed in two halves | `YES` |
| `callH`: six lines to five | four groups of output-layer values share one lookup | `YES` |
| `sh` 8 to 7, `sT` 4 to 3 | the policy's unit is halved; the policy is then not exact match | `WITHIN LIMITS`, if the caller states the policy |
| `KF` 30 to 32, `MF` 44 to 46 | the last normalization's final shift is at its maximum | `YES` |
| `NAs` 1 to 2, `lmS` 11 to 9 | the attention matrix is committed in two parts | `YES` |
| `callA`: four lines to seven | each kind of value that attention looks up has its own lookup | `YES` |
| `G` 2 to 4 | four key/value heads instead of two | `YES` |
| `nmin` 20 to 16 | smaller lookup calls, so that calls differ in size and in their number of product trees | `YES` |
| `callA`: seven lines, `KFM` first | as with seven lines, but the first lookup call has a padding key other than 0 | `YES` |
| `NAs` 1 to 7 | the attention matrix is committed in seven parts, which its cells do not fill | `YES` |
| `lt` 6 to 7 | 128 tokens instead of 64, so a position has an odd number of bits | `YES` |
| `KL.bin`: the attention shift of all layers 12 to 5 | all layers scale their attention scores differently from every example | `YES` |
| `lmS` 11 to 5 | a part of the attention matrix has 32 rows instead of 2,048 | `YES` |
| `KL.bin`: the shifts of queries and keys 29 to 15, of values 17 to 14 | a factor in the query, key and value checks that has been 1 in every proof becomes 2 and 4 | `YES` |
| `eps2_lo`, `epsF_lo`, `huD`, `NAd`, `lmad`, the order of the `call` lines, two scales | numbers that are equal in every example are made to differ, which exercises terms that no proof at the examples tells apart | `YES` |
| `xl` removed | residual values are stored in four bytes instead of five | `NOT-A-VERIFICATION` |
| `gcl` removed | the gate's input is not clamped | `NOT-A-VERIFICATION` |
| `rcl` removed | the router's scores are not clamped | `NOT-A-VERIFICATION` |
| `KL.bin`: two attention shifts in one group of layers | two layers of a group scale their scores differently | `NOT-A-VERIFICATION` |
| `prof` 20 to 19 | attention is not proved (for tests only) | `NOT-A-VERIFICATION`; `NOT CHECKED` here (point 19) |

A parameter file without the attention proofs, or a model without routed experts, cannot pass (point
19; read, untested). Two settings are not excluded by the standard conditions. `lidb` below n
(several trees per call in the range check) can pass; in the small example that setting is reached
by removing the line `lidb`, since a written 22 is rejected. `sec` and `tau` both 160 (two blocks
and two pieces per call) might: `tau` alone is rejected, other lines must be adapted to the higher
target, and whether such a file can pass in the small example is not settled. No call told on this
page covers them. The full-size example takes neither branch.
