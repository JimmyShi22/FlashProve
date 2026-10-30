-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/AllCompiledSmall.lean: runs the checks of the key file, the entry file and the proof file of the
small stored example in a row, with the tests that join them to one commitment ID, and prints the
result of every test.

No soundness: a test. A yes of this run is not a verification: see "It does not mean:" below.

This file only starts the run: the code is in Johnson/RunOne/AskAll.lean, over
Johnson/RunOne/AskKey.lean, Johnson/RunOne/AskProof.lean and OnBytes/ShellOf/EntryJoin.lean. What
"the compiled verifier" is, and what all files of this directory share: Ask/README.md.

Reads: From the user, who makes the claim: examples/accepted-proof/config/policy.txt,
  examples/accepted-proof/config/layout.txt, examples/accepted-proof/config/KL.bin (the public
  parameter files), examples/accepted-proof/ID.txt (the commitment ID),
  examples/accepted-proof/example.req (the request) and examples/accepted-proof/example.y (the
  reply). From the prover: key.parsed.bin, leaf-0.parsed.bin and proof.parsed.bin, the three parsed
  files, which tools/parser/ writes from examples/accepted-proof/ivk/key.bin,
  examples/accepted-proof/ivk/leaf/0.bin (the entry file) and examples/accepted-proof/example.proof;
  and examples/accepted-proof/ivk/leaf/0.bin itself.
  Environment variables: ASK_PARSED_KEY, ASK_PARSED_LEAF, ASK_PARSED_PROOF: the paths of the three
  parsed files; all three must be set. ASK_EXAMPLE: another example's directory instead of
  ../examples/accepted-proof. ASK_K is not read: each check is run at what its rounds need.
Command: LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 Ask/AllCompiledSmall.lean
  or, faster:
  LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --load-dynlib=./libvob.so --tstack=4000000 \
    Ask/AllCompiledSmall.lean
  (typed in lean/; Ask/README.md lists the steps that come before, and says what libvob.so is)
Takes: on a machine of 32 cores and 128 GiB that was also running other work: with libvob.so, 13 and
  16 minutes in two runs, and 10 GB. Plain: not measured to its end; it runs the checks that
  Ask/KeyCompiledSmall.lean and Ask/ProofCompiledSmall.lean run (their comments give their times),
  and the entry file's check. One thread does the work.
Its print means: The lines below go to the error stream. The number in brackets at the end of most
  lines is the time in milliseconds since the line before. An error that ends the run goes to
  standard output, as a Lean error at the line of #eval. Some lines say "leaf file": that is the
  entry file.
  read: the example's directory; the three parsed files' paths and sizes. "=== THE FILES UNCHANGED"
    heads the lines that a control repeats.
  verifier run, theorems cited: the definition that is run (`verifyAllAskRun`,
    Johnson/RunOne/AskAll.lean), test by test, up to the first NO, and three theorems
    (Johnson/RunOne/AskAllLaws.lean, Johnson/RunOne/AskKeyLaws.lean), which the run cites and does
    not check: `verifyAllAskRun_eq`, `upToNo_all`, `verifyAllAskSmall_parts`: what these tests
    answer together, as plain data, is the value of the one term `verifyAllAskSmall`; that the run
    with its print returns the same: see (19).
  read 1 to 5: the three parsed files can be read; the two readers of the parsed key file give one
    table, and so do the two readers of the parsed proof file.
  join 2, join 3: the first table in the parsed entry file is the parsed key file's table; the
    further table in the parsed entry file is the table that the parsed proof file names.
  key, entry, proof: the three checks, each one evaluation, during which nothing is printed: the key
    file's check (the answer of Ask/KeyCompiledSmall.lean; where that run ends with an error, NO),
    with join 1: the commitment ID computed from its table is the user's; the entry file's check
    from the first table to the further table, under the user's commitment ID; the proof file's
    check (the answer of Ask/ProofCompiledSmall.lean). Their own steps are not printed here. A NO at
    "key" can come from any test of that check, not from join 1 alone (at an example with another
    acceptance policy: from its test of the policy): Ask/KeyCompiledSmall.lean prints which.
  ANSWER: yes only if all ten tests say yes. After the first NO no further test is run. After a yes
    comes a line that begins "THIS YES IS NOT A VERIFICATION".
  lean ends with status 0 only after a yes. After a NO the error is "the unchanged files did not get
    a yes". Two failures end the run with an error and no ANSWER: one of the three variables is not
    set; a file is missing (Lean's own words).
It does not mean: A yes is not a verification of the reply.
  (1) All that Ask/KeyCompiledSmall.lean and Ask/ProofCompiledSmall.lean do not mean holds of the
    two checks here, but for their points on what is not tied to a commitment ID.
  (2) The number of the stored copy in the parsed proof file is held against the number in the entry
    file's name by nothing.
  (3) The original entry file, of which the proof file's check makes its record, is held to the
    parsed entry file through the proof file's table alone.
  (4) "join 2" compares the parsed entry file's own copy of the first table, at which no check is
    run: the entry file's check takes its first table out of the parsed key file, by its own reader,
    and what links that table to the one at which the key file's check is run is "read 4".
  (5) The ten tests link the tables' names (root and answers). The seeds of a table's record are
    drawn at least three times, by each check for itself; no test here compares what they are drawn
    from; all of it is made of the user's three public parameter files and the library.
  (6) The test "entry" (`yesSmallP`, OnBytes/ShellOf/EntryJoin.lean) is the library's closed check
    of the link from the first table to the further one (`verifyEntrySmall`), and the comparison of
    the user's commitment ID with the word that the hash gives of the public files and the first
    table, behind the standard test of the public files and the reader. The check is three things:
    tests on the parsed value (`askedFit`); a comparison of both tables' seeds, written by hand; and
    the lax verifier of the link out of the library's second compiler. It takes the link chain's run
    value as the parsed entry file gives it. It reads neither the request, the reply nor the
    original entry file.
  (7) Of the closed check alone a bound is proved (`verifyEntrySmall_copyBound`,
    OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean): over a uniformly random function, not the format's
    hash, for one maker, with the public files fixed before the function is drawn; of an event on
    the maker's own log, not of "a yes on a false statement"; it is not combined into one bound with
    the key file's and the proof file's parts (no theorem joins them), and the commitment ID's
    comparison is in no bound. Without the key file's part nothing follows from it. A "true" of this
    test gives the closed check's yes by a theorem, one way (`yesSmallP_true`). No theorem ties this
    test to a program.
  (8) The closed check does not trust its reader of the parsed entry file at all, no more than the
    parser; the two joins lean on one law that says which bytes became the value's two tables
    (`parseP_tables`). That a word is below the field's prime, a salt's length and rows beyond those
    that are read are tested only as far as `askedFit` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean)
    asks; the width of a stored table's column is tested by nothing here. More: the comments of
    OnBytes/ShellOf/EntryJoin.lean and OnBytes/ShellOf/EntryParsed.lean.
  (9) The library does not prove the soundness of the key file's or the proof file's protocol. Its
    theorem on innerCompiledVerifier takes named hypotheses in its place, `keySound` and `proofSound`, on the
    protocols' rounds (`keySound`: the key file's protocol is round-by-round sound; `proofSound`:
    for each record the proof file's protocol has round-by-round knowledge soundness, in the form
    for batches, for the relaxed relation at the decoded index; each with every round's error at
    most a stated bound: `CompilerSoundnessConditionStatements.keySound`, `CompilerSoundnessConditionStatements.proofSound`, Johnson/Top/InnerCompiledVerifier.lean). The
    example has the smaller of the two sizes for which the library writes out its theorem on
    innerCompiledVerifier (`innerCompiledVerifierSoundFromDryRunAtSmallSize`, Johnson/Flat/TwoSizes.lean). That file's own comment says that the
    example's protocol cannot meet `proofSound` at the claim written for that size (`claimsSmall`);
    this is by reading, no theorem. If it is right, that theorem says nothing of this example. No
    theorem derives a bound on the error of the checks that are run here from `keySound` or
    `proofSound` alone.
  (10) The protocols' own checks are written by hand after the C++ verifier. The compiler does not
    make them.
  (11) Lean evaluates this code. Its kernel, which checks the library's proofs, checks nothing of
    the run.
  (12) It is one run on one stored example, of a small synthetic model
    (examples/accepted-proof/README.md).
  (13) It judges under exact match alone. At an example with another acceptance policy the answer is
    NO, whatever the files hold.
  (14) A yes is about the parsed files. Nothing here compares the parsed key file or the parsed
    proof file with the file itself, and the parsed entry file is held to the entry file only as (3)
    says: whatever the parser writes counts as sent by the prover.
  (15) The run values of the first and third chains of the key file and of the proof file are taken
    as the parsed files give them; so is the link chain's ((6)).
  (16) No theorem links this yes to the verifier of the library's theorem on innerCompiledVerifier. Why:
    Ask/KeyCompiledSmall.lean (8), Ask/ProofCompiledSmall.lean (10).
  (17) The run does not ask how many bits of security the public parameter files give: it makes no
    accounting of their rounds and queries, so files with too few of them are not refused on that
    ground. That accounting is written in the text of verify-on-bytes
    (OnBytes/Model/VerifyAccount.lean).
  (18) Where a printed line of the two single files says that an oracle query "has a hash call in
    the format", what is tested is that the coding of oracle queries into hash calls (`okJ`,
    OnBytes/Maker/Page/Guard.lean) writes a string for that query: at a chain's query for every
    block of the answer, but at a chain's first call for the last block alone. Of two kinds of query
    no string is looked at: one kind is always refused, the other always let pass. That the call
    lies in the format's own domain, or that the query fits, is not tested.
  (19) No theorem says that the run with its print returns what `verifyAllAskSmall`
    (Johnson/RunOne/AskAll.lean) returns: that rests on a reading of the two texts.
  (20) The theorem from a yes (`verifyAllAskSmall_yes`, Johnson/RunOne/AskAllYes.lean) does not
    carry join 2: nothing in it speaks of the parsed entry file's own first table:
    `verifyAllAskSmall_join2` (Johnson/RunOne/AskAllCopy.lean) does.
  (21) This is not the verifier program that ships (cp_verify, C++) nor verify-on-bytes' text, nor
    part of either. Neither is proved sound: no stand-alone verifier program is (lean/README.md).
-/
import Johnson.RunOne.AskAllLaws

set_option stderrAsMessages false

#eval Johnson.RunOne.Ask.All.runAll []
