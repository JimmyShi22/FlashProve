-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/KeyCompiledSmall.lean: runs the compiled verifier of the key file's protocol on the key file of
the small stored example, and prints the result of every test.

No soundness: a test. A yes of this run is not a verification: see "It does not mean:" below.

This file only starts the run: the code is in Johnson/RunOne/AskKey.lean and
Johnson/RunOne/AskShell.lean. What "the compiled verifier" is, and what all files of this directory
share: Ask/README.md.

Reads: From the user, who makes the claim: examples/accepted-proof/config/policy.txt,
  examples/accepted-proof/config/layout.txt, examples/accepted-proof/config/KL.bin (the public
  parameter files) and examples/accepted-proof/ID.txt (the commitment ID). From the prover:
  key.parsed.bin, the parsed key file, which tools/parser/ writes from
  examples/accepted-proof/ivk/key.bin.
  Environment variables: ASK_PARSED: the path of key.parsed.bin; it must be set. ASK_EXAMPLE:
  another example's directory instead of ../examples/accepted-proof. ASK_K: see Ask/README.md.
Command: LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 Ask/KeyCompiledSmall.lean
  or, faster:
  LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --load-dynlib=./libvob.so --tstack=4000000 \
    Ask/KeyCompiledSmall.lean
  (typed in lean/; Ask/README.md lists the steps that come before, and says what libvob.so is)
Takes: on a machine of 32 cores and 128 GiB that was also running other work: plain, about 10
  minutes and 6 GB; with libvob.so, about 3 minutes and 6 GB. One thread does the work.
Its print means: The lines below go to the error stream. The number in brackets at the end of most
  lines is the time in milliseconds since the line before. An error that ends the run goes to
  standard output, as a Lean error at the line of #eval.
  read, plan, parsed file, numbers, to be read: what was read and made, with its sizes. "=== THE
    FILE UNCHANGED" heads the lines that a control repeats.
  plan 0: printed once, after "read"; it can only say yes (see the four failures below). plan 1 to
    7, claim 1 to 6, guard: the tests before the verifier, in order, up to the first NO: on the plan
    that Lean makes from the public parameter files ("plan 5": the acceptance policy is exact match;
    "plan 6": ASK_K is large enough); on what the parsed key file gives ("claim 3": the table's
    commitment ID, computed from the table, is the user's; "claim 5": the shared chain's run value,
    computed from the binding root, is the parsed file's); on the length and the end of one salt.
    After a NO here the verifier is not run: only THE FIRST NO and ANSWER follow.
  verifier run, theorem cited: what is run (the steps of `verifyWholeL`,
    OnBytes/Maker/ListedWhole.lean, one by one), and two theorems of Johnson/RunOne/AskKeyLaws.lean,
    which the run cites and does not check: `verifyKeyAskRun_eq`: the answer as plain data
    (`verifyKeyAskRun`) is the value of the term `verifyKeyAskSmall`; that the run with its print
    returns the same: see (14); `keyAnswer_eq`: "guard", "written" and "verdict" together are
    `verifyGuard` (OnBytes/Maker/Page/GuardVerify.lean), the guarded verdict of `verifyOneProtocol` at this
    very proof. The line behind them says that no term is called beside the steps.
  chain (three lines): the hash chain ran to its end; how many oracle queries it asked, by oracle;
    each had a hash call in the format. The two lines "behind the chain", printed after parts 1 and
    2, say the same of the queries that come after it.
  strict, forests, after, accept: 23 named tests (OnBytes/Maker/ListedSteps.lean), which show where
    a NO comes from.
  decides the verdict, part 1 and part 2: see "verdict". The next line says whether the 23 named
    tests together say what these two say. Where part 1 says NO, part 2 is not run, and the two
    lines "behind the chain" are not printed.
  THE FIRST NO (printed between the two lines "written"): the first named test that said NO, or
    "none". ("after 5" is the nine tests "accept" together: it is named only if none of these says
    NO.)
  written (twice), verdict, both together: "written": every oracle query that was asked has its hash
    call in the format. The second line "written (...)" repeats it and adds "verdict": the chain ran
    to its end, and parts 1 and 2 say yes. "both together" says "no value" where "written" is NO.
  verifier: "guard", "written" and "verdict" together: the guarded verdict of the compiled verifier
    at the proof in the parsed key file. Guarded: if an oracle query that the run asks has no hash
    call in the file format, the run has no value, and the verdict is NO.
  ANSWER: yes only if every test before the verifier, "written" and "verdict" say yes. After a yes
    comes a line that begins "THIS YES IS NOT A VERIFICATION".
  IT STOPPED BEFORE AN ANSWER: the table's record could not be made, or the parsed key file does not
    have the form of a proof of this protocol.
  lean ends with status 0 only after a yes. After a NO or a stop the error is "the unchanged file
    did not get a yes". Besides a stop, four failures end the run with an error and no ANSWER:
    ASK_PARSED is not set; a file is missing (Lean's own words); no plan can be made; the parsed
    file cannot be decoded.
It does not mean: A yes is not a verification of the key file.
  (1) The library does not prove the soundness of the protocol that is run. Its theorem on innerCompiledVerifier
    at the small size (`innerCompiledVerifierSoundFromDryRunAtSmallSize`, Johnson/Flat/TwoSizes.lean) takes it as a hypothesis:
    `keySound` of `RemainingSoundnessConditionsFromDryRunAtSmallSize` (`keySound` says that the key file's protocol is round-by-round
    sound, with every round's error at most a stated bound: `CompilerSoundnessConditionStatements.keySound`,
    Johnson/Top/InnerCompiledVerifier.lean). `keySound` is unproved at both sizes (at `theDescription`, at
    the full size, a theorem, on conditions, with limits); unlike `proofSound`, the comments do not
    say that the small example's protocol can meet it or cannot. Johnson/Flat/TwoSizes.lean sets
    the depth of the key file's request tree by its own choice and does not say the programs'.
  (2) The protocol's own checks (the test "accept 9") are written by hand after the C++ verifier.
    The compiler did not make them.
  (3) Lean evaluates this code. Its kernel, which checks the library's proofs, checks nothing of the
    run.
  (4) It is one run on one stored example, of a small synthetic model
    (examples/accepted-proof/README.md).
  (5) A yes is about the parsed key file. Nothing here compares that file with the key file itself:
    whatever the parser writes counts as sent by the prover.
  (6) The term `verifyKeyAskSmall` takes the parsed key file as decoded. Of the decoder's tests
    (`Carrier.read`, OnBytes/Maker/Carrier.lean) it repeats five lengths ("claim 2"); the others
    (words below the field's prime, rising numbers, the digests in paths) are the decoder's alone,
    which this run calls first and of which no theorem here speaks.
  (7) It judges under exact match alone. At an example with another acceptance policy the answer is
    NO, whatever the files hold. It says nothing of an entry file, a proof file, a request or a
    reply.
  (8) No theorem links this yes to the verifier of the theorem on innerCompiledVerifier: the run stands
    at oracle types of its own, which hold only what the verifier reads
    (Johnson/RunOne/Hollow.lean), and at its own coding of oracle queries into hash calls; no
    equation ties these to the terms of which `keySound` speaks.
  (9) The run draws the seeds of the table's record itself. It does not ask the oracle queries that
    test them.
  (10) The format hashes in two modes: standard BLAKE2b, and a second mode built on BLAKE2b's
    compression function. Only the first is an argument here. The second is a fixed public function
    inside the definitions. It digests public data. Other pages call it the second hash function: on
    the public files it is a fixed function here, never an oracle. More on it: Ask/README.md.
  (11) The run values of the key file's first and third chains are taken as the parsed key file
    gives them: in the format each is a hash of that chain's parameter digest together with 32
    random bytes of the key file, and the parsed file does not hold those bytes.
  (12) The run does not ask how many bits of security the public parameter files give: it makes no
    accounting of their rounds and queries, so files with too few of them are not refused on that
    ground. That accounting is written in the text of verify-on-bytes
    (OnBytes/Model/VerifyAccount.lean). Nor does the run make three more tests of that text's stage
    for the key file (`keyStage`, OnBytes/Model/VerifyStages.lean): that the parameter file's
    profile is 4, the conditions of the standard parameter form (`Common.oneTimeForm`), and the test
    on the work held.
  (13) Where a printed line says that an oracle query "has a hash call in the format", what is
    tested is that the coding of oracle queries into hash calls (`okJ`,
    OnBytes/Maker/Page/Guard.lean) writes a string for that query: at a chain's query for every
    block of the answer, but at a chain's first call for the last block alone. Of two kinds of query
    no string is looked at: one kind is always refused, the other always let pass. That the call
    lies in the format's own domain, or that the query fits, is not tested. That the string holds
    all that the query holds, and that it is the string that the programs hash, is not shown.
  (14) No theorem says that the run with its print returns what `keyParts`
    (Johnson/RunOne/AskKey.lean) returns: that rests on a reading of the two texts.
  (15) This check runs alone here. Ask/AllCompiledSmall.lean runs this check with the two others,
    and with the tests that join them to one commitment ID.
  (16) This is not the verifier program that ships (cp_verify, C++) nor verify-on-bytes' text, nor
    part of either. Neither is proved sound: no stand-alone verifier program is (lean/README.md).
  (17) The third clause of "plan 4" compares two copies of the digest of the public files inside the
    plan, both made from the files that were read. It holds them against no fixed digest: with a
    changed public file that the planner accepts, that clause still says yes. The test that ties the
    public files to the user's commitment ID is "claim 3".
-/
import Johnson.RunOne.AskKeyLaws

set_option stderrAsMessages false

#eval Johnson.RunOne.Ask.Key.run []
