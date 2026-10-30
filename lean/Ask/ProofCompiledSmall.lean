-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/ProofCompiledSmall.lean: runs the compiled verifier of the proof file's protocol on the proof
file of the small stored example, and prints the result of every test.

No soundness: a test. A yes of this run is not a verification: see "It does not mean:" below.

This file only starts the run: the code is in Johnson/RunOne/AskProof.lean and
Johnson/RunOne/AskShell.lean. What "the compiled verifier" is, and what all files of this directory
share: Ask/README.md.

Reads: From the user, who makes the claim: examples/accepted-proof/config/policy.txt,
  examples/accepted-proof/config/layout.txt, examples/accepted-proof/config/KL.bin (the public
  parameter files), examples/accepted-proof/example.req (the request) and
  examples/accepted-proof/example.y (the reply). From the prover:
  examples/accepted-proof/ivk/leaf/0.bin (the entry file: only its table's root and stored answers
  are read, and nothing here tests them) and proof.parsed.bin, the parsed proof file, which
  tools/parser/ writes from examples/accepted-proof/example.proof. The commitment ID and the key
  file are not read: see (1).
  Environment variables: ASK_PARSED: the path of proof.parsed.bin; it must be set. ASK_EXAMPLE:
  another example's directory instead of ../examples/accepted-proof. ASK_K: see Ask/README.md.
Command: LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 Ask/ProofCompiledSmall.lean
  or, faster:
  LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --load-dynlib=./libvob.so --tstack=4000000 \
    Ask/ProofCompiledSmall.lean
  (typed in lean/; Ask/README.md lists the steps that come before, and says what libvob.so is)
Takes: on a machine of 32 cores and 128 GiB that was also running other work: plain, about 48
  minutes and 10 GB; with libvob.so, about 7 minutes and 10 GB. One thread does the work.
Its print means: The lines below go to the error stream. The number in brackets at the end of most
  lines is the time in milliseconds since the line before. An error that ends the run goes to
  standard output, as a Lean error at the line of #eval.
  read, numbers, parsed file: what was read and made, with its sizes; or, at "parsed file", that it
    cannot be decoded: then the ANSWER is NO. "=== THE FILE UNCHANGED" heads the lines that a
    control repeats.
  verifier run, theorem cited (right after "read"): the definition that gives the answer
    (`verifyProofAskSmall`, Johnson/RunOne/AskProof.lean), and theorems of that file, which the run
    cites and does not check: `answer_is`, `answer_no`: the answer of the run as plain data is the
    value of that one term; that the run with its print returns the same: see (17);
    `verifyProofSmall_is`: its last part is `verifyGuard` (OnBytes/Maker/Page/GuardVerify.lean), the
    guarded verdict of `verifyOneProtocol` at the proof in the parsed proof file.
  ground, parsed file 1 to 5: six tests before the verifier: the plan, the table's record and the
    claim can be made from the files; the parsed proof file names the table that the entry file
    names, and stored copy 0; the shared chain's run value, computed from the binding root, is the
    parsed file's; none of the three run values is 32 zero bytes; its root, its three run values and
    the binding root have 32 bytes each. A NO at "ground" comes right after "theorem cited" and
    gives its reason, and only "ANSWER: NO" follows; an acceptance policy other than exact match is
    one such reason. "parsed file 1" to "5" are all printed, whatever the earlier ones say.
  the verifier has run: this line carries the verifier's time. It is one evaluation: until it ends
    nothing is printed.
  proof form, guard, hash calls, run (indented): the four steps of the last part: the parsed proof
    file has the form of a proof of this protocol; one salt has its length and end; every oracle
    query of the run has a hash call in the format; the guarded run of the verifier. Each of the
    four is printed only after a yes at the one before.
  verifier: the guarded verdict of the compiled verifier: yes only if these four say yes; "not
    asked" where one of "parsed file 1" to "5" said NO. Guarded: if an oracle query that the run
    asks has no hash call in the file format, the run has no value, and the verdict is NO.
  ANSWER: yes only if all seven parts (the six tests and "verifier") say yes. After a yes come two
    lines: one begins "THIS YES IS NOT A VERIFICATION"; the other says that the table is not tied to
    your commitment ID here.
  lean ends with status 0 only after a yes. After a NO the error is "the answer is NO". Two failures
    end the run with an error and no ANSWER: ASK_PARSED is not set; a file is missing (Lean's own
    words).
It does not mean: A yes is not a verification of the reply.
  (1) The table under this proof is the prover's word: not tied to your commitment ID here. This run
    reads no commitment ID and no key file, and it takes the entry file as given.
  (2) Nothing here ties the table to a commitment ID. The table's name comes from the entry file,
    which the prover sends. The checks of the key file and of the entry file make that tie, and they
    are not run here.
  (3) The library does not prove the soundness of the protocol that is run, and at the small size
    its theorem does not assume it either: that theorem (`innerCompiledVerifierSoundFromDryRunAtSmallSize`,
    Johnson/Flat/TwoSizes.lean) takes a hypothesis, `proofSound` of `RemainingSoundnessConditionsFromDryRunAtSmallSize`, which by that
    file's own words the small example's protocol cannot meet at the claim the library writes for
    that size (`claimsSmall`: its program holds the library's five fixed tables, not those of the
    example's parameter file). By reading; no theorem. If that reading is right, the theorem says
    nothing of this run. (`proofSound` says that for each record the proof file's protocol has
    round-by-round knowledge soundness, in the form for batches, for the relaxed relation at the
    decoded index, with every round's error at most a stated bound: `CompilerSoundnessConditionStatements.proofSound`,
    Johnson/Top/InnerCompiledVerifier.lean.)
  (4) The protocol's own checks were written by hand after the C++ verifier. The compiler did not
    make them.
  (5) Lean evaluates this code. Its kernel, which checks the library's proofs, checks nothing of the
    run.
  (6) It is one run on one stored example, of a small synthetic model
    (examples/accepted-proof/README.md).
  (7) It judges under exact match alone. At an example with another acceptance policy the answer is
    NO, whatever the files hold.
  (8) A yes is about the parsed proof file. Nothing here compares that file with the proof file
    itself: whatever the parser writes counts as sent by the prover.
  (9) The term `verifyProofAskSmall` takes the parsed proof file as decoded. Of the decoder's tests
    (`Carrier.read`, OnBytes/Maker/Carrier.lean) it repeats five lengths ("parsed file 5"); the
    others (words below the field's prime, rising numbers, the digests in rounds and paths) are the
    decoder's alone, which this run calls first and of which no theorem here speaks.
  (10) No theorem links this yes to the verifier of the library's theorem on innerCompiledVerifier: the run
    stands at oracle types of its own, which hold only what the verifier reads
    (Johnson/RunOne/Hollow.lean), and at its own coding of oracle queries into hash calls; no
    equation ties these to the terms of which `proofSound` speaks.
  (11) The format hashes in two modes: standard BLAKE2b, and a second mode built on BLAKE2b's
    compression function. Only the first is an argument here. The second is a fixed public function
    inside the definitions. It digests public data and the request file. Other pages call it the
    second hash function: on the request file and on the public files it is a fixed function here,
    never an oracle. More on it: Ask/README.md.
  (12) The run draws the seeds of the table's record itself. It does not ask the oracle queries that
    test them.
  (13) A parsed file that is changed at a field which nothing reads gets the same answer.
  (14) The run values of the proof file's first and third chains are taken as the parsed proof file
    gives them: in the format each is a hash of that chain's parameter digest together with 32
    random bytes of the proof file, and the parsed file does not hold those bytes.
  (15) The run does not ask how many bits of security the public parameter files give: it makes no
    accounting of their rounds and queries, so files with too few of them are not refused on that
    ground. That accounting is written in the text of verify-on-bytes
    (OnBytes/Model/VerifyAccount.lean). Nor does the run make four more tests that the text's stage
    "request" makes (the comment of Johnson/RunOne/ProofGround.lean): that the entry's table's shape
    is admitted; behind a yes, the test on the work held; the comparison of the request's item with
    what the sub-proofs use; the conditions of the standard parameter form.
  (16) Where a printed line says that an oracle query "has a hash call in the format", what is
    tested is that the coding of oracle queries into hash calls (`okJ`,
    OnBytes/Maker/Page/Guard.lean) writes a string for that query: at a chain's query for every
    block of the answer, but at a chain's first call for the last block alone. Of two kinds of query
    no string is looked at: one kind is always refused, the other always let pass. That the call
    lies in the format's own domain, or that the query fits, is not tested. That the string holds
    all that the query holds, and that it is the string that the programs hash, is not shown.
  (17) No theorem says that the run with its print returns what `verifyProofAskSmall`
    (Johnson/RunOne/AskProof.lean) returns: that rests on a reading of the two texts.
  (18) This check runs alone here. Ask/AllCompiledSmall.lean runs this check with the two others,
    and with the tests that join them to one commitment ID.
  (19) This is not the verifier program that ships (cp_verify, C++) nor verify-on-bytes' text, nor
    part of either. Neither is proved sound: no stand-alone verifier program is (lean/README.md).
-/
import Johnson.RunOne.AskProof

set_option stderrAsMessages false

#eval Johnson.RunOne.Ask.Proof.run [] []
