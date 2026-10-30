# FlashProve's Lean library

Terms: [TERMS.md](TERMS.md). The statements to read, with their Lean text:
[STATEMENTS.html](STATEMENTS.html).

FlashProve is meant to let a provider show that a list of output tokens is what one fixed language
model returns on a prompt, without showing its weights. This folder holds its Lean library: a
verifier written in Lean, `verify`, the protocol's honest provers as Lean definitions, the theorems
about them, and their proofs, which Lean's kernel checks.

`verify` takes three public files (parameter, layout and scale file), a commitment to a language
model's weights, a prompt, a list of output tokens and a proof, and accepts or rejects. It is
compiled in Lean, by Merkle trees and the Fiat–Shamir transformation, from an interactive oracle
proof that is itself written in Lean (`VerifierAndGoals.theDescription`).

## What is proved

In short, and what this means for the programs:

- **Soundness** is proved, in Lean, for the verifier written in Lean: it accepts a proof of a false
  claim with probability at most about 2^-124 per hash query (with a floor of about 2^-101), in the
  random-oracle model, for [exact-match](../guide/terms.md) claims; under the tolerant
  ([clipped-gap](../guide/terms.md)) policy that serving uses, Lean proves only that the reply meets
  that policy ([Known limits](../guide/known-limits.md)). The C++ verifier and the CUDA prover are
  written to follow the same protocol and are tested against it, not themselves proved.
- **[Completeness](../guide/terms.md) and [zero knowledge](../guide/weight-hiding.md)** are proved,
  in Lean, for the compiled prover and verifier, in the random-oracle model, with honest provers
  written in Lean as definitions (not programs that run), default values included: both at the
  requests that can be served and whose output tokens are the model's, and zero knowledge at every
  request up to one bit for it (served or refused), which depends on the weights. Before hashing,
  for the interactive oracle proof, Lean proves soundness and both of these too, zero knowledge
  there against an honest verifier. The three statements before hashing are about one protocol;
  completeness and zero knowledge about one triple of provers in it ([LIMITS.md](LIMITS.md), L92).

  Further theorems are about weights that pass the first worst-case check, or the least-bound check
  with numbers that hold (these are the library's own checks; neither is `cp_commit`'s worst-case
  check): at these the model has a result on every well-formed request. They cover no request that
  completeness after compiling does not already cover: that holds at all weights, for every
  well-formed request whose claimed output is the model's result. What follows from this premise on
  the weights is said of every prompt, not of every request ([LIMITS.md](LIMITS.md), L93). Made-up
  weights are shown by name to pass the first check, and at the reference settings every set of
  weights whose layers lie within one stated bound is shown to pass the first check, or the
  least-bound check with numbers that hold (`passesSomeWorstCaseCheck_atReferenceSettings`); no
  theorem says whether a real model's weights do.

  Neither completeness nor zero knowledge covers batches, coins derived from a short key or the
  simulators' running time, and neither says anything of what the public files themselves tell of
  the weights, of timing or of the released programs (the C++ verifier and committer, the CUDA
  prover). Zero knowledge holds within stated bounds on what is shown under one commitment, and for
  one commitment to the weights. The theorems, their objects and their limits:
  [LIMITS.md](LIMITS.md), L88 to L93. In the code completeness and zero knowledge are tested, not
  verified: every honest proof tried was accepted, and in honest runs we have seen nothing beyond a
  declared list.
- So, for a prototype, we have **reasonably high trust** in what the system produces: soundness,
  which matters most for a verifier, is machine-checked for the Lean verifier, and the C++ verifier
  is tested against it. We expect, rather than know, that the programs hide the weights at the
  default setting, in honest runs, if the provider keeps its duties (this does not reach any real
  model's weights, or the parameter file and scales fitted to them): by design every published value
  that depends on the weights, beyond a declared list, is masked or published only as a salted hash;
  in Lean zero knowledge is proved for the protocol, and nothing for the programs; and, with the
  protocol's conditions kept, we know of no attack, though few were sought and no test on the
  released programs hunts for a leak. Before you commit weights that must stay secret, read [Weight
  hiding](../guide/weight-hiding.md).

Where the conditions of these three bullets stand:

- **Soundness:** [THEOREM.md](THEOREM.md), "Look first at four things" (what you must check
  yourself), "In exact terms" and "What it does not say". The theorem is for exact match alone, at
  one proof format and model size and public files fixed before the hash function is sampled. Under
  a tolerant (clipped-gap) policy another theorem holds, which by itself bars nothing against a
  committer whose weights make every output meet the policy: "The theorem under a policy: other
  acceptance policies".
- **Completeness and zero knowledge:** [THEOREM.md](THEOREM.md);
  every limit, entry by entry: [LIMITS.md](LIMITS.md), L88 to L93.
- **Trust:** what has run over this repository's files: [CHECK-RESULTS.md](CHECK-RESULTS.md); the
  tests of the programs and of `verify`'s executable form: [THEOREM.md](THEOREM.md), "What has been
  run"; on hiding: [Weight hiding](../guide/weight-hiding.md), "The programs"; in which calls the
  honest proofs were accepted, and in what sense the programs are the released ones:
  [GAPS.md](GAPS.md), 14 (k) and (l). Every limit and every gap, entry by entry:
  [LIMITS.md](LIMITS.md), [GAPS.md](GAPS.md).

Exact match is the policy, set in the parameter file, under which every output token must be the
model's own choice (greedy decoding). For the six theorems and for the soundness theorem on
`verify`, Lean's kernel checks the proofs, which rest on Lean's three standard axioms alone; the
proof of the soundness theorem on `verify` rests on no conjecture on error-correcting codes; the
random oracle and a second, fixed hash function belong to that theorem's statement, not to its
proof's axioms. The coding theory beneath it is proved here from files adapted from ArkLib and
Mathlib ([LIMITS.md](LIMITS.md), L15). [THEOREM.md](THEOREM.md) tells each result with its
conditions: the statement, its assumptions, what an accept means, what it does not say, and what has
been run. Read it before you rely on an accept.

In exact terms, theorem by theorem:

- **The compiled prover and verifier, `compile (flashProve setup)`: the six theorems.** Six theorems
  (`AtFullSide/Face/TheSixLines.lean`) are about one argument system, `compile (flashProve setup)`.
  In each of them `setup` is a public setup (`PublicSetup`): three public files that are in the
  verifier's scope, that are read without error, that state the exact-match policy (under it every
  output token must be the model's own choice: greedy decoding; the verifier does not test that they
  state it), and that pass the test `protocolDataWellFormed`, which the verifier makes too (the
  protocol's data can be built from them without error, no list of rounds is empty, the data for the
  key and for the proof have the full-size depth, and the sizes lie within fixed limits). In the
  lines on soundness, binding, completeness and zero knowledge the hash function is drawn at random.
  The honest committer and prover are Lean definitions, not programs. These pages call the six
  theorems the six lines; all that goes with them: [LIMITS.md](LIMITS.md), L93.
  - Soundness, `sound`: a cheating committer and prover with q hash queries between them get the
    verifier to accept output tokens that are not the model's, at the weights that one extractor
    reads from the commitment and the committer's hash queries, with probability at most about
    q/2^124 + 2^-101. That is a bound, not a security level ([LIMITS.md](LIMITS.md), L11).
  - Soundness with binding, `soundAndBinding`: soundness and binding, with one extractor for both:
    nobody opens the commitment to weights other than that extractor's, except with probability
    about q/2^124 + 2^-100, where q counts the hash queries of whoever made the commitment and of
    the opener together.
  - Completeness, at the requests that can be served, `completeOnCanServe`: at every request that
    can be served (`CanServe`) and whose output tokens are the model's, the honest proof is rejected
    with probability at most 2^-40. Nothing is said of a request outside `CanServe`, among them
    those where the model has no result, or of an output that is not the model's: there the honest
    prover's reply is the empty proof. Which requests can be served depends on the weights.
  - Zero knowledge, at the requests that can be served, `zeroKnowledgeOnCanServe`: there is a bound
    that stays at or below 2^-154 within 2^64 hash queries and 688,127 replies, and zero knowledge
    holds within this bound on the requests that can be served and whose output tokens are the
    model's: one simulator, which may depend on the public setup and is handed nothing of the
    weights in the experiment. What the public files tell of the weights is not counted. Whether a
    request can be served depends on the weights, and that is not hidden. By itself it says nothing
    of a refused request. One request per proof and one commitment are covered, not batches. What
    else it does not cover: [LIMITS.md](LIMITS.md), L93, L83.
  - The reply at a refused request, `refusedHandsOutNoProof`: every reply that the prover can return
    at a refused request is the empty proof. A request is refused if it is ill-formed, if the model
    has no result on it, or if its result is other tokens. That a refusal is right is not covered:
    an empty proof proves nothing, and a prover can return it at a request that it could serve.
  - The replies fit, `repliesFit`: 688,127 (`finalReplyCount`) is at most `onlineRunsPerCopy setup`,
    the number of runs of the online IOP that the honest settings give one copy; the opened columns
    fit each table; and one run each of the honest sampler of commitment randomness, the honest
    committer and the honest prover make together at most 2^48 hash queries. `onlineRunsPerCopy` is
    a written number, 688,127 too: the first compares two written numbers. The second is what ties
    that number to a table: 62 + 688,127 · 64 columns are within a copy's 44,040,191. The prover
    counts no replies, so nothing in it enforces the first two.
  - Two corollaries. Completeness at every well-formed request whose claimed output is the model's
    result (`completeAtWellFormedRequests`): these are the same requests. Zero knowledge at every
    request (`zeroKnowledgeAtEveryRequest`, from `zeroKnowledgeOnCanServe` and
    `refusedHandsOutNoProof`; that it gives the former back is not proved): in the random-oracle
    model, against any verifier, for one commitment with one copy of the table, up to 688,127
    replies and 2^64 hash queries, a simulator that may depend on the public files and gets each
    request and, of the weights, one bit for it (served or refused: a request is refused if it is
    ill-formed, if the model has no result on it, or if its result is other tokens) makes a view
    within 2^-154 of the real one. The bit depends on the weights: so for every request of its
    choice a verifier learns whether the claimed output is the model's result. A service that
    chooses to say "failed" reveals one label of three in its place (served, failed or other
    tokens).
  - All six ask for exact match, which the verifier does not test: public files with another policy
    are not covered ([LIMITS.md](LIMITS.md), L5). A provider that picks its public files after
    seeing the hash function is not covered either ([LIMITS.md](LIMITS.md), L28). One public setup
    is known (`FilesInUse`; `filesInUse_stored`): the library's stored full-size files
    (`storedSetup`); their scale file is that of an example with synthetic weights (by the head of
    `Ladder/Stored.lean`; no theorem).
- **The Lean verifier.** Two Lean terms bear this name: one verifier, with and without its hash
  function. The audit page's Lean verifier is `leanVerifier setup`, that is `(compile (flashProve
  setup)).accepts blake2bHash`: the compiled verifier with each of its hash queries answered by
  BLAKE2b. On the other pages the Lean verifier is `verify` (`Ladder.lean`): the verifier of that
  same system, before any hash function is supplied (`compile_flashProve_verify_eq`, with
  `theDescription_eq`). As in any proof in the random-oracle model, the six speak of the verifier
  under a hash function drawn at random, not of `leanVerifier`, where BLAKE2b stands in its place:
  the three that speak of acceptance (`sound`, `soundAndBinding`, `completeOnCanServe`) draw the
  hash function at random, so their verifier is `verify` under a random hash function, not at
  BLAKE2b; the other three do not call the verifier. `leanVerifier setup` equals
  `finalVerifierProgram` at that setup's files (`leanVerifier_eq`). Wherever the user's files read
  as a claim, the verdict of `verdictOf`, the function whose parts `lean-verify` evaluates
  (`verdictOf_at`), is `finalVerifierProgram` at the user's public files
  (`verdictOf_eq_finalVerifierProgram`), and it is `verify`'s value at BLAKE2b (`verdictOf_map`).
  So, where the user's files read as a claim and the user's public files are a public setup's, and
  only there, that verdict is `leanVerifier`'s (`verdictOf_eq_leanVerifier`); the command does not
  establish that the public files are a public setup's. Five of the files that this function takes
  come from a parser outside Lean, of which nothing is proved, and nothing is proved of a run
  ([LIMITS.md](LIMITS.md), L53; L9).
  - The line `sound` rests on a theorem on `verify`: *the soundness theorem on `verify`*,
    `VerifierAndGoals.AtTheName.sound_of_verify_at` (`Johnson/Goal/Skeleton/SoundOfVerifyAt.lean`;
    [THEOREM.md](THEOREM.md)): `verify` is proved sound at the given public files, in the
    random-oracle model and at exact match. `finalSound` takes it at the files and carries `Sound`
    over to the compiled system (`theDescription_eq`, `Johnson/Goal/Description/Description.lean`;
    `compile_flashProve_sound_iff`, `Johnson/Face/FinalStatement.lean`; `finalSound` itself:
    `Johnson/Face/FinalSoundProof.lean`), and `sound` is `finalSound` at a public setup.

Every page here keeps two layers apart:

- **The protocol, as written in Lean:** what is proved of it, and of which object.
- **The programs** (C++ and CUDA). Nothing is proved about them, the verifier that users run by
  default among them, nor that they run the protocol that `verify` checks. What ties them to Lean is
  tests. The command `lean-verify` (`tools/lean-verify/`, at the repository's top) runs the
  executable form of `verify` inside Lean on the prover's proof files. No theorem speaks of the
  command itself, of its parser or of compiled code, and no stand-alone verifier program is proved
  sound ([THEOREM.md](THEOREM.md)). `verify-on-bytes` is the Lean text below `OnBytes.Main`: a hand
  translation of `cp_verify` into Lean, from which this repository builds no stand-alone program
  (one test, `tools/accepts/`, compiles it and has Lean load the compiled code while it evaluates
  files of `lean/Ask/`); it is a different verifier, the theorem is not about it, and `lean-verify`
  is the command to use.

## How to check it

The six theorems: two lines on [CHECKING.md](CHECKING.md), "The six theorems, and eight more", build
`AtFullSide/Face/TheSixLines.lean` and ask, for each of the six, on which axioms it depends; run on
a build of this repository's files they ended with exit status 0 and, for each of the six, Lean's
three standard axioms alone (the same place). The build compiles the heavy files of `ShapeLines/`
too, and needs a large machine.

A lighter look is at the soundness theorem on `verify`, on which `sound` rests. Install Lean as
[CHECKING.md](CHECKING.md) says under "Before you start". Run everything as an ordinary user, not as
root and not under `sudo`: as with any Lean project, a build runs code from this repository as your
user. Then, from the repository's top (the second line fetches Mathlib's compiled files; from the
public servers that fetch is untried: [CHECKING.md](CHECKING.md), "Before you start"):

```
cd lean
lake exe cache get
LEAN_ABORT_ON_PANIC=1 lake build Johnson.Goal.Skeleton.SoundOfVerifyAt > .lake/sound_of_verify_at.log 2>&1; echo "exit status: $?"
grep -A1 "sound_of_verify_at' depends" .lake/sound_of_verify_at.log
```

The exit status must be 0, and the answer must read `'VerifierAndGoals.AtTheName.sound_of_verify_at'
depends on axioms: [propext, Classical.choice, Quot.sound]`, with nothing else in the brackets. A
build alone does not fail on an unfinished proof or a new axiom: that answer is what shows that none
lies beneath this name. It reads the compiled files and re-checks nothing. The build compiles about
16,000 Lean files and needs a large machine (on a machine with many cores and less memory set
`LEAN_NUM_THREADS`: [CHECKING.md](CHECKING.md), "What you can do, and on what machine"). The
library's own full check is `scripts/check.py`; one whole run over this repository's files has
passed ([CHECK-RESULTS.md](CHECK-RESULTS.md)). One Lean file, with one definition and four theorems,
which nothing else imports, was added after the runs reported here and checked on its own
([CHECK-RESULTS.md](CHECK-RESULTS.md)). Three of the check script's pinned values were changed and
three of its stored lists were extended for it; nothing else in the script or the lists changed. To
run the executable form of `verify` on a proof: `tools/lean-verify/README.md`.

## The pages

| For people | |
|---|---|
| [THEOREM.md](THEOREM.md) | the soundness theorem on `verify`: statement, assumptions, what an accept means, what it does not say, what has been run |
| [STATEMENTS.html](STATEMENTS.html) | the statements and the definitions beneath them, in plain words beside their Lean text: the page to audit |
| [AUDIT.md](AUDIT.md) | statements and definitions with their Lean text, as plain text |
| `STATEMENTS-ALL.html` | a long page that is not in this repository: many declarations, each with its comment beside its Lean text; one call makes it: [CHECKING.md](CHECKING.md), "The HTML pages" |
| [SOUNDNESS-PROOF-MAP.md](SOUNDNESS-PROOF-MAP.md) | the proof of the soundness theorem on `verify`, step by step |
| [TERMS.md](TERMS.md) | each term, the Lean name that states it, and of which system it is proved |
| [CHECKING.md](CHECKING.md), [CHECK-RESULTS.md](CHECK-RESULTS.md) | how to check the library by machine, and what has been run of the full check |
| [CREDITS.md](CREDITS.md) | what was adapted from others' work, and where it came from |

| For agents | |
|---|---|
| [LIMITS.md](LIMITS.md), [GAPS.md](GAPS.md) | every limit and every gap, each whole under a label that the Lean files' comments cite |
| [GLOSSARY.md](GLOSSARY.md) | the working words of the comments, and the short labels in the names of folders and files |
| `OnBytes/`, `Johnson/Bind/`, `Ask/`, `ThirdParty/`, `ShapeLines/`, `scripts/` | each has a `README.md` of its own |

The pages "for agents" are open to anybody: they are written to be looked up, by label or number,
not read through. A number behind lean/GAPS.md, as in "lean/GAPS.md, 52", is an entry of that page,
not a line; a label behind lean/LIMITS.md, as in "L15", is an entry there.

Which list of words to open: for the terms of the claims, [TERMS.md](TERMS.md); for a word in a Lean
comment or in the name of a folder or file, [GLOSSARY.md](GLOSSARY.md).

## The folders

| Where | What |
|---|---|
| `Ladder.lean`, `Ladder/` | `verify`, which public files are in scope, the error bound, and goals typed for any IOP, as definitions |
| `Johnson/Goal/` | `Skeleton/`: the soundness theorem on `verify` and its further forms. `Description/`: `theDescription`, with the tests on the public files |
| `Johnson/PVR/` | the executable form of `verify`, and the theorems that tie it to `verify` |
| `Johnson/Face/`, `AtFullSide/Face/` | `AtFullSide/Face/TheSixLines.lean`: the six theorems, each about `compile (flashProve setup)`; besides, the compiled protocol, the final statement, a structure of six fields (`FinalStatementOneBit`; with the label shown: `FinalStatement`), and the Lean files on those fields; how the fields stand to the six theorems: [LIMITS.md](LIMITS.md), L93 |
| `VerifiableInference/` | the statements (`Sound` and its kin, `Statements.lean`) and the random oracle model; `Final/`: theorems on the compiled prover and on the protocol's statements at the public files; `Compilation/FinalRoad.lean`: what the final statement's field `zeroKnowledge`, and a statement that gives its field `complete` (`FinalCompleteAtEveryRequest`), follow from; `Bounds/`, over `IntegerModel/Bounds/`: the library's own worst-case checks on the weights, and what follows at weights that pass the first worst-case check, or the least-bound check with numbers that hold |
| `IntegerModel/`, `Inst/` | the model: a transformer in integer arithmetic |
| the rest of `Johnson/` | most of it the proof: a soundness lemma for each kind of step of the protocol, and the theorems that join them; `Bind/`: an illustrative committer |
| `Cb/`, `Cm/`, `Blocks/`, `Iop/`, `Ior/`, `Hiop/`, `Cond/` | the sub-protocols, the model's relation, interactive oracle proofs and reductions, and the object that the sub-protocols form |
| `Compile/`, `CompileK/`, `Top/`, `Rom/`, `ZKCP/` | the library's general compiler to a non-interactive argument (the `compile` of the six theorems is declared elsewhere: `Johnson/Face/Compiler.lean`), the random oracle model, the definition of the argument system (`ZKCP/Defs.lean`) |
| `Code/`, `ThirdParty/`, `Prob/`, `Hash/`, `Alg/` | coding theory (`ThirdParty/`: adapted from ArkLib and Mathlib), probability, Merkle trees, algebra |
| `E2E/` | the protocol as an interactive oracle proof at the public files (`protocolAtFiles`), with the statements on it: soundness (`E2E/SoundAsIOPAtFiles.lean`), completeness (`E2E/CompleteAsIOPAtFiles.lean`) and the three side by side (`E2E/ThreeAtOneProtocol.lean`); most of the proof on index privacy |
| `Johnson/WholeKey/`, `Johnson/Prover/`, `Johnson/LinkSim/` | the results on index privacy, and the link proof's honest prover; the proof of the conditional theorem on index privacy also runs through `Johnson/LateWorld/`, `LateSide/`, `LateSide2/`, `TokenSide/`, `TokenSide2/`, `TokenRel/`, `TokenRules/`, `WrapLaws/`, `GhostSide/`, `HopSide/` and `CoinsTie/` |
| `AtFullSide/` | a side library: theorems at the library's written copies of the two stored sets of public files; `Honest/`, `E2E/`: the honest provers written in Lean (definitions, not programs that run), and the Lean files on them |
| `ShapeLines/` | a third Lean library (no default target; a thread stack of 256 MiB): closed facts on the stored full-size layout that Lean's kernel evaluates; the side library's files import them ([ShapeLines/README.md](ShapeLines/README.md)) |
| `Policy/` | acceptance policies: what it means to meet one (`MeetsPolicy`), and the relation on a request under a policy |
| `Run/`, `Fmt/`, `Decl/`, `OnBytes/` | Lean functions on bytes, BLAKE2b among them, and the text `verify-on-bytes` (not `verify`; nothing on its soundness is proved: [LIMITS.md](LIMITS.md), L53) |
| `Ask/`, `scripts/` | files that put single questions to Lean; the full check and its lists |

## Who wrote it

AI systems wrote nearly all of the Lean library, part of it adapted from credited third-party code
([CREDITS.md](CREDITS.md)), and nearly all of the pages under `lean/`. Lean's kernel checks the
proofs, so nobody needs to read them: a person reads what is proved. The meaning lies in the
statement and in the definitions that it names, which [STATEMENTS.html](STATEMENTS.html) sets out,
but for three large values that it names and leaves as black boxes: the protocol's description, one
test on the public files, and the honest provers and settings. `verify` and the definitions beneath
the statements are definitions: Lean's kernel checks proofs, not what a definition means, so a
reader of the statements must read those definitions ([LIMITS.md](LIMITS.md), L43). Comments in the
Lean files, and some strings in the code of about twenty of them, are notes for whoever builds on
the proofs. Lean does not check them, and what holds is what the theorems state, not what such a
note says; some are rough, and some point to files that are not in this repository, and what they
say on the strength of such a file is not shown here. Where a comment, a string or a page differs
from Lean's printed statement, the statement counts; a limit that a page places in a file's head or
a docstring holds as it stands there ([LIMITS.md](LIMITS.md), L23, L55, L56).
