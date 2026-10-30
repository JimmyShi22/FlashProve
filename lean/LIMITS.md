# Limits of the Lean library

Terms: [TERMS.md](TERMS.md).

This page is a reference. It tells each limit of the library in full, once, under a label (V0, V2,
…; L1, L2, …). Comments in the Lean files and the other pages tell a limit in short and point here
by its label. Labels are names, not a count: they give no order, and not every number is in use.

The short ranked list for a person is on [THEOREM.md](THEOREM.md), "What it does not say". What is
open at the soundness theorem on `verify`, at its verifier and at the interface between the C++
programs and Lean: [GAPS.md](GAPS.md). The limits of `verify-on-bytes`, the Lean text below
`OnBytes.Main` (a hand translation of `cp_verify` into Lean, from which this repository builds no
stand-alone program; one test (`tools/accepts/`) compiles it and has Lean load the compiled code
while it evaluates files of `Ask/`): [OnBytes/LIMITS.md](OnBytes/LIMITS.md). What has been run of
the full check: [CHECK-RESULTS.md](CHECK-RESULTS.md).

One Lean file, with one definition and four theorems, which nothing else imports, was added after
the runs reported here and checked on its own ([CHECK-RESULTS.md](CHECK-RESULTS.md)). Three of the
check script's pinned values were changed and three of its stored lists were extended for it;
nothing else in the script or the lists changed.

## What is proved, and of which object

The library holds theorems about several objects. A limit on this page is a limit of the object that
its entry names, and of no other.

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
  theorems the six lines; all that goes with them: L93.
  - Soundness, `sound`: a cheating committer and prover with q hash queries between them get the
    verifier to accept output tokens that are not the model's, at the weights that one extractor
    reads from the commitment and the committer's hash queries, with probability at most about
    q/2^124 + 2^-101. That is a bound, not a security level (L11).
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
    else it does not cover: L93, L83.
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
    are not covered (L5). A provider that picks its public files after seeing the hash function is
    not covered either (L28). One public setup is known (`FilesInUse`; `filesInUse_stored`): the
    library's stored full-size files (`storedSetup`); their scale file is that of an example with
    synthetic weights (by the head of `Ladder/Stored.lean`; no theorem).
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
  come from a parser outside Lean, of which nothing is proved, and nothing is proved of a run (L53;
  L9).
  - The line `sound` rests on a theorem on `verify`: *the soundness theorem on `verify`*,
    `VerifierAndGoals.AtTheName.sound_of_verify_at` (`Johnson/Goal/Skeleton/SoundOfVerifyAt.lean`;
    [THEOREM.md](THEOREM.md)): `verify` is proved sound at the given public files, in the
    random-oracle model and at exact match. `finalSound` takes it at the files and carries `Sound`
    over to the compiled system (`theDescription_eq`, `Johnson/Goal/Description/Description.lean`;
    `compile_flashProve_sound_iff`, `Johnson/Face/FinalStatement.lean`; `finalSound` itself:
    `Johnson/Face/FinalSoundProof.lean`), and `sound` is `finalSound` at a public setup.
  - The independent checker has accepted the soundness theorem on `verify`, with what lies beneath
    it, over a build of this repository's files; which of the six it has accepted by name: L80.
  - That theorem's only hypotheses are three on the public files: they are in scope, they are read
    without error, and they ask for exact match. `verify` is compiled from `theDescription`: the
    protocol that the programs are written to run, as Lean describes it. That it is what the
    programs run is not proved. The short ranked list of that theorem's limits stands on THEOREM.md,
    and what is open at it on GAPS.md. Entries L1 to L52 tell its limits one by one: what its
    statement says, its bound, the verifier and the model, the commitment, what else is proved, and
    how far the checking goes. At other policies in scope there is *the theorem under a policy*,
    `soundUnderPolicy_of_verify_at` (L5). What is proved of acceptance: L9.
- **The protocol as an interactive oracle proof, before hashing.** For the protocol as written in
  Lean, and for honest provers written in Lean as definitions (not programs that run), default
  values included, Lean proves soundness, and two things beside it, first for the interactive oracle
  proof, before hashing, and then for the compiled prover and verifier (the six lines): completeness
  on served requests, and zero knowledge, which before hashing is honest-verifier zero knowledge.
  The three statements before hashing are about one protocol; completeness and zero knowledge about
  one triple of provers in it (L92).
  - Completeness: on served requests the three runs' chances of failing (offline, link, online: L90)
    add up to at most 2^-41 before hashing, among the challenges that pass the proof-of-work tests.
  - Zero knowledge: before hashing it is honest-verifier and statistical, and one bit for each
    request (served or not) is not hidden.
  - Completeness and zero knowledge hold at public files that pass three tests (they are in scope,
    they pass `protocolDataWellFormed`, and they are read without error: L88); the statements of L92
    and those on the compiled system also need files that ask for exact match (a public setup,
    above). The library's stored full-size files `VerifierAndGoals.storedPublicFiles` meet these
    conditions. Completeness says nothing where the model has no result; zero knowledge holds there
    too, by the corollary at every request, except that the bit is revealed, or the label where a
    service shows it.
  - Further theorems are about weights that pass the first worst-case check, or the least-bound
    check with numbers that hold (these are the library's own checks; neither is `cp_commit`'s
    worst-case check): at these the model has a result on every well-formed request. They cover no
    request that completeness after compiling does not already cover: that holds at all weights, for
    every well-formed request whose claimed output is the model's result. What follows from this
    premise on the weights is said of every prompt, not of every request (L93). Made-up weights are
    shown by name to pass the first check, and at the reference settings every set of weights whose
    layers lie within one stated bound is shown to pass the first check, or the least-bound check
    with numbers that hold (`passesSomeWorstCaseCheck_atReferenceSettings`); no theorem says whether
    a real model's weights do.
  - Neither completeness nor zero knowledge covers batches, coins derived from a short key or the
    simulators' running time, and neither says anything of what the public files themselves tell of
    the weights, of timing or of the released programs (the C++ verifier and committer, the CUDA
    prover). Zero knowledge holds within stated bounds on what is shown under one commitment, and
    for one commitment to the weights. The theorems, their objects and their limits: L88 to L93.
- **`innerCompiledVerifier`.** It is the verifier that this library's compiler makes from an
  interactive oracle proof (IOP) written in Lean, whichever it is given. `verify` runs
  `innerCompiledVerifier` at `theDescription`, behind a test on the public files
  (`protocolDataWellFormed`), two public readings and a parser. *The theorem on
  `innerCompiledVerifier`*, `VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound`
  (`Johnson/Top/InnerCompiledVerifier.lean`), says this: round-by-round soundness of the key, copy
  and proof protocols gives soundness of the hash-compiled argument. It holds under 16 named
  hypotheses. It is not the soundness theorem on `verify`, whose proof calls, for the compiler's
  step, another form of it (`verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor`,
  `Johnson/Top/InnerCompiledVerifierByPublicReading.lean`). Entries V0 to V13 are about that theorem
  and what stands between it and the programs. Where they speak of hypotheses that are not proved,
  they speak of the two IOPs of `Johnson/Flat/TwoSizes.lean` (a full size and a small example), not
  of `theDescription`. The 16 named hypotheses are not the sixteen tests on the public files that
  `verify` runs itself (THEOREM.md). In comments "verify()" stands for `innerCompiledVerifier` in
  some places and for `verify` in others (L53).
- **The definitions in which the statements are written, and the model.** `Sound`, `CompleteOn`,
  `ZeroKnowledgeOn` and the other properties (`VerifiableInference/Statements.lean`,
  `MoreStatements.lean`, `Steps.lean`) are defined over any argument system; the condition
  `CanServe` (`VerifiableInference/CanServe.lean`), the claim under a policy, `MeetsPolicy`
  (`Policy/Front/MeetsPolicy.lean`), and the integer model (`VerifiableInference/ModelWeights.lean`,
  `IntegerModel/`) are defined over the model alone. A definition is no theorem: which property is
  proved, and of which system, is told at L18. A limit of a definition is a limit of every theorem
  that is stated through it.
- **`verify-on-bytes`** (`OnBytes/`), a Lean text from which this repository builds no stand-alone
  program. It is not `verify` and does not run it. The theorems in `OnBytes/` are about that text;
  no theorem on soundness among them reaches a call that checks a real proof, and a program built
  from it is not independent of `cp_verify`, the C++ verifier (L22).
- **The released programs: the C++ verifier and committer and the CUDA prover.** Nothing is proved
  about them, nor that they run the protocol that `verify` checks. Their own limits are on
  `docs/limits.md` (at the repository's top).

L93 is the entry on the six lines (their place in the build: L88). Entries L88 to L92 are about the
protocol's honest provers as written in Lean, and about soundness, completeness and zero knowledge
before hashing; L94 to L98 tell what the lemmas on these provers leave open. Entries L1 to L52 are
about the soundness theorem on `verify`, the definitions in which it is stated, the model and the
checks. Entries L53 to L60 tell what is called a verifier here and how to read the comments of the
Lean files. L61 to L75 are about the Lean verifier's system: illustrative systems (they keep its
verifier and extractor and have another committer, written in Lean), Lean's results on index privacy
at the default setting, and single limits on its statements and on the public files. L76 to L87 are
further limits, each of the object that it names first.

## How an entry says how it is known

A **Basis** line says how what an entry says is known. *Proved*: a Lean theorem says it. *By
reading*: it is read off the Lean statement, definition or docstring, or the page or source file,
that is named; it is not machine-checked: no theorem or program establishes the sentence; most such
sentences are negatives, which Lean cannot prove about itself. *Computed*: arithmetic, or a search
over the files' text. *Tested*: a program was run; the line says on what. *Not shown in this
repository*: it rests on files or runs that are not here. What stands on a reading, a comparison, a
search, a run, a proof or argument on paper, or arithmetic by hand has not been independently
reviewed or repeated, unless the place says otherwise: that is said here and at L43, not at each
place. A name that stands there without a path can be found by a search of the library.

## All limits, by weight

In four groups, the heaviest first, and a fifth, which is not ranked. The entry has the limit: how
far it goes, what is proved beside it, and how it is known.

**Before the four groups: the named hypotheses of the theorem on `innerCompiledVerifier`.** That
theorem is neither one of the six nor the soundness theorem on `verify`, and neither the six nor the
soundness theorem on `verify` has any of these as a hypothesis; at `theDescription`, where the tests
on the public files pass, `keySound` and `proofSound` are theorems (`keySound_holds`,
`proofSound_of_verify`; V10). The named hypotheses are the fields of one structure,
`CompilerSoundnessConditionsWithMeaning` (`Johnson/Top/InnerCompiledVerifier.lean`). They are
hypotheses, not axioms: Lean's list of axioms shows none of them. Each one that is not proved is a
limit: if it is false, the theorem on `innerCompiledVerifier` says nothing (V9). "State" is at the
two IOPs of `Johnson/Flat/TwoSizes.lean`, with parameters open; "proved" and "holds" rest on the
theorems `withContentFull`, `byDefinitionFull`, `byConstructionFull`, `atOurWiringFull` and their
forms at the small example, in that file.

| Name | In one line | State at the two IOPs | Entry |
|---|---|---|---|
| `keySound` | the key file's protocol is round-by-round sound | not proved; may be false. (At `theDescription`, where the tests on the public files pass, it is a theorem: `keySound_holds`; V10.) | V10 |
| `proofSound` | the proof file's protocol is round-by-round knowledge sound | not proved; may be false; at the small example it cannot be met. (At `theDescription`, where the tests on the public files pass, it is a theorem: `proofSound_of_verify`; V10.) | V10 |
| `commitment` | index binding at the key carries over to index binding at the 32-byte commitment ID | not proved of a given set of parameters; met by setting free fields | V11 |
| `sound` (a field of this structure, not the theorem `sound`) | what the relation says is "the output tokens are the model's" | not proved for every claim; a definition to read | V9 |
| `wires` | in every round, uniform hash answers give an exactly uniform verifier message | true of a layout of the hash queries that is written in this library; not shown of the programs' | V3 |
| `entrySound` | the copy's file's protocol is round-by-round sound | proved, with the statement on codes as a hypothesis (L15) | V3, V8 |
| `seedLaw` | an OOD seed made from uniform digests makes a given word collide only with small probability | proved | V3 |
| `answersCode` | no two lists of OOD answers are written alike | proved, of a coding that is written in this library | V3 |
| `noneColl`; `keyLocal`, `entryLocal`, `proofLocal`; `keyCoherent`, `entryCoherent`, `proofCoherent`; `answersLength` | how the decoder, the three verifiers' reads, their marks and the answers' lengths are laid out | hold by a definition (the first) or by construction | V3 |

Of the eleven that hold besides `wires`, ten say nothing of a cheating prover; the one that does is
`entrySound`. *May be false*: it states a fact about the IOP that could turn out false. *A
definition to read*: it defines what is being claimed; the reader must judge whether the claim is
the one wanted, and no proof could settle that.

**What changes what you may conclude.** Read these first.

| | limit | part |
|---|---|---|
| L15 | [The statement on codes: proved here, from adapted files](#theorems-under-the-statement-on-codes) | 6 |
| L1 | [A model in Lean, not the programs](#a-model-in-lean-not-the-programs) | 3 |
| L12 | [Parameters: where they come from, proof of work, and a kept row's random values](#parameters-where-they-come-from-proof-of-work-and-a-kept-rows-random-values) | 3 |
| L21 | [The compiler and the proof files differ in two places](#the-compiler-and-the-proof-files-differ-in-two-places) | 3 |
| L22 | [Lean functions on bytes, and `verify-on-bytes`](#lean-functions-on-bytes-and-verify-on-bytes) | 3 |
| L7 | [The model is the library's own integer program](#the-model-is-the-librarys-own-integer-program) | 3 |
| L27 | [Completeness is stated only where CanServe holds](#completeness-is-stated-only-where-canserve-holds) | 3 |
| L90 | [Completeness, as an interactive oracle proof, on served requests](#completeness-as-an-interactive-oracle-proof-on-served-requests) | 10 |
| L91 | [Honest-verifier zero knowledge, as an interactive oracle proof, before hashing](#honest-verifier-zero-knowledge-as-an-interactive-oracle-proof-before-hashing) | 10 |
| L93 | [The compiled prover and verifier: the six theorems](#the-compiled-prover-and-verifier-the-six-theorems) | 10 |
| L44 | [How the model differs from the public model](#how-the-model-differs-from-the-public-model) | 3 |
| L2 | [Whose weights](#whose-weights) | 1 |
| L28 | [What the commitment does not bind](#what-the-commitment-does-not-bind) | 4 |
| L4 | [One commitment, one proof; a joint probability](#one-commitment-one-proof-a-joint-probability) | 1 |
| L5 | [Exact match only](#exact-match-only) | 1 |
| L18 | [What is proved, and what is not](#what-is-proved-and-what-is-not) | 5 |
| L19 | [Several proofs, several commitments: weak bounds](#several-proofs-several-commitments-weak-bounds) | 2 |
| L11 | [The bound is a probability for a number of hash queries](#the-bound-is-a-probability-for-a-number-of-hash-queries) | 2 |
| L10 | [The bound mixes two units](#the-bound-mixes-two-units) | 2 |
| L33 | [After an honest commitment: a weak bound](#after-an-honest-commitment-a-weak-bound) | 2 |
| L29 | [Valid settings need not suit any model](#valid-settings-need-not-suit-any-model) | 3 |
| L25 | [The independent checker](#the-independent-checker) | 6 |
| L9 | [Soundness alone says little](#soundness-alone-says-little) | 4 |
| L14 | [Hiding and soundness, object by object](#hiding-and-soundness-object-by-object) | 3 |
| L50 | [What the results on hiding rest on](#what-the-results-on-hiding-rest-on) | 3 |
| L43 | [Who wrote it, and what has not been independently reviewed](#who-wrote-it-and-what-has-not-been-independently-reviewed) | 6 |

**What the statements say exactly, and what they leave out.** For whoever quotes a theorem.

| | limit | part |
|---|---|---|
| L38 | [The statement itself](#the-statement-itself) | 1 |
| L36 | [What the verifier rejects outright](#what-the-verifier-rejects-outright) | 1 |
| L37 | [Any prefix of the model's answer](#any-prefix-of-the-models-answer) | 1 |
| L39 | [Ties, and where the model has no value](#ties-and-where-the-model-has-no-value) | 1 |
| L47 | [Tokens are numbers](#tokens-are-numbers) | 1 |
| L3 | [The prover picks what is claimed](#the-prover-picks-what-is-claimed) | 5 |
| L8 | [Random oracle, classical adversary](#random-oracle-classical-adversary) | 2 |
| L41 | [A system whose proof is simply the weights](#a-system-whose-proof-is-simply-the-weights) | 4 |
| L13 | [No sizes, no running times](#no-sizes-no-running-times) | 2 |
| L32 | [Opening a commitment](#opening-a-commitment) | 4 |
| L42 | [One honestly made commitment in the experiment](#one-honestly-made-commitment-in-the-experiment) | 4 |
| L51 | [Five definitions that take a default value where an input is missing](#five-definitions-that-take-a-default-value-where-an-input-is-missing) | 6 |
| L52 | [At the proximity test 2^-128 is one round's figure](#at-the-proximity-test-2-128-is-one-rounds-figure) | 6 |

**How the library is checked, and what it leaves unproved.** With L25 above.

| | limit | part |
|---|---|---|
| L46 | [What is machine-checked on the agreement of Reed–Solomon codes](#what-is-machine-checked-on-the-agreement-of-reedsolomon-codes) | 6 |
| L17 | [Conditional theorems](#conditional-theorems) | 6 |
| L16 | [Statements without a proof](#statements-without-a-proof) | 6 |
| L23 | [Comments are not checked](#comments-are-not-checked) | 6 |
| L24 | [The script that ships with the library](#the-script-that-ships-with-the-library) | 6 |
| L26 | [Tests that change the source](#tests-that-change-the-source) | 6 |
| L45 | [Trusted, not proved](#trusted-not-proved) | 6 |

**The cited definition, and the texts that are followed.** On `ZKCP.IsZKCPArg`, and on the sources
of Lean's protocol.

| | limit | part |
|---|---|---|
| L35 | [A scheme with empty proofs meets the definition](#a-scheme-with-empty-proofs-meets-the-definition) | 5 |
| L49 | [Hiding for batches: a definition, and no theorem on the protocol](#hiding-for-batches-a-definition-and-no-theorem-on-the-protocol) | 5 |
| L48 | [The protocol in Lean and the protocol of the texts](#the-protocol-in-lean-and-the-protocol-of-the-texts) | 3 |

**Verifiers by name, what comments say, the illustrative committers, the results on index privacy,
further limits, and completeness and zero knowledge with the lemmas on the honest provers.**

| | limit | part |
|---|---|---|
| L53 | [What is called a verifier in this library](#what-is-called-a-verifier-in-this-library) | 7 |
| L54 | [Hiding under a tolerant policy](#hiding-under-a-tolerant-policy) | 7 |
| L55 | [Comments may say more than the library shows](#comments-may-say-more-than-the-library-shows) | 7 |
| L56 | [How to read a comment that cites a file](#how-to-read-a-comment-that-cites-a-file) | 7 |
| L57 | [The limits of two conditional files beneath the soundness theorem on `verify`](#the-limits-of-two-conditional-files-beneath-the-soundness-theorem-on-verify) | 7 |
| L58 | [A comment that reads brighter than two theorems bear](#a-comment-that-reads-brighter-than-two-theorems-bear) | 7 |
| L59 | [Three premises that are not shown to be met here](#three-premises-that-are-not-shown-to-be-met-here) | 7 |
| L60 | [A named theorem whose file is not here](#a-named-theorem-whose-file-is-not-here) | 7 |
| L61 | [Properties of an illustrative system](#properties-of-an-illustrative-system) | 8 |
| L62 | [The committed tables alone, before any hashing; no prover's message](#the-committed-tables-alone-before-any-hashing-no-provers-message) | 8 |
| L63 | [The conditional theorem's conditions that read no prover or coin](#the-conditional-theorems-conditions-that-read-no-prover-or-coin) | 8 |
| L64 | [Conditional theorem on index privacy: not the whole protocol](#conditional-theorem-on-index-privacy-not-the-whole-protocol) | 8 |
| L65 | [The link proof's honest prover, written in Lean, and its files](#the-link-proofs-honest-prover-written-in-lean-and-its-files) | 8 |
| L66 | [Statements on hiding that have not been independently reviewed](#statements-on-hiding-that-have-not-been-independently-reviewed) | 8 |
| L67 | [That `verify` rejects no other policy rests on a reading](#that-verify-rejects-no-other-policy-rests-on-a-reading) | 8 |
| L68 | [The set of possible weights sets the limit](#the-set-of-possible-weights-sets-the-limit) | 8 |
| L69 | [The library's written copies of the public files](#the-librarys-written-copies-of-the-public-files) | 8 |
| L70 | [The digest checks on the written copies are evaluations](#the-digest-checks-on-the-written-copies-are-evaluations) | 8 |
| L71 | [`SoundFor` says as much as its claim says](#soundfor-says-as-much-as-its-claim-says) | 8 |
| L72 | [`SoundForWith` and the definition's form: two arrows, no stated equivalence](#soundforwith-and-the-definitions-form-two-arrows-no-stated-equivalence) | 8 |
| L73 | [Refined completeness: where it is proved](#refined-completeness-where-it-is-proved) | 8 |
| L74 | [Two theorems on the guard speak of the first chain's run alone](#two-theorems-on-the-guard-speak-of-the-first-chains-run-alone) | 8 |
| L75 | [Lines in comments that name a reading](#lines-in-comments-that-name-a-reading) | 8 |
| L76 | [What the full check does not build, replay or test](#what-the-full-check-does-not-build-replay-or-test) | 9 |
| L77 | [The order of draws in one sumcheck of the C++ verifier](#the-order-of-draws-in-one-sumcheck-of-the-c-verifier) | 9 |
| L79 | [A verdict of the typed verifier computed on bytes: an unchecked length, and a related case](#a-verdict-of-the-typed-verifier-computed-on-bytes-an-unchecked-length-and-a-related-case) | 9 |
| L80 | [Four theorems at which the independent checker gives no verdict](#four-theorems-at-which-the-independent-checker-gives-no-verdict) | 9 |
| L81 | [The soundness proof runs by list decoding](#the-soundness-proof-runs-by-list-decoding) | 9 |
| L82 | [Further limits of the named hypotheses of `innerCompiledVerifier_sound`](#further-limits-of-the-named-hypotheses-of-innercompiledverifier_sound) | 9 |
| L83 | [What `ZeroKnowledgeOn` covers, and what it leaves out](#what-zeroknowledgeon-covers-and-what-it-leaves-out) | 9 |
| L84 | [What a bound on zero knowledge counts](#what-a-bound-on-zero-knowledge-counts) | 9 |
| L85 | [`Laid` and `LaidAlone` do not determine a block](#laid-and-laidalone-do-not-determine-a-block) | 9 |
| L87 | [Three comments under `Johnson/P1K8R/` say that premises follow from the head](#three-comments-under-johnsonp1k8r-say-that-premises-follow-from-the-head) | 9 |
| L88 | [How these theorems stand, and of what they speak](#how-these-theorems-stand-and-of-what-they-speak) | 10 |
| L89 | [Soundness, as an interactive oracle proof](#soundness-as-an-interactive-oracle-proof) | 10 |
| L92 | [The three, of one protocol and one triple of provers](#the-three-of-one-protocol-and-one-triple-of-provers) | 10 |
| L94 | [Lemmas on the honest prover hold "wherever the invariant holds"](#lemmas-on-the-honest-prover-hold-wherever-the-invariant-holds) | 11 |
| L95 | [No state is shown at which the test `shapeAt` accepts](#no-state-is-shown-at-which-the-test-shapeat-accepts) | 11 |
| L96 | [`RowDataIsReady` is stated, not proved](#rowdataisready-is-stated-not-proved) | 11 |
| L97 | [Cases that two of the honest prover's senders handle with a default value and no error](#cases-that-two-of-the-honest-provers-senders-handle-with-a-default-value-and-no-error) | 11 |
| L98 | [A test on the shape that no definition of the honest provers asks](#a-test-on-the-shape-that-no-definition-of-the-honest-provers-asks) | 11 |

## The theorem on `innerCompiledVerifier`

Entries V0 to V13 are about `innerCompiledVerifier`, the verifier that this library's compiler makes
from an IOP (interactive oracle proof, as written in Lean), and about its theorem,
`VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound`
(`Johnson/Top/InnerCompiledVerifier.lean`). They are not about the Lean verifier `verify`, whose
soundness theorem ([THEOREM.md](THEOREM.md)) is stated at another IOP, `theDescription` (the
protocol that the programs are written to run, as Lean describes it). Where a limit of these entries
has a counterpart there, the entry says what holds there. No entry here tells a theorem on the
released programs.

### V0. The public files, `verify-on-bytes`, and the parser

**What "proved" means on this page.** "Proved" and "Lean has checked" mean that Lean's build
accepted the proof. A build alone does not fail on an unfinished proof or on an added axiom: the
full check does ([CHECKING.md](CHECKING.md); what has been run of it:
[CHECK-RESULTS.md](CHECK-RESULTS.md)).

**The public files are fixed first.** Every soundness statement here takes the public files as fixed
before the hash function is drawn. A committer that chooses its public files with the hash function
in hand, for instance by trying many against it, as every provider can in use, is covered by no
theorem.

**`verify-on-bytes`.** All four parts of `verify-on-bytes` (the commitment ID, the key file, the
copy's file, the proof file) are written by following the C++ verifier's source, not made by the
compiler, so a mistake that the two share would not show. A user cannot rely on a `YES` of
`verify-on-bytes` being a yes of `innerCompiledVerifier`. One tie between the two is stated, under
hypotheses that are proved at no input and may be false (`OnBytes.K.exit_innerCompiledVerifier`,
`Johnson/Top/TieInnerCompiledVerifier.lean`: L22). Exit code 0 covers both `YES` and `WITHIN
LIMITS`. `verify-on-bytes` and the C++ verifier, `cp_verify`, are tested against each other, not
proved equal, and known to differ in named places (`OnBytes/LIMITS.md`).

**`front_sound`.** The limits of `front_sound`, a theorem under named hypotheses, every one of which
is left open there, about any term that takes a commitment ID, a prompt, output tokens and the
files, and asks the hash function as an oracle, stand in the head of `Johnson/Top/FrontParts.lean`
("What it does not show"). Neither it nor the theorem on `innerCompiledVerifier` is proved from the
other.

**The parser.** A parser makes typed strings of the files. It needs no trust for the soundness of
the proof: the claim (the commitment ID, the prompt, the output tokens and the public files) comes
from the user, not from the parser, and the parser's own hash queries count as the prover's. Each
hash chain's starting value is taken as the prover's message and hashed in before its own chain
draws anything; nothing that the statement must bind reaches a chain through these values alone.
That rests on a reading of the format and the code; it is not proved.

`front_sound` holds for every parser that is fixed before the hash function is drawn. No hypothesis
of it excludes a parser that holds a fixed hash function inside: for the parsers written in this
library that rests on a reading of their text; no scan for it ships, and no theorem says it.

**The starting values.** This limit is about Lean's side behind the parser (the tests in `Ask/`, and
the theorems' design), not about `cp_verify` and `verify-on-bytes`. Both compute every chain's
starting value themselves, where a chain has one: one hash call on the chain's label, the digest of
its parameters and 32 more bytes, which are the binding tree's root at the shared chain and 32
random bytes that stand in the file at each other chain. That is read from a copy of the two
programs' sources that differs from the sources here; that this part is the same is not shown.

What the tests do: the parser hands them seven starting values. The two of the shared chains are
recomputed and compared, in a test that stands in front of the compiled verifier. The other five
(the key file's one-time and second chain, the link chain of the copy's file, the proof file's first
and second chain) are taken as given: asked is only that each has 32 bytes and is not all zero. They
are not recomputed there: the parsed files do not hold the 32 random bytes, and the tests do not
read the parser's order file, which holds them.

Where that matters: the format tells two trees of one number apart by their chains' starting values
alone (`docs/format/FORMAT.md`, R7.13). At the full-size key file one tree of the shared chain and
one of the second chain agree in number, depth and width. No test compares one starting value with
another, so whoever fills in a parsed file can make the two equal, and in the test the format's
separation of these two trees is then gone. No gain to a prover from it is known: each root binds
its own leaves. No theorem says so. The compiled tests of a key file and a proof file ship at the
small size, where no two trees meet.

**Behind the parser: not the same on every file.** A verifier behind the parser judges the parsed
file, not the original file. One original file has many parsed files: this parser writes one, and
whoever fills a parsed file by other means can put other values into those entries of a path that
the verifier does not read. And several original files can have one parsed file: a file that leaves
out an opening whose leaves are all opened elsewhere in the file parses to the same parsed file as
the whole file. Such a verifier accepts the shorter file, and `cp_verify`, which reads every given
digest and refuses a byte left over, refuses it. The theorem says the same of both original files,
since it speaks of the parsed file. So the two verifiers need not agree on every file. On files as
`cp_prove` writes them they can agree. (An original file in which a given digest is altered does not
get through this parser: it follows every opening by itself to its root.)

Basis: proved (`front_sound`, `exit_innerCompiledVerifier`) · by reading (the heads of
`Johnson/Top/FrontParts.lean` and `Johnson/Top/TieInnerCompiledVerifier.lean`; `Ask/README.md` and
the comments of the files under `Ask/`; `docs/format/FORMAT.md`; the two programs' sources; no
theorem says it) · computed (that `innerCompiledVerifier_sound` is not proved from `front_sound`:
the import lines; the converse: of the files that `Johnson/Top/FrontParts.lean` imports, at any
depth, none but the theorem's own names `innerCompiledVerifier_sound`, by a search of their text;
the trees' numbers, depths and widths: an evaluation from the public files at both sizes) · tested
(`verify-on-bytes` against `cp_verify`, both built from copies of the sources that differ from this
repository's; neither from this repository's: `OnBytes/LIMITS.md`).

### V2. Of what the theorem on `innerCompiledVerifier` speaks

The theorem on `innerCompiledVerifier`, `innerCompiledVerifier_sound`, is a theorem about every IOP
(interactive oracle proof, as written in Lean: Lean's specification of the interactive protocol,
with its rounds, messages and checks). It says this: round-by-round soundness of the protocols of
the key file, the copy's file and the proof file gives soundness of the argument that is compiled
with the hash function. So the interactive protocol's own soundness is assumed, not proved (V3). It
does not speak of the bytes of the files that the programs write: no theorem ties the two, and by
reading the two texts they differ in named places (V6).

**The two IOPs.** The library writes an IOP at the default setting's two sizes, the full size and a
small example: the two IOPs of `Johnson/Flat/TwoSizes.lean`. Only a part of each is written out. The
protocol of the copy's file and the OOD sample's seed and code are values; the key file's and the
proof file's protocols are written in this library at open parameters; the rest are open parameters,
the honest provers among them: nothing is asked of them, so nothing on completeness or on hiding is
said at these two IOPs. "Open parameters" are values left open, like x in a formula. Only the copy's
file, the decoder and the depth of the copies' tables are set at the two sizes: the key file's and
the proof file's chains are written at open parameters, fixed at neither size.

**The bound** is a formula in those parameters: Lean gives no number, nothing in the theorem makes
the bound small, it is no security level, and at some values of the parameters the statement says
nothing. At the two IOPs every round's error is stated at 2^-128, counted with the round's proof of
work; of the key file's and the proof file's rounds that figure is stated, not proved. Fiat–Shamir's
bookkeeping lies inside these stated errors too: a round's challenges are made from blocks of
digests inside the decision, and a round's error, as a share of these messages, holds the sampler's
bias and counts the work. That the challenges are near enough to uniform is stated with the errors,
not proved.

**The reply.** The reply's place is not fixed in the two IOPs: which part of an instance stands in
the first query is the open parameter `early` (V3), and binding the reply is left to `proofSound`
(the head of `Johnson/Flat/TwoSizes.lean`).

**The three kinds of file.** The programs write three kinds of file. The *key file* holds the first
weight table's Merkle root and the committer's proofs about it. A *copy's file* holds the root of
one stored copy of the table and a chain that ties it to the first table. A *proof file* is what a
client receives for one request (`GLOSSARY.md`). The pages under `docs/` call the copy's file the
leaf file, the first table the anchor and a further table a leaf table.

**Of `verify`.** That the bound is a formula without a number is said of
`innerCompiledVerifier_sound`. The error of the soundness theorem on `verify` is written out
([THEOREM.md](THEOREM.md)).

Basis: proved (`innerCompiledVerifier_sound`) · by reading (its statement; the head and the
definitions of `Johnson/Flat/TwoSizes.lean`; no theorem says it).

### V3. Under what it holds

The theorem on `innerCompiledVerifier` holds under 16 named hypotheses (V9). At the two IOPs of
`Johnson/Flat/TwoSizes.lean`, with parameters open, Lean has checked 12 of them:

- 8 hold by the way the IOP is built: 1 by a definition, 7 by construction.
- 2 are proved: `seedLaw`, and `answersCode`, on how the answers are coded, of a coding that is
  written in this library.
- 1, `wires`, is true only of a layout of the hash queries that is written in this library and is
  not shown of the programs': the layout is chosen so that the hypothesis holds: so it is met by
  that choice, and not proved of the programs' layout.
- 1, `entrySound`, takes the statement on codes as a hypothesis. The library proves that statement
  elsewhere, from files adapted from ArkLib and Mathlib (L15), and does not apply it in the theorem
  on `innerCompiledVerifier` itself: the forms at the two IOPs whose names end in `_codes` do
  (`Johnson/Flat/TwoSizesCodes.lean`), and so do the bounds on the closed check of the copy's file
  (V13).

The counts are the same at both sizes. They rest on the theorems `byDefinitionFull`,
`byConstructionFull`, `withContentFull`, `atOurWiringFull` and their forms at the small example
(`Johnson/Flat/TwoSizes.lean`), which hold for every value of the open parameters. Of the eleven
besides `wires`, ten say nothing of a cheating prover; the one that does is `entrySound`.

4 are not proved: `keySound` and `proofSound` (the key file's and the proof file's soundness),
`commitment` (the step on the commitment) and `sound` (what the claim means for the model). A user
cannot rely on these four. The weight of the theorem lies in them. `keySound` and `proofSound` may
be false (at the small example `proofSound` cannot be met: V10). `commitment` is not proved of a
given set of parameters (V11). `sound` is a definition to read: it defines what is being claimed,
and the reader must judge whether that is the claim wanted (V9). Nothing shows that the four can
hold together at an IOP of the programs' protocol (one toy IOP, Lean's own and not the programs',
meets all 16 together, at languages that are all of the space and at errors of 0: V8), and if one of
them is false the theorem says nothing. Soundness is reduced to them, not proved.

**Of `verify`.** All this is said of `innerCompiledVerifier_sound` and of the two IOPs. The
soundness theorem on `verify` is stated at another IOP, `theDescription` (the protocol that the
programs are written to run, as Lean describes it). It is proved under three hypotheses on the
public files and no other: they are in scope, they are read without error, and they ask for exact
match. In its model the second hash function is one fixed, named function
(`OnBytes.secondHashFunction`). The theorem assumes no property of it, collision resistance
included; that it may be treated as separate from the sampled hash function is an assumption of the
model, not a hypothesis of the theorem. No lemma about a step of the protocol and no conjecture on
codes is assumed there ([THEOREM.md](THEOREM.md)). The 16 named hypotheses are not the sixteen
conditions of THEOREM.md ("Its reach"), which are tests on the public files that `verify` runs
itself.

**Two assumptions.**

- **Assumption 1:** BLAKE2b may be treated as a random oracle, drawn after the public files are
  fixed. It is not a theorem, and it is not stated in Lean. It is an assumption about the hash
  function and this verifier together; its object is `Run.oBits ()`, made of Lean's BLAKE2b, and
  that Lean's text of BLAKE2b is BLAKE2b rests on known answers alone. No proof can close this (L8).
  Of these answers 287 come from `hashlib` of CPython 3.13.16, whose BLAKE2b is compiled from the
  BLAKE2 authors' own source code package, so they are not of another origin than the Lean texts; 39
  (13 of them also among the 287), all BLAKE2b-512 without key, salt or personalization, were each
  computed with two implementations that take neither their compression function nor their constants
  from that package, one of them a BLAKE2b in pure Python that is not part of this repository and
  may not be independent of that package. The same holds of `secondHashFunction` and
  `secondHashFunctionTree` as the format's second hash function: known answers alone.
- **Assumption 2** (of the programs and of the theorem on `innerCompiledVerifier`; what the
  soundness theorem on `verify` assumes of that function: above, "Of `verify`")**:** the second hash
  function resists collisions, and, as it runs BLAKE2b's compression function under another counter
  word, does not disturb BLAKE2b's standing as a random oracle. This is a weak assumption about the
  pair, that is one that asks little of it, and it is what the argument needs. That function is
  outside BLAKE2b's published analysis, and no attack on it is known. That a parameter file
  determines its four lookup tables rests on that assumption alone (the file holds only their
  digests under the second hash function): a condition on the public files, not on the prover. That
  is said of `cp_verify` and `verify-on-bytes`, which compute the four tables and compare. Of
  `verify-on-bytes` the Lean text says so (`tableHeld`, `OnBytes/Model/Config.lean`). Of `cp_verify`
  it is read from a copy of its source that differs from the source here; that this part is the same
  is not shown. `innerCompiledVerifier` compares no table with the file: there that link is checked
  by no theorem, and it is less than the byte format's own text asks (below, "The four lookup
  tables").
- In the byte format the request file's words enter the first chain's first query, before any
  challenge, under BLAKE2b itself; the second hash function stays beside it as a fixed function, and
  nothing that a prover chooses is bound by it alone. That rests on a reading of the Lean text and
  of the byte format; no theorem says it.
- The second hash function is built on BLAKE2b's compression function. As a fixed public function it
  is harmless only where what it digests is fixed before the hash function is drawn; where it also
  digests the request file, that digest is redundancy: the words stand under BLAKE2b itself.
- For the theorem on `innerCompiledVerifier`: neither hash function occurs in its statement. The
  hash is one random function; the request enters as a typed instance, made by the open parameter
  `buildInstance`, and the part of it that the open parameter `early` keeps stands in the first
  Fiat–Shamir query of the proof file's chain (and, where the protocol names a late round, the whole
  instance in that round's query; at the two IOPs there is none). How a typed query is written as a
  string is the open parameter `oracleCoding` (V4). So the theorem says nothing on which bytes bind
  a request.

**The four lookup tables.** `cp_verify` and `verify-on-bytes` compute the four tables and hold them
against the parameter file's 32 digest lines, where the file has them. Such lines are admitted only
with routed experts, and in `verify-on-bytes` only at profile 4; `cp_verify` takes no other profile
(read, in both sources; not run); every parameter file in the scope of the soundness theorem on
`verify` has them (`Johnson/Unfolds/TablesInScope.lean`); and in the Lean text no whole call without
them ends `YES` or `WITHIN LIMITS` (`OnBytes/Model/Stages.lean`; of both programs this rests on a
reading of their texts and is untested: `OnBytes/LIMITS.md`, points 15 and 19). There the second
hash function's resistance to collisions is what makes "the file names these tables" mean one set of
tables.

`innerCompiledVerifier` carries the tables as written data, compares nothing and checks no file at
run time: there the link to the file rests on the tables as they are written in the source, and on
nothing else. That the written tables have the digests which the file's lines hold is checked by no
theorem, and the same resistance to collisions is needed only for "names" to be unambiguous. That
the entries of the library's fixed tables (`tbRef`) under the four digests in Lean's own copy of the
full-size parameter file are those of the tables that the program computes at these files is tested
at every build, by Lean's evaluator (`Johnson/Top/Own/OwnStoredTablesRun.lean`, with the test file
that it imports). That is less than "the model's tables are the proofs' tables": it holds up to a
collision of the second hash function, and that file's head lists what lies under no digest. That
this copy is the public files that ship rests on checksums taken outside Lean.

This is one named place where Lean's typed verifier does less than the byte format's own text asks.
By `docs/format/FORMAT.md` a verifier that takes the four tables as data computes each table's
digest all the same and rejects if it differs from the file's line; otherwise its verdict is about
tables that nothing ties to the commitment.

Basis: proved (the four theorems at each size named above; the theorems of
`Johnson/Unfolds/TablesInScope.lean`) · by reading (the head of `Johnson/Flat/TwoSizes.lean`; the
statement of `innerCompiledVerifier_sound`; `OnBytes/Model/Stages.lean`; `docs/format/FORMAT.md`;
the programs' sources; no theorem says it) · tested (the known answers of BLAKE2b:
`Run/Blake2b/Test/`; the tables' entries: `Johnson/Top/Own/OwnStoredTablesRun.lean`, by Lean's
evaluator, which the kernel does not check) · not shown in this repository (the second
implementation in pure Python; the checksums taken outside Lean).

### V4. Three further claims stand outside the list

The 16 named hypotheses are not all that the theorem on `innerCompiledVerifier` needs before it
speaks of the programs. Three further claims stand outside the list, and none is proved.

1. That all typed hash queries can be coded into one hash function, one-to-one and onto, as the
   programs write them. With it go: that the programs hash a leaf and a node each as one block of
   the function, and that this is a coding that meets the conditions in `oracleCoding`'s type; and
   that the library's framing of those strings into BLAKE2b's calls (`Run.oBits`) is one-to-one. The
   coding is not shown, and the framing is shown only in pieces. At the two IOPs of
   `Johnson/Flat/TwoSizes.lean` the coding is the open parameter `m`, and no Lean term is written
   for it. By reading the byte format, one such coding can be given; none is written. That some
   coding exists is proved only with the axiom of choice, not by a construction, for interfaces
   whose instances, bodies of leaves and plain parts are countable (`exists_impl`,
   `Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean`): that is not the programs'
   coding.
2. That some IOP is the programs' (at the two IOPs, among others: that the programs are wired as the
   written wiring says).
3. That the model which the statement names is the integer model of the committed weights.

So the theorem on `innerCompiledVerifier` does not speak of the programs.

The theorem's inputs carry conditions in their types, which the list of named hypotheses does not
count: above all that coding (`OracleCoding`, `Rom/Family.lean`).

**One more departure** lies in the inputs at the two IOPs. They hold the digest of the public files
as a value that is fixed with the input, before the hash function is sampled (`cfg`, a field of
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize` and of
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize`, `Johnson/Flat/TwoSizes.lean`). In the
format that digest is itself an answer of the hash function, and the format's specification rules
out, for a model of the format, that it is fixed before the hash function is chosen. No false proof
is known to pass by it.

**Of `verify`.** The soundness theorem on `verify` leaves no such input open: its only hypotheses
are the three on the public files (V3), and the coding of the hash queries is a part of
`theDescription`. On the second claim there: that `theDescription` is the protocol of the C++
programs is not proved. On the third: [THEOREM.md](THEOREM.md), "Look first at four things". The
departure on the digest holds of the soundness theorem on `verify` only in part: in its model that
digest is an answer of the hash function (`VerifierAndGoals.readConfig`, `Ladder.lean`), but the
IOPs and the tests on the public files are written out in Lean with a 32-byte constant in the place
of the files' digest (THEOREM.md, "Look first at four things").

Basis: proved (`exists_impl`) · by reading (the types of `InnerCompilerInput`,
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize` and
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize`; `Rom/Family.lean`; `Ladder.lean`;
`docs/format/FORMAT.md`; no theorem says it).

### V5. Exact match only

The theorem on `innerCompiledVerifier` claims that every output token is the model's first choice.
No other acceptance policy is covered (L5).

Basis: by reading (the statement).

### V6. Runs of `innerCompiledVerifier` on files that the programs made

A user cannot rely on `innerCompiledVerifier` accepting an honest proof. As a whole it has run on
none of the three kinds of file that the programs write (a key file, a copy's file, a proof file): 0
of 3. At the two IOPs no theorem shows that it accepts anything.

At the two IOPs of `Johnson/Flat/TwoSizes.lean` (`innerCompilerInputFromDryRunAtFullSize`,
`innerCompilerInputFromDryRunAtSmallSize`) it has no compiled code, and no value of their open
parameters is given, so there it cannot run as a whole at all. `innerCompiledVerifier` takes typed
values. The compiler's checks that run under `Ask/` run one file at a time on parsed files, or the
small example's three in a row (`Ask/AllCompiledSmall.lean`); that they are
`innerCompiledVerifier`'s parts is shown by nothing.

That its IOP hashes what the programs hash is said by no theorem; by a reading of the two texts,
they differ at named places. So no run shows that `innerCompiledVerifier` accepts a file that the
prover makes, and the theorem on `innerCompiledVerifier` would hold as well of a verifier that
rejects everything (L9).

**Of `verify`.** All this is said of `innerCompiledVerifier` at the two IOPs. The executable form of
`verify` has run, inside Lean, on full-size proofs at synthetic weights. 109 calls of the reference
run were made over this repository's Lean files, and so were further calls of that run
([CHECK-RESULTS.md](CHECK-RESULTS.md)). Other calls were made on copies of the Lean files that
differ from this repository's. What was run, by kinds and counts, and the altered proof files that
it accepted are told on [THEOREM.md](THEOREM.md), "What has been run"; a proof file does not show
which program made it. What is known of whether `verify` accepts: L9.

Basis: by reading (the head of `Johnson/Flat/TwoSizes.lean`; `Ask/README.md`; the limits in the head
of `Johnson/Top/InnerCompiledVerifier.lean`; no theorem says it) · not shown in this repository
(that `innerCompiledVerifier` has no compiled code at `innerCompilerInputFromDryRunAtFullSize` and
`innerCompilerInputFromDryRunAtSmallSize`: Lean's own print, which is not here and was made on a
copy of the Lean files that differs from the files here).

### V8. What the theorem on `innerCompiledVerifier` rests on, and what it does not say

What the theorem on `innerCompiledVerifier` rests on is told in three places: the 16 named
hypotheses and the hash function (V3), the three claims outside the list (V4) and the statement on
codes (L15). Its Lean text is in `Johnson/Top/InnerCompiledVerifier.lean`.

**The statement on codes** (`Cb.BCHKS46At`) is proved in this library (`Cb/Bridge/`), from files
adapted from ArkLib and Mathlib (L15). It is no premise of the theorem on `innerCompiledVerifier`
itself. It enters where one of the hypotheses is proved at or beyond half the code's distance: in
the statements of the theorems at the two IOPs of `Johnson/Flat/TwoSizes.lean` and of the soundness
of the copy's file it stands as a hypothesis in the forms of `Johnson/Flat/TwoSizes.lean` itself. So
these forms carry five undischarged hypotheses, the four of V3 and this one. Further forms (names
ending in `_codes`, `Johnson/Flat/TwoSizesCodes.lean`) and the bounds on the closed check of the
copy's file (V13) apply its proof. If the statement were false, the forms that take it as a
hypothesis would say nothing.

Its proof runs through ArkLib's proof of a theorem of ArkLib's own and a comparison of that
theorem's bound with this library's. The cited paper's own form of the bound is not proved here.
That this statement is the bound which the written analysis uses, at this library's parameters,
rests on a reading of the two texts; no theorem says it (L15).

**The toy.** One toy IOP, Lean's own and not the programs', meets all 16 together (`two_holes`,
`Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean`). The hypotheses on the key file
and the copy's file hold there because their languages are all of the space. No oracle is read and
every round's error is 0 (`εs` = 0). Nothing is proved on whether `innerCompiledVerifier` accepts
anything. All marks are local, all depths of request trees are 0 and no part of an instance is named
late, so what sets this form of the compiled verifier apart is exercised by nothing there. Nothing
shows that an IOP of the programs' protocol meets the 16.

**What it does not say.** The theorem reduces soundness to the named hypotheses: it does not prove
it until the list is empty, and if one of them is false it says nothing. Each of the four, until it
is proved at an IOP of the programs' protocol, may turn out false there. Nothing says that
`innerCompiledVerifier` accepts anything: where the tests of the two IOPs fail (V10) it accepts
nothing, and the hypotheses on the key file and the proof file hold vacuously. No theorem shows that
`innerCompiledVerifier`, or its check of the copy's file, accepts any honest file: so each soundness
statement here would also be true of a verifier that rejects everything (V6; L9).

**The error** (`compiledSoundnessError`, `Johnson/Top/InnerCompiledVerifier.lean`) is a formula in
values that are stated beside the IOP, above all a bound on a round's error (`εs`) and an error term
for the step on the commitment (`εId`). At the two IOPs `εId` is an open parameter, so Lean gives no
number (V2).

What holds of `verify` at `theDescription`: V3, "Of `verify`".

Basis: proved (`two_holes`; `Cb.Bridge.bchks46At`; the forms at the two IOPs whose names end in
`_codes`) · by reading (the heads of `Johnson/Top/InnerCompiledVerifier.lean`,
`Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean` and `Johnson/Flat/TwoSizes.lean`;
the cited paper beside `Cb.BCHKS46At`; no theorem says it).

### V9. The named hypotheses

The 16 are the fields of one structure,
`VerifiableInference.OnPublicFiles.CompilerSoundnessConditionsWithMeaning`
(`Johnson/Top/InnerCompiledVerifier.lean`), which the theorem takes as an argument. Each is a
definition (`CompilerSoundnessConditionStatements.` with the field's name, as
`CompilerSoundnessConditionStatements.keySound`) with a docstring that says it in a sentence. They
are hypotheses, not axioms, so Lean's list of axioms shows none of them: "Lean's three axioms" says
nothing on whether they hold. A named hypothesis that is not proved is a limit of the theorem.

They are not all that the theorem needs: by its own file, parts of its input (`r.oracleCoding`,
`r.queryLayout`, `r.protocol`) hold conditions and instances in their types, and the further claims
of V4 stand outside the list.

**The words for a hypothesis's state** (in the table of the named hypotheses under "All limits, by
weight", and in V3). The state is at the two IOPs of `Johnson/Flat/TwoSizes.lean`, with parameters
open.

- *Proved*: a theorem of this library proves it. The eight theorems on which these states rest (V3)
  stand on `scripts/top-theorems.txt`, the list of names whose axioms the library's full check
  prints ([CHECKING.md](CHECKING.md)). The word does not rest on a check's result: what has been run
  of the check is told at [CHECK-RESULTS.md](CHECK-RESULTS.md).
- *Proved, with the statement on codes as a hypothesis*: `entrySound` alone (V3).
- *Holds by a definition*: it holds by unfolding definitions and says nothing of a cheating prover.
- *Holds by construction*: it holds by unfolding and by lemmas that hold of all data, and it too
  says nothing of a cheating prover.
- *Not proved*: no theorem of this library proves it.
- *May be false*: the hypothesis states a fact about the protocol that could turn out false. Proved
  at the IOP or not, it may be false at the programs' own strings: a place where the IOP departs
  from the programs. At some values of the open parameters such a hypothesis is false or says
  nothing. `keySound` and `proofSound` bear this mark; why: V10.
- *A definition to read*: the hypothesis defines what is being claimed. The reader must judge
  whether the claim is the one wanted, and no proof could settle that. `sound` bears this mark.

**`commitment`** is not proved of a given set of parameters (V11).

**`sound`** says that what the relation says is "the output tokens are the model's". It is not
proved for every claim. Read it as at risk: it holds vacuously where `buildInstance` refuses
everything. If `buildInstance` itself refuses every output that is not the model's, `sound` holds
whatever the relation is, and the theorem says nothing on the protocol (the head of
`Johnson/Top/InnerCompiledVerifier.lean`). At the full size, for one written claim, it is a theorem,
but only by moving the assumption into `keySound` and `proofSound` (`soundThreeFull_ref`,
`Johnson/Flat/ThreeFull.lean`, whose head says so).

What holds of `verify` at `theDescription`: V3, "Of `verify`"; of `keySound` and `proofSound` there:
V10; of `commitment`: V11.

Basis: proved (`soundThreeFull_ref`) · by reading (the structure
`CompilerSoundnessConditionsWithMeaning` and the docstrings of the definitions under
`CompilerSoundnessConditionStatements`; the heads of `Johnson/Top/InnerCompiledVerifier.lean` and
`Johnson/Flat/ThreeFull.lean`; no theorem says it) · computed (that the eight names stand on the
list: a search of its text).

### V10. What is known of `keySound` and `proofSound`

Under `keySound`, `proofSound` and "The tests of the two IOPs" the first paragraphs are said of the
two IOPs of `Johnson/Flat/TwoSizes.lean`, at which the key file's and the proof file's soundness are
open. The paragraph "At `theDescription`" that closes each of the first two says what holds at the
IOP of the soundness theorem on `verify`, `theDescription`.

**`keySound`** says that the key file's protocol, as written in this library, is round-by-round
sound. A user cannot rely on a false key file being refused except with the error that the theorem
names (an open parameter; no number is evaluated): that is the hypothesis `keySound`, not proved. It
may be false.

Nothing of the key protocol's soundness is proved for the two IOPs at the default setting's numbers.
One file (`Johnson/Top/H/KeyValues.lean`) fixes some counts of a key file's plan and says itself
that they are not shown to be the plan's. Beyond the chains no proof of the key file's soundness at
the two IOPs is known. Open; not shown false.

The bound in `keySound` also includes the factor 2 ^ `G.k.oneTime.binding.logLeaves` at the key
file's shared rounds. In the written layout of the hash queries the depth of the key file's request
tree is that of the key's chains, not 0; which depth the programs have is not said there, and no
number of the factor is evaluated (`Johnson/Flat/TwoSizes.lean`).

*At `theDescription`* that named hypothesis is a theorem: `keySound_holds`
(`Johnson/Goal/Conditions/KeyOpenHolds.lean`), at the full size, at public files in scope, where the
tests on the public files (`protocolDataWellFormed`) pass. That they pass is proved at the library's
written copies of the two stored sets of public files (`VerifierAndGoals.storedPublicFiles`,
`VerifierAndGoals.zGap`), in a side library (`AtFullSide/`), and is evaluated or unknown elsewhere.
`protocolDataWellFormed` reads no proof: a yes is no sign that `verify` accepts any proof. It is one
of the conditions on the public files under which the soundness statements hold (what is known of
acceptance: L9). The copies are Lean terms, and no theorem ties them to the files on disk (L69).
There the factor is 1 (`depthReqT_the`, `Johnson/Goal/Conditions/KeyDepthAtThe.lean`). The theorem
rests on the files under `ThirdParty/` (L15), and its file's own limits say where it may be empty.
It is one of three conditions beneath the soundness theorem on `verify` (`KeySound`, `EntrySound`,
`ProofSound`, `Johnson/Goal/Conditions/RowsAtTheRecord.lean`; they are not the three hypotheses on
the public files), not that theorem.

**`proofSound`** says that the proof file's protocol is round-by-round knowledge sound. A user
cannot rely on a false proof file being refused except with the error that the theorem names (an
open parameter; no number is evaluated): that is the hypothesis `proofSound`, not proved. It may be
false, and it is derived for neither of the two IOPs.

The decision of the key file's and the proof file's typed protocols tests that every word of a field
element in the three views, and of the key's seeds, is below the field's prime (`okView`, `okSeeds`,
`OnBytes/Maker/OkView.lean`; `decide3_no_of_word`, `decide3_no_of_item`, `decide3_no_of_factor`,
`OnBytes/Maker/OkViewLaws.lean`): where one such word is not below the prime, it rejects. Not tested
there: the words of the key's answers, what a round draws, and that the seeds are the table's. Two
further conditions are assumed without a test. One, that β (the challenge of `pscEnds`:
`OnBytes/Model/Merge.lean`, `OnBytes/K/Kc/Flat.lean`) is not zero, holds by the choice of the
challenge space in this format and is ensured by nothing in another (by reading, not
machine-checked; the same of a factor of a drawn seed: the head of `OnBytes/Maker/OkView.lean`). The
other, that the words of the OOD answers are below the prime, is tested there by nothing: behind a
parser that does not test them, nothing does. The verifiers that ship make the word test.

At the small example `proofSound` cannot be met by the small example's protocol at `claimsSmall`
(`Johnson/Flat/ClaimsSizes.lean`): the small example's programs prove another program. That is read
from the definitions; no theorem says it.

The typed verifier's verdict, computed on bytes, does not check the request leaf's salt length: its
strict test asks only "joined, or empty". A wrapper adds that test for runs made through it
(`verifyGuard`, `OnBytes/Maker/Page/GuardVerify.lean`); `cp_verify` holds that length by
construction of its read (by reading, not machine-checked); the theorem on `innerCompiledVerifier`
is untouched. That unchecked case in full, and a related one: L79.

*At `theDescription`* that named hypothesis is a theorem: `proofSoundAt_of_verify`
(`Johnson/Goal/Skeleton/SoundOfVerifyMore.lean`), at the full size, at public files in scope that
are read, where the tests on the public files pass; where these pass, and what their yes does not
show, is as told of `keySound_holds` above. At each set of public files in scope whose files are
read it is `ProofSoundAt`. As no set is in scope unless its files are read, the assembled
`ProofSound`, at every set in scope, is a theorem too: `proofSound_of_verify`
(`Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean`). As typed, it and `keySound_holds` speak of the
term from which `theDescription` is built (`dataAtFiles flashProveData Z`), with two fixed values in
the place of the verifier's two public readings, and name neither `verify` nor `theDescription` (the
definitions `KeySound` and `ProofSound`, `Johnson/Goal/Conditions/RowsAtTheRecord.lean`; that file's
head and the head of `SoundOfVerifyGoals.lean`). It rests on the files under `ThirdParty/` (L15),
and its file's own limits say where it may be empty. It is another of the three conditions beneath
the soundness theorem on `verify`, not that theorem.

**The tests of the two IOPs.** Each of the two IOPs has two tests, one for the key file and one for
the proof file (`GuardsPassFull`, `GuardsPassSmall`, `Johnson/Flat/WireAt.lean`). That they pass is
shown at no value of the open parameters. Where such a test fails, that file's decision says no at
every instance (at the full size: `runKFull_false`, `runPFull_false`), and the hypothesis on that
file's soundness then holds vacuously; that last step is read from the two lemmas, and no theorem
draws it. The five hypotheses that are left at the two IOPs are the four that are not proved and the
statement on codes: `Johnson/Flat/TwoSizes.lean` does not import that statement's proof and keeps it
as a hypothesis (V8; L15).

**Families that answer zeros.** Some families of typed checks in this library (`famOf`, `famX`,
`famXPd`, `famP`, `gJ`) are terms for statements only. At strings outside their domain they answer
zeros, and they are no verifiers. A family of this kind leaves a case unchecked as soon as its
verifier is given a typed value that Lean's own typing did not make, as an untrusted parser can. By
the comments of the files under `Ask/`, the runs of compiled checks that V6 tells stand under
`famRun` or under the wrapper that tests for that (`verifyGuard`); that has not been traced run by
run. For the runs of the executable form of `verify` ([THEOREM.md](THEOREM.md), "What has been run")
it has not been traced whether that holds: do not read it of them.

Basis: proved (the three theorems `decide3_no_of_…`; `runKFull_false`, `runPFull_false`;
`keySound_holds`, `depthReqT_the`, `proofSoundAt_of_verify`, `proofSound_of_verify`) · by reading
(the heads of `Johnson/Flat/TwoSizes.lean`, `Johnson/Top/H/KeyValues.lean`,
`OnBytes/Maker/Page/GuardVerify.lean` and `Johnson/Goal/Conditions/KeyOpenHolds.lean`; the comments
of the files under `Ask/`; `cp_verify`'s source; no theorem says it).

### V11. The named hypothesis `commitment`

A user cannot rely on a theorem for "the 32-byte commitment ID fixes the weights". That step is the
named hypothesis `commitment`: index binding at the key (a root with the OOD sample's seed and
answers) carries over to index binding at the commitment ID, which is the hash of the key's code. Of
a given set of parameters it is not proved. That the key in turn fixes the weights rests on the key
file's soundness (`keySound`, V10).

**What is proved beside it.** The programs' commitment ID hashes the OOD seeds: its string holds the
configuration's digest, the table's name, the seeds, the answers and a closing word.

- In general, a key's code that is one-to-one binds the commitment to the key's content in the plain
  sense, for an extractor that reads the commitment and the committer's log alone, with the error
  (tC + tP + 2)² / 2^256 (`Rec.commitmentBinds_of_code`, `Johnson/Top/FrontCommit.lean`).
- For the ID's string as the Lean text `verify-on-bytes` spells it, the key's code is one-to-one
  (`encId_oneToOne`, `Johnson/TypedOracleCompiler/Top/IdSeedAt.lean`).
- For `innerCompiledVerifier`'s own type of key the corresponding theorems (`idCodeSeed_oneToOne`,
  `commitmentBinds_seed`, `Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean`) each take two
  premises, that the answers' and the seed's spellings are one-to-one, which their own file shows of
  no concrete spelling; `Johnson/TypedOracleCompiler/Top/IdSeedAt.lean` shows them at the written
  spelling.
- Where the key's code spells the ID's string with the OOD sample's seed in it, at the library's
  extractor and error term, and if the spellings of an OOD sample's answers and of its seed are
  one-to-one, the hypothesis is a theorem (`CompilerSoundnessConditionStatements.commitment_idSeed`,
  `Johnson/Top/CommitCodeAtInnerCompilerInput.lean`). It is an implication whose premise, index
  binding of the scheme whose verifier holds the key, is shown at neither size.
- At the two IOPs of `Johnson/Flat/TwoSizes.lean` the hypothesis is met by setting five free fields
  of the structure of parameters, not by a proof about a given one (`commitment_withIdFull`,
  `commitment_withIdSmall`, `Johnson/Flat/CommitCodeSizes.lean`), with the public files' digest a
  constant in the code, which the format's own text rules out for a model of the format (the
  docstring of `CompilerSoundnessConditionStatements.commitment`,
  `Johnson/Top/InnerCompiledVerifier.lean`). The other three hypotheses are not proved, and are then
  premises at the changed parameters, and it is not shown that the structures of parameters
  (`InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize`,
  `InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize`) have any member (that file's limits).
- Wherever the step is proved, the key's code holds the OOD seed, and the proofs need it there: the
  extractor sees the commitment and the committer's hash queries and has no access to the hash
  function, so it cannot compute a seed that the committer never asked for (the same docstring).

**Of `verify`.** At `theDescription` no such step is left open. The soundness theorem on `verify` is
stated at the 256-bit commitment itself, and there it is index binding (`sound_iff`,
`VerifiableInference/Agreement.lean`; stated so at `verify`: `indexBinding_of_verify_at`; with the
extractor named: `indexBindingWith_of_verify_at`, `Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`).
The commitment and the committer's hash queries settle the weights that the extractor returns, at
exact match and at public files that are fixed beforehand; these need not be the weights that a
committer used.

**Of the programs.** Nothing here is proved of the programs, and no theorem says of the program that
commits that the 32-byte commitment ID fixes the weights.

Basis: proved (the theorems named above) · by reading (the docstring of
`CompilerSoundnessConditionStatements.commitment`; the limits in the heads of
`Johnson/Top/CommitCodeAtInnerCompilerInput.lean` and `Johnson/Flat/CommitCodeSizes.lean`;
`Fmt.publishedBytes`, `Fmt/Rules4.lean`, for the ID's string; no theorem says it).

### V13. The closed check of the copy's file

A user cannot rely on this bound for a whole claim: it is about one file of three. The closed check
of the copy's file (`verifyEntryFull`, `verifyEntrySmall`) has a bound in Lean with no unproved
hypothesis (`verifyEntryFull_copyBound`, `verifyEntrySmall_copyBound`,
`OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean`). It holds over a random hash function
(the assumption that BLAKE2b may stand in its place stays: V3), with the public files fixed before
the hash function is drawn, for every parser output.

**The figure.** At both sizes the bound is at most 2^-85 at 2^40 hash queries, with 32 of the 128
bits counted as proof of work, at one hash query for each try, at 6 of the 41 rounds at the full
size and at four rounds at the small one; without counting the proof of work, by arithmetic outside
Lean, about 2^-53 there. That is not 128 bits.

**What it covers.** It covers that file's own promise, not the whole claim, and says nothing without
the key file's part. It chains with nothing. It speaks of one maker, holds no commitment ID, and is
for the lax form of the link, made by a second form of the compiler (L21). That the closed check
accepts anything is shown by no theorem: if it never did, the bound would speak of nothing.

**What the figure bounds** is not the chance of a yes on a false file. It bounds one event
(`EntryFailFull`, `EntryFailSmall`, in the same Lean file), in which all of these hold: (a) the
check accepts; (b) two strings are read off the hash queries of whoever made the file, under the two
roots that the parsed file names, and the first decodes with its OOD sample, which determines one
table; (c) the second does not decode, with its own OOD sample, to a table that agrees with the
first's before the pads, or its OOD sample determines no table. Where (b) fails nothing is said:
that is why nothing follows without the key file's part.

**"No unproved hypothesis"** means here that the statement on codes is applied, not assumed: the
bound rests on that statement's proof in `Cb/Bridge/` and `ThirdParty/`. The library proves the
statement from files adapted from ArkLib and Mathlib (who adapted them, how they were compared with
their sources, and what Lean does not check of them: L15).

Basis: proved (`verifyEntryFull_copyBound`, `verifyEntrySmall_copyBound`; the figure at 2^40
queries: the same names with `_40`) · by reading (the comment on `verifyEntryFull_copyBound`; no
theorem says it) · computed (the figure without counting the proof of work: arithmetic outside Lean,
in the heads of `OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean` and
`OnBytes/TypedOracleCompiler/Slice/EntrySmallNum.lean`).

---

## Words that this page uses

The terms for the Lean verifier `verify`, its commitment, its key and its files:
[TERMS.md](TERMS.md). Entries V0 to V13 tell their own words. Beside these:

- **Settings.** The *settings* are the integer model's sizes and quantization parameters; they are
  public. `verify`'s system takes them from the public files as read
  (`VerifierAndGoals.settingsOfRead`), and these are fixed before the hash function is sampled.
- **Extractor.** A function that returns weights, or nothing, from a commitment and that committer's
  hash queries with their answers.
- **Picked by choice.** Taken by Lean's axiom of choice from a proof that such a thing exists. The
  picks are written out nowhere.
- **Table of scales.** A table of rescaling numbers, in the library's own types. The settings hold
  the model's sizes and the table's numbers, but for 72 that the model does not read, so many tables
  have the same settings (an argument, no theorem). Valid settings are exactly the settings of the
  *lawful* tables (`Scales.Lawful`, `Cm/Rel2.lean`).
- **Copies of the table.** The committer encodes all the weights once, in the first table, and then
  one or more further times, each in a copy of the table. The file with a copy's root and its link
  proof is the copy's file. A proof names one copy and works on it. Names in the Lean files call a
  copy a leaf; it is not a leaf of a hash tree.
- **Link.** A protocol, run once for each copy, whose purpose is to show that the copy holds the
  same weights as the first table. Its proof, the link proof, is stored in the copy's file.
- **Agreement.** Short for mutual correlated agreement, a property of an error-correcting code at a
  given radius: a bound on how many coefficients can make a combination of two words look close to
  the code although the two are not both close to it on the same positions. Proximity tests need
  such a bound.
- **The compiler.** A transformation that the library defines, of the kind known as BCS. It makes
  the interactive protocol non-interactive: a root of a hash tree stands for each oracle message,
  and a hash value for each message of the verifier. It has nothing to do with the compiler of the
  Lean language.
- **Typed query, string.** The compiler is analysed over several random oracles, each with its own
  type of input and of answer; some answers are long. To ask one of these once is a typed query. The
  statements (`Sound` and its kin) have one hash function, from bit strings to 256 bits, and a long
  answer is fetched block by block. One hash query puts one bit string to that function. This page
  counts hash queries in these strings. (On this page a call is a call of the prover or of a
  program.) So one typed query can be many strings.
- **OOD sample.** A part of a key, for a committed table: a seed (the OOD seed) with the answers to
  it (the OOD answers). In the interactive protocol the verifier draws the seed at random; the
  programs hash it from the table's root and public data. "Out-of-domain sample" is the literature's
  name. In the Lean the verifier draws a seed of a sample map and the prover answers with the linear
  functionals it determines; soundness counts the seeds at which two codewords of the list give the
  same answers. No definition requires the sampled functional to lie outside the evaluation domain,
  and a search of the library's text finds no such premise anywhere; the sending's soundness
  statement (`Cb/Ld/LdSend.lean`) does not use one.
- **Below, under, on its road.** A declaration lies below or under a theorem, or on its road, if it
  is used, at any depth, in the theorem's statement or proof.
- **The full check.** One run, with all its steps, of the library's own script, `scripts/check.py`
  ([CHECKING.md](CHECKING.md)).
- **The independent checker.** An independent proof checker, another program than Lean (nanoda:
  [CHECKING.md](CHECKING.md)). It reads a text that this project's own exporter, which is not in
  this repository, writes from the compiled declarations (L25).
- **Guard.** A theorem that guards against reading a statement as more, or as less, than it says.
  Most guards show that a theorem is not vacuous: that its conditions can be met, or that what it
  speaks of exists.
- **Vacuous.** Of a statement: true because its hypothesis is never met, so that it says nothing.
- **Trivially.** Of zero knowledge or index privacy: met by a prover that shows nothing.

## 1. What the soundness theorem on `verify` says

### The statement itself

**L38.** What is proved is the statement in Lean of the soundness theorem on `verify`,
`VerifierAndGoals.AtTheName.sound_of_verify_at`. A rendering of it in ordinary words, on
[THEOREM.md](THEOREM.md) or anywhere else, is a gloss, nothing more. Such a gloss does not go
without the limits that these entries tell: L1, L2, L4, L5, L7, L10, L11, L12, L15, L25, L27, L29,
L44; nor without "What it does not say" on that page. The statement:

`Johnson/Goal/Skeleton/SoundOfVerifyAt.lean`:

```lean
theorem sound_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1
```

`VerifiableInference/Statements.lean`:

```lean
/-- Soundness. There is one extractor such that, for every committer with at most `committerQueries`
queries to the hash function and every prover with at most `proverQueries` queries: the probability
that the verifier accepts output tokens that are not those of the model with the weights that the
extractor gives, from the committer's commitment and queries, is at most ε (committerQueries +
proverQueries).
The prover picks the prompt and the output tokens. If the extractor gives no weights, every accepted
proof counts as a failure. The committer passes its state to the prover, so the two may act as one
adversary. -/
def Sound (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries)
```

Three more things go with the statement:

- The prompt and the output are the prover's to name, and the committer hands its state to the
  prover.
- t is the sum of two bounds: one on the committer's queries on every path, one on the prover's at
  every state. A committer and a prover that share one budget of t queries as they go are covered at
  the most that the one can spend plus the most that the other can, so at 2 t at most: that costs at
  most one bit in the bound's first term and two in the second. `SoundOpened`
  (`VerifiableInference/Statements.lean`) and `NoTwoOpenings`
  (`VerifiableInference/MoreStatements.lean`) differ: there one adversary makes all the queries, and
  they are counted together.
- The theorem rests on the three axioms of Lean's core library, `propext`, `Classical.choice` and
  `Quot.sound`, and on no other. The last lines of its file make Lean print them at every build. A
  proof by compiled code (`native_decide`) would show there as a further axiom (`Lean.ofReduceBool`,
  with `Lean.trustCompiler`). By a search of the files' text no Lean file of the library has the
  word, and the script's step `words` rejects it.

The five binders of `sound_of_verify_at`, its three hypotheses among them, stand in its statement.
Other theorems of the library take theirs from a `variable` line above them, some by a line
`include` as well. So whoever copies one of these copies those lines too: an excerpt without them
shows a theorem without its hypothesis. `modelNextToken_eq_nextToken`
(`IntegerModel/Arrays/SameModel.lean`) takes two hypotheses so.

Basis: proved (the theorem; `modelNextToken_eq_nextToken`) · by reading (`Sound`;
`RandomizedAlgorithm.QueryBound`; the last lines of the theorem's file; the shared budget: an
argument) · computed (the bits, from `VerifierAndGoals.soundnessErrorInQueries`, `Ladder/Bits.lean`;
the search for `native_decide`) · tested (the axioms: Lean prints them at every build, and the
script's step `build` audits the axioms of every declaration, L24; over which Lean files a build has
been made: L88; what has been run of the full check: [CHECK-RESULTS.md](CHECK-RESULTS.md)).

### Whose weights

**L2.** The claim of the soundness theorem on `verify` (`sound_of_verify_at`) is about the weights
that the extractor returns from the commitment and the committer's hash queries, at the given public
files, not about weights that anybody has shown. That a commitment is to a given model is outside
the statements.

The extractor is a function of the commitment and the committer's queries with their answers. It is
not given the prompt, the output, the proof or the prover's queries. It returns weights or nothing;
if it returns nothing, every accepted proof counts as a failure. It is a rule defined with choice,
not a program: nothing shows that it can be computed, nothing bounds its running time, and nothing
says that any party has these queries. The public files are a parameter of it, and no theorem bars
one commitment from being accepted at two sets of public files, with other weights extracted at each
([GAPS.md](GAPS.md), gap 69). The statement of `sound_of_verify_at` says only that there is an
extractor; which forms of the theorem name the protocol's own extractor: [GAPS.md](GAPS.md), gap 77.
What it returns at a commitment that no committer written in Lean made is told by no theorem
([GAPS.md](GAPS.md), gaps 64 and 78).

No witness is extracted from the prover (here: the intermediate values of the model's run). This is
binding for the language, not knowledge soundness: the theorem does not show that the prover knows
the weights or ran the model. It covers any commitment, each on its own.

[THEOREM.md](THEOREM.md) calls the property by the name that its definition bears in
`ZKCP/Defs.lean`, index-binding knowledge soundness (`HasIndexBinding`), in its witness-free case
(stated so at `verify`: `indexBinding_of_verify_at`; with the extractor named:
`indexBindingWith_of_verify_at`; both in `Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`). The name
claims no more than this entry grants: where the extractor may be any function, the definition's
clause on the witness adds nothing (`indexBinding_iff_sound`, `ZKCP/Basic.lean`).

That the extracted weights are, up to an error, the weights to which the commitment can be opened,
and an honest committer's own, is proved of illustrative systems, not of the Lean verifier's own
system, whose committer returns one constant whatever the weights (L61); of the final system: L93.
Nothing follows for a commitment that nobody opens (L32).

So take the commitment from a source that you trust.

Basis: proved (the two forms at `verify`; `indexBinding_iff_sound`) · by reading (`Sound`; the
statement of `sound_of_verify_at`; that the extractor is defined with choice: the docstrings of
`LayoutsByPublicReading.extractor`, `Johnson/Top/InnerCompiledVerifierByPublicReading.lean`, and of
`keyOfCode`, `ZKCP/DigestKey.lean`; [THEOREM.md](THEOREM.md)). What has been run of the full check:
[CHECK-RESULTS.md](CHECK-RESULTS.md). The independent checker: L25. Tests that change the source:
L26.

### One commitment, one proof; a joint probability

**L4.** The soundness theorem on `verify` (`sound_of_verify_at`) covers one commitment and one
proof, and its bound is on "accepted and wrong", not on "wrong, given that it was accepted".

The two differ by the chance of being accepted at all: "wrong, given that it was accepted" is
"accepted and wrong" divided by "accepted". For a prover that is seldom accepted the first can be
near 1 while the second is tiny. So the bound says how seldom a cheating prover gets a wrong output
through. It does not say how far an accepted proof can be trusted: that also depends on who sends
proofs, and how many of them are honest.

N proofs handed in at once under one commitment cost N times that error, the error taken at the
whole list's hash queries; for proofs checked one after another no bound is stated
([GAPS.md](GAPS.md), gap 70). Several commitments: L19. The claim has one prompt and one output;
what follows for a batch of requests: [THEOREM.md](THEOREM.md), "What it does not say", 18.

Basis: proved (`soundManyProofs_union_of_verify_at`,
`Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`) · by reading (`Sound`; the statement of
`sound_of_verify_at`).

### Exact match only

**L5.** Exact match only. What the soundness theorem on `verify`,
`VerifierAndGoals.AtTheName.sound_of_verify_at`, claims of an accepted output is that every output
token is the model's first choice (exact match with greedy decoding). The theorem on
`innerCompiledVerifier` claims the same. Under these two no other acceptance policy is covered.
Exact match is a premise on the parameter file, which `verify` does not test
([THEOREM.md](THEOREM.md), "Look first at four things", 1; [GAPS.md](GAPS.md), 44). Another theorem
on `verify`, the theorem under a policy, has a tolerant policy of one kind alone, the clipped gap,
in the place of exact match. Its claim bounds a mean and a count, not each token.

**The theorem under a policy.** `VerifierAndGoals.AtTheName.soundUnderPolicy_of_verify_at`
(`Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean`; [THEOREM.md](THEOREM.md), "The theorem under a
policy: other acceptance policies") is the soundness theorem on `verify` without the premise of
exact match, with the claim `MeetsPolicy` (`Policy/Front/MeetsPolicy.lean`), at the policy that the
public files state, in the place of exact match. In the random oracle model, at all public files
that are in scope and are read, for every committer that makes at most a hash queries and every
prover that makes at most b, whatever state it is handed, with t = a + b: the probability that
`verify` accepts a prompt and output tokens while the protocol's own extractor returns nothing from
the commitment and the committer's queries, or returns weights under whose scores the output tokens
do not meet the policy, is at most `VerifierAndGoals.soundnessErrorInQueries t n`, where n bounds
the hash queries of the proof parser. The protocol's own parser makes one
(`VerifierAndGoals.theDescription_within`, `Johnson/Goal/Description/Description.lean`), so there
the bound is that of the soundness theorem on `verify`, `soundnessErrorInQueries t 1` (THEOREM.md,
"The error"). It counts proof of work (L12) and is no security level: it counts hash queries, not
time (L8, L11). The theorem takes no statement on codes as a hypothesis; it rests on the library's
proof of that statement (L15).

The policy is three numbers: the clip `C`, the bound `theta` on the mean cost, the limit `cap`. They
are three lines of the parameter file, one of the public files, which are fixed before the hash
function is sampled: a committer or a prover that picks the policy after its hash queries is not
covered by the theorem. No theorem ties a commitment to one policy, or to one set of public files
(L28; GAPS.md, 69). Public files in scope stay in scope under other policy lines exactly if 2^8 ≤
`theta` ≤ `C` < 2^32 and `cap` ≤ 1,024 (`LPFPol.inScope_iff_range`,
`Johnson/LPFPol/ScopeAtPolicy.lean`): these are the policies that pass this library's rendering of
the programs' tests on the three policy lines (`PolTests`, `Inst/Model/ProgTests.lean`;
`polTests_iff`, `Inst/Model/Scales.lean`) and have 2^8 ≤ `theta`. The output tokens meet the policy
under the weights' scores if the model has scores for them (`HasScores`) and (a) the costs of the
counted output tokens, each clipped at `C`, sum to at most `theta` times their number; (b) at most
`cap` of the counted output tokens cost more than `C`; (c) an output token that follows a full
window (the 1,025th token of prompt and output together) is the model's next token. A token's cost
is its logit gap + 2^8. The counted tokens are the output tokens inside the window of 1,024 tokens.

What goes with that theorem:

- What a client learns. Under a tolerant policy (an argument; no theorem) a client that can have
  outputs of its own choice proved, as often as it likes, can measure the model's scores by seeing
  what is served and what is refused. This theorem says nothing on it. No theorem of this library on
  hiding covers it (L54): the files under `Policy/` say nothing on hiding.
- The claim bounds a mean and a count, not each token: a counted token that costs more than `C` may
  be any token at all; of such tokens there are at most `cap`, and fewer where the mean binds. A
  counted token that costs at most `C` has a gap of at most `C` - 2^8, and of at most n (`theta` -
  2^8), where n is the number of counted tokens (`few_costly_of_meetsPolicy`); whoever picks prompt
  and output picks n.
- By the docstring of `logitGap`, a gap has the unit of the logits. In `MeetsPolicy` these are the
  given weights' own, and whoever makes the weights sets their scale: under weights whose logits
  barely differ every gap is small, so the same policy is strict for one model and loose for
  another.
- By the docstring of `MeetsPolicy`, the prompt's tokens are not scored: a reply that is cut into
  several outputs has a mean and a count in each, and what is scored in one is unscored prompt in
  the next.
- A policy can be empty of content. Clause (a) holds of every output as soon as `C` ≤ `theta`; if
  besides `cap` is at least the number of counted tokens, (b) holds too
  (`meetsPolicy_iff_of_clip_le_mean`). Such policies are in scope, (256, 256, 1024) among them
  (THEOREM.md, "Some policies in scope mean nothing"): the theorem is true there and says next to
  nothing. By the programs' text (no theorem says it), their whole verification call, where it names
  a policy, refuses a request with a counted token at which (a) and (b) both say nothing (this
  library's port of that test: `policyEmpty`, `OnBytes/Model/Config.lean`); the tests on the three
  policy lines alone (`PolTests`) do not. If that reading holds, this is a fact about the Lean
  verifier and not a limit of the programs.
- A second kind of policy bars nothing. `MeetsPolicy` itself puts no condition on the three numbers,
  and at valid settings, in an output that has scores, no token costs more than 2^8 + 8191 (144 ·
  2^(finalBits − finalShift) + 2560) + 1. So at every policy whose `theta` and `C` are both at least
  that number, whatever `cap` is and under all weights, clauses (a) and (b) hold of every output,
  and the claim says only that the model has scores for the output and that a token after a full
  window is the model's next token (`Policy.meetsPolicy_iff_of_gapCeiling_le`,
  `Policy/Front/MeetsPolicyIdleAtScales.lean`). By arithmetic that number is 19,345,962,753 at the
  largest difference that valid settings allow, 14; it lies below 2^32, the bound on `C` in scope,
  only up to the difference 11 (the next bullet).
- Nor do `PolTests` or a small `cap` show that a policy has content. The two exponents of the
  model's final normalization, `finalBits` and `finalShift`, are settings, and valid settings allow
  every difference `finalBits` − `finalShift` from 0 to 14. At a difference of at most 11 no token
  costs more than 2,436,593,409, which is below 3 · 2^30, under any weights. There every policy with
  2,436,593,409 ≤ `theta` and 2,436,593,409 ≤ `C` says no more than a policy of the second kind
  (`Policy.meetsPolicy_of_close_scales`, `Policy.exists_policy_of_close_scales`,
  `Policy/Front/MeetsPolicyIdleAtScales.lean`). One of them passes `PolTests` (by putting the
  numbers in): (`C`, `theta`, `cap`) = (2^32 − 1, 2,436,593,409, 0). The reference settings have the
  difference 14. There no policy with `theta` < `C` < 2^32 is of that kind: some weights and some
  output fail it (`Policy.TeethAll.every_output_at_meets_iff`, `Policy/Front/TeethAllChannels.lean`;
  the weights are made up).
- The claim is about the weights that the extractor returns, not about weights that anybody has
  shown, and nothing says that they are a sensible model. At valid settings, at the all-zero
  weights, every output meets every policy with 257 ≤ `theta` and 257 ≤ `C`, whatever `cap` is, if
  prompt and output are not empty, lie in the vocabulary and have at most 1,025 tokens together, and
  a token after a full window is token 0 (`meetsPolicy_zeroWeights`); the like goes for any weights
  under which the model has values and each row of logits is constant (an argument from
  `meetsPolicy_of_close_logits`, `Policy/Front/MeetsPolicyBounds.lean`). The extractor's definition
  has to be read too (L2). By itself the theorem bars nothing against a committer who commits to
  weights under which every output meets the policy: it means something only together with
  correctness of extraction at the same extractor and with knowing who made the commitment, which no
  theorem says. For one illustrative committer, a Lean committer that models one part of `cp_commit`
  and which no theorem ties to the programs' committer, that joining is proved
  (`Bind.Cpp.soundAtCommitted_own`, `Johnson/Bind/Cpp/SoundAtCommitted.lean`); no theorem shows that
  `verify` accepts any proof under such a commitment, and the further limits are told at L61.
- After a prompt of 1,024 tokens no token is counted, and the claim is exact match
  (`meetsPolicy_iff_of_fullPrompt`). Each output token is judged after the prompt and the tokens of
  the output that come before it.
- One kind of policy is covered, the clipped gap with the exponent 8: a token's cost is its logit
  gap + 2^8 (`policyKind`, `OnBytes/Model/Config.lean`, names it clipped-gap, and exact-match at its
  strictest lines). This library's port of the programs' verifier admits more in the same test
  (`policy`, `OnBytes/Model/HeadLayout.lean`): the exponent 7, and tables at which a token's cost
  also counts a negative log-probability (the kinds that `policyKind` names log-probability and
  another-table). None of these is covered. "Admits" is said of that one test on the parameter
  file's lines, not of a call. By the Lean text a whole call of that program under a table of the
  last kind is rejected on the policy before the proof is read: `cpPolicyHeld`
  (`OnBytes/Model/VerifyHeads.lean`) refuses wherever the parameter file's lines `sT` and `sh` do
  not meet `sT` + 4 = `sh`, and these are the kinds log-probability and another-table
  (`policyKind`). That test is left out where the request's length is no multiple of four or the
  file lacks one of the six parameter lines that it reads; by the comments there a later stage then
  refuses; no theorem says either. The exponent 7 with sT + 4 = sh is not refused by that test;
  nothing here says whether a later stage refuses it. No sampling seed or noise enters the scores.
- Soundness alone, for one commitment and one proof. A verifier that rejects everything is sound
  too. The line on completeness (L93) is at exact match alone: at another policy no theorem after
  hashing stands beside this one (before hashing, on requests whose output is the model's own: L90).
- The theorem names its extractor. A form with the extractor under "there is" is weak on its own: at
  policies with 257 ≤ `theta` and 257 ≤ `C` it is met by an extractor that always returns the
  all-zero weights, with a verifier that only tests the form of a request (an argument, no theorem:
  `Ladder.lean`, point 6 of its opening comment). Which forms at `verify` say only that an extractor
  exists: GAPS.md, 77.
- At valid settings the sizes are those of one architecture (1,024 positions, 48 layers, a
  vocabulary of 202,048 tokens: `settingsAreValid`). One shipped example is at the full size under a
  clipped gap that is not exact match, `examples/full-size-clipped-gap/`: what the library's reader
  returns at its written copy of these files (`VerifierAndGoals.zGap`) are valid settings and the
  policy (25856, 512, 1) (`VerifierAndGoals.valid_of_read`, `VerifierAndGoals.filesRead`); no
  theorem ties that copy to the files on disk.
- Clause (a) has the form of Token-DiFR's test ([CREDITS.md](CREDITS.md), section 9); (b) and (c)
  have no counterpart there. To meet (a) is not to pass that test: there the checker runs a model it
  knows and pools many outputs' tokens.
- By the head of the theorem's file, the limits of the soundness theorem on `verify` hold of it
  whole, but for "Exact match only". This page tells them on the verifier (L1), the model (L7), the
  extractor (L2), the public files (L28) and the joint probability (one commitment, one proof;
  "accepted and wrong", not "wrong, given that it was accepted": L4). Where one of the tests of
  `verify` on the public files fails, `verify` rejects everything and the theorem holds for that
  reason (THEOREM.md, "Its reach").

**Other statements with a policy.** On integers alone, the relations of the model's last segment
imply the policy's clauses (`Inst/Model/Head/PolicySound.lean`). For the whole model, for every
prime p with 2^61 - 1 ≤ p and every table with lawful scales and a policy with C, θ < 2^40 and cap <
2^16 (`LedgerRel.TableOK`, `Policy/Rel/LedgerRel.lean`): cells below 2^18 that meet the conditions
of the relation pair with the cost ledger, formed modulo p, show that the integer program at the
table runs and that the table's policy holds of its logits (`Policy.ledger_noWrap`); where the
program runs and that policy holds, the honest trace has cells below 129 and meets these conditions
(`Policy.ledger_honest`); and a request has a witness, strict or relaxed, exactly where the model's
own relation at that table holds of it (`Policy.ledger_lang`; all three:
`Policy/Rel/LedgerRelLaws.lean`; by its head that file's statements are on a relation, not on a
protocol).

Three limits of the three statements above (`Policy.ledger_noWrap`, `Policy.ledger_honest`,
`Policy.ledger_lang`). They speak of the table's own policy alone: none is stated for a policy apart
from the table's. A request holds 1,024 tokens, an announced token y, and two numbers r and e that
bound the covered positions t, r ≤ t < e (`Instance`, `Inst/Model/Program.lean`).
`Policy.ledger_honest` has the hypothesis that y = 0 where e < 1,024: of a request with e < 1,024
and y ≠ 0 it says nothing, and such a request has no witness, since the conditions ask that clause.
`Policy.ledger_lang` is for well-formed requests only: the relation on its right side has the
request's form in it (r < e ≤ 1,024; y = 0 if e < 1,024).

Guards and sizes. That some request is true under a policy, and that the relation is not everything,
is shown for the relation pair with the cost ledger by guards modulo 2^64 - 2^32 + 1, at the weights
and policies that they name (`Policy/Rel/LedgerGuards.lean`, `Policy/Rel/PosGuards.lean`). For the
like pair with the plain head and no policy (`Cm/TargetPRel.lean`), `Cm.target_p_guards`
(`Cm/TargetPLangsProofs.lean`) carries four of the eight facts on true requests of `Cm/RelTrue.lean`
to "has a witness", and a fifth has its like (`Cm/TargetPRelProofs.lean`); no theorem carries
`Cm.true_pos`, `Cm.true_unique` or `Cm.true_next` to that pair. `Cm/SegNumsSz.lean`, the file of
tools for the model's sizes, states no bound on the sizes of the model's segments (its head,
"Limits").

The definitions of the files of `Policy/` have not been independently reviewed (who wrote them:
L43). The script compares none of their statements with a stored copy:
`scripts/front-statements.txt` has no block for a theorem of `Policy/` (L24). No test that changes
the source has been run over this repository's files (L26).

Basis: proved (the theorems that are named) · by reading (`IsModelOutput`; the statements of
`sound_of_verify_at` and `innerCompiledVerifier_sound`; the statement of
`soundUnderPolicy_of_verify_at`, its file's head and `SoundUnderPolicyAtZ`; `SoundForWith`,
`InScope`, `readFiles`, `MeetsPolicy` and `HasScores`, with their docstrings; the opening comment of
`Ladder.lean`; the statements and heads of `Inst/Model/Head/PolicySound.lean`,
`Policy/Rel/LedgerRel.lean` and `Policy/Rel/LedgerRelLaws.lean`; the heads of `Cm/RelTrue.lean`,
`Cm/TargetPRel.lean`, `Cm/SegNumsSz.lean`, `Policy/Rel/LedgerGuards.lean` and
`Policy/Rel/PosGuards.lean`; `Cm/TargetPLangsProofs.lean` and `Cm/TargetPRelProofs.lean`; the Lean
text under `OnBytes/Model/`; the programs' source and the example's files, for the sentences on
these) · computed (the arithmetic on the costs; by a search of the files' text: the stored copy has
no block).

### Any prefix of the model's answer

**L37.** An output that counts as correct may be any prefix of the model's output under greedy
decoding, the empty one too; whether the model would go on after it is not said.

`IsModelOutput` (`VerifiableInference/Statements.lean`) asks of each output token that is sent that
it is the model's next token, and asks nothing beyond the last.

So it holds of the empty output at all weights: under the soundness theorem on `verify` an accepted
empty output is no false claim, where the extractor returns weights. The theorem under a policy (L5)
does count it as one, at exact match too: no empty output meets a policy
(`Policy.not_meetsPolicy_nil`, `Policy.meetsPolicy_exact_iff`,
`Policy/Front/MeetsPolicyGuards.lean`). What `verify` does with an empty output: L36. Check the
output's length yourself ([THEOREM.md](THEOREM.md), "Look first at four things", 3).

Basis: by reading (that definition and its docstring; the docstring of `IntegerModel.IsModelOutput`)
· proved (the two theorems that are named).

### What the verifier rejects outright

**L36.** `verify` builds a request only from a prompt and an output that are not empty and have at
most 1,025 tokens together, with every token, the padding's too (L3), below 202,048. Where no
request is built it rejects. So after a prompt of 1,024 tokens a request is built for one output
token and no more.

`Sound` (`VerifiableInference/Statements.lean`) does not say this; the docstrings of
`requestOfTokens` and `IntegerModel.requestOf` (`VerifiableInference/RequestOfTokens.lean`) say when
no request is built, and the protocol's builder, `Flat.buildReq` (`Johnson/Flat/LedgerClaim.lean`),
builds one just where `requestOfTokens` does (`buildReq_some`; `buildReq_of_built`,
`Johnson/Flat/BuiltOK.lean`). What is shown to be rejected outright: by `verify`, every claim at
public files out of scope (`VerifierAndGoals.theDescription_out`,
`Johnson/Goal/Description/Description.lean`); by `innerCompiledVerifier`, whichever IOP it is given,
a claim from which no request is built (`FlashProve.innerCompiledVerifier_no_build`,
`Johnson/Goal/Tie/DescriptionOfDataRefuse.lean`). That `verify` runs `innerCompiledVerifier` with
this builder is read off the definitions: no theorem says of `verify` itself that it rejects an
empty output. By its text `verify` also rejects a key whose code does not hash to the commitment
(`ZKCP.verifyDigestKey`, `ZKCP/DigestKey.lean`), and everything where one of its tests on the public
files fails ([THEOREM.md](THEOREM.md), "Its reach").

The empty output counts as the model's (L37), so a verifier that rejects it whatever the hash
function, the commitment and the proof cannot meet `Complete`, as that definition is written, at any
error below 1 (for every argument system: `not_complete_of_rejected`,
`VerifiableInference/NotComplete.lean`; [GAPS.md](GAPS.md), 39). What is known of whether `verify`
accepts: L9.

Basis: proved (the theorems that are named; `IntegerModel.requestOf_some`, `requestOfTokens_some`) ·
by reading (`requestOfTokens` and `IntegerModel.requestOf`, with their docstrings; `Sound`;
`verifyAt`, `Ladder.lean`; that the builder is `Flat.buildReq`: the proof of
`FlashProve.meaning_the`, `Johnson/Goal/Conditions/SoundAtThe.lean`, closes that equation by `rfl`;
`ZKCP.verifyDigestKey`).

### Ties, and where the model has no value

**L39.** Where several tokens have the largest logit, the model's next token is the lowest of them;
where the model has no value, no token is the model's.

The choice is the first arg-max, `firstArgmax` (`IntegerModel/Model.lean`).

An acceptance where the model has no value counts against the prover: `IsModelOutput`
(`VerifiableInference/Statements.lean`) asks "= some token" at each position of the output, and the
bound covers such an acceptance like that of any wrong output. By its docstring, at valid settings
`modelNextToken` (`VerifiableInference/ModelWeights.lean`) has no value exactly if there is no
token, if there are more than 1,024, if a token is 202,048 or more, or if a range condition of the
integer program fails at some position.

Basis: by reading (`firstArgmax`; `IsModelOutput`; `IntegerTransformer.model`; the docstring of
`modelNextToken`).

### Tokens are numbers

**L47.** What turns text into tokens, and back, is outside every theorem: a token is a natural
number, and the claim is about lists of numbers.

No tokenizer and no chat template is in any statement, and no way of choosing a token but the greedy
one (L5). By the head of `IntegerModel/Model.lean` the model function leaves out, among other
things, the vision part, the tokenizer, any choice but the greedy one, and the cache of keys and
values (L44).

Basis: by reading (`Token`, an abbreviation for ℕ; that head) · computed (a search of the Lean
files: "tokenizer" stands in that head alone, "chat template" nowhere).

## 2. The bound

### The bound mixes two units

**L10.** Inside the bound of the soundness theorem on `verify`, t is added to 1, for the proof
parser's query, and to an allowance for the verifier's own queries, most of them counted in another
unit: that sum is not a count of anyone's hash queries.

For t, a bound on the committer's hash queries plus a bound on the prover's (not a shared budget:
L38), `VerifierAndGoals.soundnessErrorInQueries t 1` (`Ladder/Bits.lean`) is

16 · T / 2^128 + (T + 2)² / 2^256, with T = t + 1 + 2^23.

From about t = 2^124 on it is above 1 and claims nothing. `sound_of_verify_at` has no condition on
the number of hash queries; its hypotheses are the three on the public files.

- t counts strings: a query is one string, whatever its length. A bound on queries holds on every
  path and counts every single query, repeated queries too. An adversary whose number of queries is
  bounded only on average is not covered.
- 2^23 is a fixed allowance for the verifier's own queries. Those of `innerCompiledVerifier` are
  counted in it as the compiler counts them, in typed queries, where a long answer counts once (in
  strings it is asked digest by digest). That the verifier's queries, so counted, stay within it is
  proved (`VerifierWithin`, a part of `g8bits_of_verify`,
  `Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean`). No theorem bounds the number of strings that
  `verify` hashes, so do not take 2^23 for the verifier's hash queries ([GAPS.md](GAPS.md), gaps 36
  (e) and 70 (c)).
- One query returns 32 bytes. How the real hash function's calls count in t:
  [THEOREM.md](THEOREM.md), "The error".

Basis: proved (`g8bits_of_verify`) · by reading (`soundnessErrorInQueries`,
`verifierQueryAllowance`, `VerifierWithin` and "Units" in the head of `Ladder/Bits.lean`;
`RandomizedAlgorithm.QueryBound`; `Sound`) · computed (2^124).

### The bound is a probability for a number of hash queries

**L11.** `VerifierAndGoals.soundnessErrorInQueries t 1`, the bound of the soundness theorem on
`verify`, is a probability that grows with t, the sum of two bounds on hash queries: "124 bits" is a
rate for each query, not the chance of a false accept and not 128, and from about t = 2^124 on the
bound claims nothing. One bound is on the committer's queries, the other on the prover's (L10). The
bound is never below about 2^-101. In round figures it is t / 2^124 + 2^-101: about 2^-84 at t =
2^40, 2^-60 at 2^64 and 2^-44 at 2^80 ([THEOREM.md](THEOREM.md), "The error"; [GAPS.md](GAPS.md),
gap 36).

- The figure for 2^64 queries must not stand alone: t counts the committer's queries too, every try
  at a proof of work is a query, and the bound is for one commitment, one proof and one call of
  `verify` (L4). One honest commitment or proof may itself cost many queries. The honest side of the
  final system stays within 2^48 hash queries (`RepliesFit`, L93). The illustrative committer of L61
  makes no key file and is counted as making 2^35 + 2 hash queries. Of one proof alone Lean bounds
  the hash queries of the hashed argument's general prover, whichever honest provers it is given,
  with limits on its searches for a proof of work that are the library's own choice: at most 8 +
  7,068,035,999,651 queries, about 2^42.7, in scope, where the tests on the public files pass
  (`FlashProve.queryBound_home`, `Johnson/Goal/Conditions/HonestAtHome.lean`).
- The bound counts proof of work (L12). The goals of `Ladder/Bits.lean`, at whose error the theorem
  is stated, have one level: none speaks of an error with the work not counted (that file's head).
- The 2^35 + 2 of `theCpp`'s illustrative committer (`Bind.Cpp.honest_count`,
  `Johnson/Bind/Cpp/SoundAtCommitted.lean`) is not a measurement. It is an upper bound that holds on
  every path; by the comment at `twinBudget` (`Johnson/Bind/Cpp/Defs.lean`) that committer calls the
  hash function about 2^33 times, at two queries a call at most.

So do not quote the library's bounds on the honest parties' queries as what a proof or a key costs.

Basis: proved (`honest_count`; `queryBound_home`; `RepliesFit`: L93) · computed (the figures, from
`VerifierAndGoals.soundnessErrorInQueries`; 2^42.7) · by reading (`soundnessErrorInQueries` and the
head of `Ladder/Bits.lean`; the comment at `twinBudget`).

### After an honest commitment: a weak bound

**L33.** `SoundAfterHonestCommitmentFor`, with its case `SoundAfterHonestCommitment`
(`VerifiableInference/MoreStatements.lean`), bounds a cheating prover after an honest commitment. It
is proved of an illustrative system with `verify` (`Bind.Cpp.soundAtCommitted_own`: L61). The bound
there is weak, because the honest committer's own hash queries count as if the prover had made them:
it is never below about 2^-88, where that of the soundness theorem on `verify` is never below about
2^-101. The constant committer of the Lean verifier's own system (a committer that returns one
constant whatever the weights, and so commits to nothing; the committer of the six theorems (L93) is
another: the one that `compile` makes (`Johnson/Face/Compiler.lean`), which encodes the weights and
hashes the key) meets the definition for every claim, so it is no test of a committer (L61,
"One-sided"). Of the definition:

- The probability is an average over honest commitments, that is, over the committer's randomness;
  it says nothing on a single commitment. That a given commitment was made honestly is outside the
  statement.
- The weights are fixed before the hash function is sampled. Whoever picks weights after looking at
  the hash function is not covered.
- One commitment, one proof. The prover is given the commitment and the committer's randomness. It
  is shown no honest proof: with the randomness it can make honest proofs itself, and the queries
  for that count in its own bound.

Basis: proved (`soundAtCommitted_own`) · by reading (`SoundAfterHonestCommitmentFor` and its
docstring; the figures: the head of `Johnson/Bind/Cpp/SoundAtCommitted.lean`).

### Several proofs, several commitments: weak bounds

**L19.** Beyond one commitment and one proof, the library defines two forms of soundness
(`SoundManyProofs`, `SoundSeveralCommitments`, `VerifiableInference/MoreStatements.lean`): for a
list of proofs that is sent at once, and for commitments that all come from one run of the
committer. Both bounds are weak: each comes from a union bound.

At `verify` the first is a theorem, at N times the error of one proof, the error taken at the whole
list's hash queries (`soundManyProofs_union_of_verify_at`; told whole: [GAPS.md](GAPS.md), gap 70).

- The prover sends all its proofs at once: it sees no decision before.
- Nothing is said on a list of proofs after an honest commitment.

The second is stated at `verify` by no theorem. A general lemma gives it of every system that is
`Sound` (`Sound.severalCommitments`, `VerifiableInference/SeveralCommitments.lean`): a committer
publishes a list of commitments, and a prover then names one of them and gives one proof under it.

- It multiplies the bound by the number of commitments, by a union bound.
- All commitments come from one run of the committer, and the prover starts after the last of them.
- A commitment that is not in the committer's list is not covered, and all commitments are checked
  under one set of public files.

So to rely on the first theorem, count every proof that is ever checked under the commitment,
accepted and rejected alike.

Basis: proved (the theorem; the lemma) · by reading (the two definitions' docstrings; the head of
`VerifiableInference/SeveralCommitments.lean`) · computed (nothing at `verify` on several
commitments, nor on a list after an honest commitment: a search of the Lean files' text for the two
definitions' names, which can miss a theorem).

### Random oracle, classical adversary

**L8.** Each soundness theorem of this library that speaks of a hash function, among them the
soundness theorem on `verify` (`sound_of_verify_at`) and the theorem on `innerCompiledVerifier`, is
a statement over a hash function drawn at random, a random oracle, with classical queries. So none
of them covers a structural weakness in the programs' real hash function (BLAKE2b), which takes the
oracle's place in a run, or a quantum adversary. Nor does any statement say that a function drawn
uniformly among all functions on byte strings of the format's lengths stands for the hash function
that the programs run; that identification is the random-oracle model itself. The programs use
BLAKE2b, a concrete function, and beside it the second hash function. What stands in the theorems as
a fixed function beside the oracle, and what is assumed of it: V3. In the soundness theorem on
`verify` too the second hash function is a fixed function. That theorem assumes no further property
of it, collision resistance included; that it may be treated as separate from the sampled function
is an assumption of the model, not a hypothesis of the theorem (V3, "Of `verify`"). The library
states two goals that ask for soundness whatever function stands in the second hash function's place
(`G7'`, `Ladder.lean`; `G7'bits`, `Ladder/Bits.lean`); neither is proved of `verify`
([GAPS.md](GAPS.md), 60). That `secondHashFunction` and `secondHashFunctionTree` compute the
format's second hash function is shown by known-answer tests alone (V3). Whether `verify` behaves at
the real hash function as at a sampled one, and the one constant beneath it that is a value of the
real hash function: [GAPS.md](GAPS.md), gap 51.

The further forms of the soundness theorem on `verify` are corollaries of `sound_of_verify_at` and
`soundUnderPolicy_of_verify_at`, and they say no more than these two do: every limit under "What it
does not say" on [THEOREM.md](THEOREM.md) holds of them too, and they prove nothing more beneath
`verify`.

Neither the soundness theorem on `verify`, with its further forms, nor the theorem on
`innerCompiledVerifier` covers the step from the random oracle to the concrete functions; it is the
usual heuristic of the random oracle model.

The committer and the prover are fixed before the hash function is sampled: in `Sound`
(`VerifiableInference/Statements.lean`) they are quantified outside the probability, which is taken
over the hash function and the random choices (`Prob`,
`VerifiableInference/RandomOracleModel.lean`). They learn of the function only what their queries
return. An adversary that is chosen with knowledge of the hash function, or that comes with advice
on it, is not covered. The model's hash function serves this one experiment: nothing is said of a
function that other programs or protocols use too.

Basis: by reading (`uniformHash`; `RandomizedAlgorithm`; `Sound`; `Prob`; of the soundness theorem
on `verify` and its further forms: [THEOREM.md](THEOREM.md); the programs' hash functions:
`docs/format/FORMAT.md`, R2.1 and R15.3).

### No sizes, no running times

**L13.** No theorem on `verify` bounds the size of a key file, of a copy's file or of a proof file,
what the verifier computes, or the running time of an extractor or a simulator.

The statements have no measure of either. An algorithm is a tree whose next step is any function of
what it has seen (`RandomizedAlgorithm`, `VerifiableInference/RandomOracleModel.lean`); the
extractor in `Sound` is any function, and a `Simulator` is three maps of any kind
(`VerifiableInference/Statements.lean`); a proof of the Lean verifier's system is a list of tokens
and five byte strings of any length (`FormBytes`, `Johnson/Goal/Tie/DescriptionOnBytes.lean`). What
is bounded of the verifier is a count of its queries, in mixed units (L10). The theorems on the
executable form speak of a term's value, not of whether or when an evaluation ends
([THEOREM.md](THEOREM.md), "The executable form, and how to run it").

The library does have theorems on sizes (`Compile/Batch/SizeO.lean`), but they are about the
compiler in general, and no other file names one of its theorems on sizes.

Basis: by reading (the definitions named; the statements in
`Johnson/Goal/Skeleton/SoundOfVerifyAt.lean` and `SoundOfVerifyForms.lean`) · computed (a search for
the names of the theorems on sizes: no other file names one of them; a search of the Lean files'
text for names that hold `sizeIVK`, `sizePrf`, `sizePair` or `SizeNums`: none under `Johnson/`,
`Ladder/`, `OnBytes/`, `E2E/` or `AtFullSide/`; a search by name can miss a theorem).

## 3. The verifier in Lean, the programs, the model

### A model in Lean, not the programs

**L1.** Every theorem of this library is about terms written in Lean. No theorem is about the C++
and CUDA programs that commit, prove and verify; none of these programs runs the Lean verifier
`verify`; and no theorem says that they run `theDescription`, the protocol that `verify` checks
(`Ladder.lean`, point 7 of its opening comment; [THEOREM.md](THEOREM.md), "In short", "The
programs"). Reading a statement tells you nothing about what the verifier program does.

What a Lean file models is not the released programs. Where a comment in a Lean file speaks of "the
implementation", what it says need not hold of them.

`verify` as typed cannot be executed: Lean marks it noncomputable. The command `lean-verify` runs
its executable form inside Lean. What is proved of that form, and what is not proved of a run of it:
[THEOREM.md](THEOREM.md), "The executable form, and how to run it"; [GAPS.md](GAPS.md), 45, 56
and 65. What `verify` tests can be read only from its definition and the definitions beneath it
(L43; [GAPS.md](GAPS.md), 28).

One text of this repository, `verify-on-bytes`, is a verifier written in Lean and lies in
`OnBytes/`; this repository builds no stand-alone program from it. It is another verifier. The
theorems of `OnBytes/Tie/` tie its Lean source to a compiled verifier of one chain (L22;
`OnBytes/THEOREMS.md`).

For what the soundness theorem on `verify` claims of an accepted output, a reading of its statement
and of the definitions under it suffices. Whether `theDescription` is the protocol of the cited
paper, of a technical report on this protocol that is not public (both: `CREDITS.md`) or of the
programs is said by no theorem, and no reading of the statement can establish it (L48). What has
been tested: [THEOREM.md](THEOREM.md), "What has been run". Where the two verifiers are known to
part: [THEOREM.md](THEOREM.md), "What it does not say", 12.

Basis: by reading (the opening comment of `Ladder.lean`, point 7; the sections of THEOREM.md and the
entries of GAPS.md that are named; the comments of the Lean files that point here; no theorem says
it).

### Parameters: where they come from, proof of work, and a kept row's random values

**L12.** The numbers of the protocol that `verify` checks (its codes, radii, numbers of opened
positions, bits of proof of work and lengths of salts) come from the public files: the library's
planner makes them from the parameter file's lines and the layout's shapes
(`OnBytes.Params.configure`, `OnBytes/Params/Configure.lean`). Every statement on `verify` is scoped
to one proof format and model size, the default setting's at full size: the stored layout and
parameter files, byte for byte but for eight numbers, with a lawful scale file
([THEOREM.md](THEOREM.md), "Its reach"; [GAPS.md](GAPS.md), 35). At other parameters nothing is
proved: `verify` rejects such files. The full-size numbers also stand written out in Lean
(`VerifiableInference.PlanWritten.proofSizedFull`, `Johnson/Desc/Ok/PlanWritten/SizedLit.lean`). By
that file's head they are a print of what the library's own planner makes, so they are no second
witness for it, and that they are what the planner makes of any files is proved nowhere. That the
planner makes of a file what the programs make of it is no theorem (L1).

- **Proof of work.** The bounds on soundness count proof of work on the challenges. At the rounds
  that draw positions, 20, 28 or 32 of one round's 128 bits are proof of work: 20 in a request's own
  rounds, 28 in the rounds that the requests of a batch share, 32 in the key file's and the copy's
  file's (`workQuery`, in `proofSizedFull`; the tests by name: L52). No such round reaches 2^-128
  without the work: without it these rounds stand at about 2^-96 to 2^-110 (added up by a program,
  no theorem). These are figures of single rounds. They are not the chance of a forgery, and they
  are not the bound of the soundness theorem on `verify`, which is stated whole, in hash queries,
  each try at the proof of work being counted as a query ([THEOREM.md](THEOREM.md), "The error"; the
  rounds one by one: [GAPS.md](GAPS.md), 36 (f)). To multiply a round's error by 2^-work is the
  random-oracle model's count; against the real hash function it is the usual assumption on the cost
  of grinding. The bound of the soundness theorem on `verify` counts the proof of work; none of its
  forms is stated with the work not counted (L11).
- **A kept row has as many random values as shown positions: no slack.** In the protocol that the
  programs run, a kept row (a row of an oracle message in a request's own rounds that later segments
  read) has 219 random values for the 219 positions of it that a proof shows: as many as positions,
  and none to spare. In Lean's written plan the two numbers stand side by side (`r := 219` and `t :=
  219`, in the group that the proof file's plan, `proofSizedFull`, names `link`; it is a group of a
  request's own rounds, not the link proof, whose sizes are `linkSizedFull`); of the programs they
  are what the verifier's own planning call gives at the default setting's full-size file. This
  bears on hiding, and no Lean statement names that number. The theorem of L91 is about the online
  prover as written in Lean, at the protocol that the planner makes of the public files, and it
  speaks of all that an honest verifier reads of that prover's oracle messages; that the rows there
  have the written plan's two numbers is proved nowhere (above). The result on the committed tables
  is about the committed tables, whose rows have their own number of random values, and covers no
  kept row (L62). The conditional theorem on index privacy has no such number in it (L64). The link
  proof, as written in Lean (L65), has no kept row. That 219 random values are enough, as a
  statement on that number, is argued on paper only; the argument is not machine-checked. The row is
  one example: as run, no main or mask row of any proximity test has slack ([GAPS.md](GAPS.md), the
  appendix on gap 15, (10)).

Basis: by reading (`configure`; the written plan, its head and its fields `workQuery` and `link`;
the statement of the soundness theorem on `verify`; that no Lean result covers a kept row's number:
the statements named at L62, L64 and L65; no theorem says it) · computed (the rounds' figures
without the work: [GAPS.md](GAPS.md), 36 (f)) · not shown in this repository (the verifier's
planning call; the argument on paper for a kept row's number).

### Hiding and soundness, object by object

**L14.** At the one proof format and model size that `verify` takes, Lean proves that what is shown
of the committed tables, within a budget of opened columns, has the same distribution whatever the
weights (Lean's encoder, fresh pads, full size, before any hashing). With fixed-message provers a
conditional theorem carries this past hashing, against any verifier, up to a stated error.
(Fixed-message provers: provers that send the same messages whatever the weights, and so show
nothing of them; at public files in use the protocol's honest provers are others: only where a
function that makes them refuses do they fall back on these.) That is proved for one request per
proof, not for batches, and of the paper's whole-key argument, not of the Lean verifier's own
system. No theorem covers the OOD answers as the programs make them (L62 to L64). For the key file's
and the request's provers as written in Lean: L91, and after hashing L93. The programs derive their
masks from a secret seed, which no Lean theorem covers. The theorems: the result on the committed
tables, `AtPublicFiles.AtFiles.tables_own` (`E2E/TablesAtOwnObject.lean`); the conditional theorem,
`OnBytes.WholeKey.wholeKeyPrivacy` (`Johnson/WholeKey/Main.lean`).

On soundness three objects are kept apart here.

- **`innerCompiledVerifier`.** The theorem on `innerCompiledVerifier`, a verifier written in Lean,
  holds under named hypotheses, and those on which soundness turns are not proved: it reduces
  soundness to these, it does not prove it. It is a theorem about every IOP (interactive oracle
  proof, as written in Lean). Two are given, one at each of the default setting's two sizes, as
  typed: the two IOPs of `Johnson/Flat/TwoSizes.lean`. In each the copy's file and the OOD sample's
  seed and code are values, the key and proof files are written in the library at open parameters,
  and the rest are open parameters. The bound is a formula in open parameters: no number; at some
  settings of the open parameters the statement says nothing. Not the shipped files' bytes: no
  theorem ties them.
- **`verify`.** The soundness theorem on `verify`, the Lean verifier, is stated at another IOP,
  `theDescription`. There no lemma about a step of the protocol and no conjecture on codes is
  assumed, and the error is written out ([THEOREM.md](THEOREM.md)). What this entry says of
  `innerCompiledVerifier` is not said of it.
- **`verify-on-bytes`.** `verify-on-bytes` (L22) is a Lean text, from which this repository builds
  no stand-alone program: no theorem on soundness is proved of what a program built from it accepts.

Beside the compiler with which `verify` is built the library has a further form of a compiled
scheme. The library has definitions for it, one lemma on types, and three statements on index
binding (`CompileK/RecScheme.lean`, `CompileK/RecBindSpec.lean`): `Johnson/RecCompile/Bcs.lean`
proves one (`rec_bcs`), and the other two are not proved. Even a proof of these three would be about
a verifier whose design, by the head of `CompileK/RecBindSpec.lean`, is not the technical report's
([CREDITS.md](CREDITS.md)); and no program is tied to it (L1).

Index binding is proved, under hypotheses, for the compiled verifier on which the theorem on
`innerCompiledVerifier` rests (`cmsRA_binding_at`,
`Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean`); what stays unproved there, among it the
commitment at one hash function and the laws of the answers' code, are named hypotheses of that
theorem ("Before the four groups", above; how far the hypothesis on the commitment is proved: V11).

For the interactive protocol the library has general theorems (`Hiop/RecMain.lean`), but they are
conditional. Nothing in the library shows that a protocol meets their conditions together, and at
`verify`'s configuration `rec_main_zk` (`Hiop/RecWhole.lean`), as typed, says nothing: clauses that
it asks fail there ([GAPS.md](GAPS.md), the appendix on gap 15, (9)).

Two theorems beside them (`rec_hvzk_whole`, `Hiop/RecWholeProof.lean`;
`Hiop.Seeded.whole_all_seeds`, `Hiop/Seeded/WholeProof.lean`) have their conditions met, beyond a
toy, by fixed-message provers alone. Applied to these provers they give the result on the committed
tables, told in this entry's first paragraph: the first with the index type cut to the matrices in
range (`AtPublicFiles.AtFiles.tables_atFiles`, `E2E/WholeViewAtFiles.lean`), the second without that
cut (`AtPublicFiles.AtFiles.tables_own`; [GAPS.md](GAPS.md), gap 15). Neither theorem is applied at
the protocol's own provers. What is proved of these goes by two sisters of the second: `form_laws`
(`Hiop/Seeded/FormProof.lean`), from which `Hiop.Seeded.whole_all_seeds` itself is drawn, gives the
whole view before hashing (`wholeViewFollows`, `Johnson/T3/WholeViewFollows.lean`; at the honest
provers, at public files in scope that pass the test: `zkOnServedRequests_inScope`,
`AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean`; L91); and `lifeSeededAt`
(`Hiop/Seeded/AtIndex.lean`) stands under `wholeKeyPrivacy` (by way of
`Johnson/WrapLaws/AtKit.lean`; L64, L93).

Basis: proved (`rec_bcs`; `cmsRA_binding_at`; the theorems on hiding named) · by reading (the
statements; the files named and their heads; that a thing is stated or proved nowhere, no theorem
says) · computed (a search for a proof of the other two statements on binding).

### What the results on hiding rest on

**L50.** Of hiding too, what is proved is each theorem's statement in Lean; the sentences in
ordinary words on these pages are a gloss (L38). A statement says of the weights only what the
definitions under it say. For the results on hiding (L62 to L65, L91, L93) these are, among others:
how the encoder lays a table from the weights and its random values (`OnBytes.Flat.codingHonest`,
`OnBytes/Flat/CodingHonest.lean`), what the whole-key argument's committer and prover draw at random
and send (`commitAt`, `argW`, `HonestSide`, `Johnson/WholeKey/Defs.lean`; the laws of their coins:
`RunLaw`, `SaltsLaw`, `Johnson/WholeKey/CoinLaws.lean`), and what a round hashes (`Head`,
`OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean`). For L91 and L93: the definitions named
there. These definitions are Lean's own, tied to no program (L1) and compared with the texts by
reading only (L48). They have not been read through as a whole, from the results' statements down;
for L62 to L65, L91 and, of L93, the corollary at every request and the field `zeroKnowledge` in its
two forms, the meaning of those that do not lie beneath the statements of the six theorems has not
been independently reviewed either (L66). No theorem of the library refutes a system against the
text of `ZeroKnowledge` or `ZeroKnowledgeOn` (what the library refutes, and against which
definitions: [GAPS.md](GAPS.md), 80). Over a build of this repository's files the independent
checker (that the compiled files that its passes read were that build's is known from a report
alone; Lean's own files were not compared with a list of checksums) has accepted the soundness
theorem on `verify` (`sound_of_verify_at`), with every declaration beneath it; the results of L62 to
L65, L91 and L93 are not among these, and for them, but for `sound`, `repliesFit` and
`refusedHandsOutNoProof` (L80), there is, over this repository's files, Lean's own kernel alone
(L25, L80).

Basis: by reading (the statements; the definitions named, which are not all that lie beneath them;
no theorem says it) · computed (that nothing refutes a system against the two texts: a search of the
files' text, [GAPS.md](GAPS.md), 80).

### The protocol in Lean and the protocol of the texts

**L48.** That `theDescription`, the protocol as Lean describes it, is the protocol of the texts that
it follows is a reading, not a theorem. The texts:
[CREDITS.md](CREDITS.md#the-texts-on-the-protocol). One of them, the technical report, is not in
this repository: a comparison with it is on paper. `theDescription` is written after the programs'
default setting, and the programs are not the protocol of that report: they differ
([GAPS.md](GAPS.md), 16). No program is tied to Lean's protocol either (L1).

Where a file renders a part of these texts, its comments declare the differences that its writers
saw. That a Lean definition says what a text says is in every case a reading, not a theorem. These
pages tell of no comparison of the whole of `theDescription`, clause by clause, with a written
specification. Only parts have been compared: (a) the encoder, with the format's pages (L62); (b)
what is hashed, with `cp_verify`'s log, which is not equal to the executable form's call for call:
for the rounds' challenges the form asks hashes that `cp_verify` never computed (the cause is seen
in the logs and by reading, and is no theorem: [GAPS.md](GAPS.md), 22); (c) verdicts, in runs
([THEOREM.md](THEOREM.md), "What has been run").

Basis: by reading (the library's comments; the pages named; no theorem says it).

### The model is the library's own integer program

**L7.** The model in the soundness theorem on `verify` is the library's own integer program: no
theorem says that it renders the arithmetic of any real model. Nor does one say what its five lookup
tables contain as a whole, or that the converted weights of a real model are valid. What the five
tables hold is known by recomputing them outside Lean; no theorem states it.

- **The function.** The model in the statement is `modelNextToken`
  (`VerifiableInference/ModelWeights.lean`), the field `nextToken` of `verify`'s system
  (`VerifierAndGoals.system`, `Ladder.lean`). It is `IntegerTransformer.model`
  (`IntegerModel/Model.lean`, a file without imports) at the settings, the weights and five fixed
  tables. The protocol's claim is written over another text of the program, of a committed matrix
  and a request (`Policy.IsTrueUnder`, `Policy/Rel/True.lean`). That the two speak of one model, at
  every lawful table of scales and every policy, is a theorem
  (`VerifiableInference.Meaning.meaning_nextToken`; at what the reader of the public files returns,
  `meaning_atFiles`; both in `Johnson/Goal/Meaning/NextToken.lean`). That theorem names no verifier.
  One of its steps is `modelNextToken_eq_nextToken` (`IntegerModel/Arrays/SameModel.lean`).
- **The sizes.** By the docstring of `hasModelSizes` (beside `modelNextToken`), nine of its sizes
  are those of Llama 4 Maverick's text model; the window of 1,024 positions and the rotary scale are
  this system's. No theorem ties the program to that model or to this repository's code for it.
  "Valid" tests sizes and ranges alone (L29). What is known to differ from the public model: L44.
- **The table of scales.** The model's quantization parameters, its table of scales, belong to the
  public settings, not to the weights. A fitted model's are made from its weights: some 17 whole
  numbers a layer (`LayerSettings`, `IntegerModel/Model.lean`). They are public, and no statement on
  hiding covers them or counts what they tell of the weights ([GAPS.md](GAPS.md), 54 (d)). At
  `verify` they are read off two of the three public files, the scale file and the parameter file
  (`VerifierAndGoals.readFiles`, `VerifierAndGoals.settingsOfRead`, `Ladder.lean`). No theorem ties
  a commitment to one set of public files, and so none ties it to one table (L28;
  [THEOREM.md](THEOREM.md), "Look first at four things", 2). The scales in the reference table are
  "one set of example scales of this project" (the docstring at `Inst/Model/Program.lean`); the
  file's head adds that they "may depend on Llama 2 7B and Llama 4 Maverick" (see THIRD_PARTY.md).
- **The reference table.** The library proves that a lawful table exists: its own reference table of
  scales (`Cm.lawful_sRef`, `Cm/Rel2Guards.lean`). Its file does not say that this table is fitted
  to any model: its numbers may depend on models of Meta's (`THIRD_PARTY.md`, "What depends on
  Meta's models"), and this library has no theorem that ties them to a file of the programs. That
  bears on `validSettings_exist` (`VerifiableInference/ModelGuards.lean`), whose witness is that
  table's settings, and on every guard at `referenceSettings`
  (`VerifiableInference/ModelGuardsAtReference.lean`). Its settings are the ones that `verify`'s
  system has at the library's written copies of the two stored sets of public files
  (`VerifierAndGoals.settingsOfRead_full`, `VerifierAndGoals.settingsOfRead_gap`,
  `Johnson/Goal/Files/FilesReadAtRef.lean`; these copies are Lean terms that no theorem ties to the
  files on disk: L69).
- **The real model.** No theorem shows that a table of scales fitted to a real model's weights gives
  valid settings, or that these weights, as quantised, are valid weights.
  - One finding on a table: a program that tests Lean's definition of a lawful table
    (`Cm.Scales.Lawful`, `Cm/Rel2.lean`) clause by clause printed "lawful" for the table of scales
    of a fit to the real model's public weights, in two runs on one scale file. Neither the program
    nor a record of the runs is in this repository. That the program tests Lean's definitions as
    they stand rests on a comparison of the texts and on the program's own tests. The finding is no
    theorem, it has not been independently reviewed, it says nothing of the weights, and it has not
    been carried on to "valid settings". "Lawful" does not say that a table is sensible (the head of
    `Cm/Rel2.lean`, "Limits").
  - A run of `cp_commit` at full size on the public weights, with a fitted table of scales, passed
    that program's own worst-case check; that the `cp_commit` of this repository does so is not
    shown. That check is not Lean's test of the settings, and the two have not been compared; nor is
    it any of the library's own worst-case checks (L27): no theorem relates it to one of these
    either.
  - By the word of a Python program of this project that mirrors the Lean checks, Llama 4 Maverick's
    public weights, at settings fitted by this project, of which by its word they are valid weights
    (`ModelWeights`), fail the first worst-case check (`PassesWorstCaseCheck`) and pass the
    least-bound check, with numbers made, as `leastBoundNumbersOf` makes them, from bounds that pass
    a test on such bounds that is defined in Lean (`stretchNumbersPassSmallerSideGramTest`,
    `IntegerModel/Bounds/SmallerSideGramTestOfStretchNumbers.lean`) and that the program runs in its
    own arithmetic. Lean theorems say that such numbers hold
    (`hold_of_stretchNumbersPassSmallerSideGramTest`, the same file; `leastBoundNumbersOf_hold`,
    `IntegerModel/Bounds/LeastBoundOfLength.lean`); so, if the program's word holds, the weights
    meet the premise of the completeness theorem at weights that pass a worst-case check
    (`theHonestPart_complete_where_some_worst_case_check_passes`, L93; the premise:
    `PassesSomeWorstCaseCheck`: the first worst-case check, or the least-bound check with numbers
    that hold; L27, L93). It is not a Lean evaluation, no theorem joins the program to Lean, and the
    program is not in this repository; each check was run once, and some margins are thin.
  - If the Python program's word holds, what the completeness theorem at weights that pass a
    worst-case check states of the model alone follows at these settings, from theorems that hold at
    any settings: the model has a result on every well-formed request, and every prompt that is not
    empty and whose tokens are all in the vocabulary has exactly one output of each length that fits
    which is the model's own. That the honest proof is accepted at these weights is not shown: that
    theorem asks that the public files be in use (`FilesInUse`), which is shown for the public files
    stored in this library, and not for those that belong to these settings. That these settings are
    valid settings is not shown either.
  - What would carry "lawful" and "an index", the library's notions, to "valid settings" and "valid
    weights": `settingsAreValid_iff`, `settingsAreValid_settingsOf` and `weightsOfIndex`
    (`IntegerModel/Arrays/OfIndex.lean`).
- **The whole window.** `Sound` does not ask that the program have a value on the whole window
  (`ArgumentSystem.IsModelOutput`, `VerifiableInference/Statements.lean`). The protocol's claim asks
  it, also of the tokens that fill the window after the checked positions; at `verify` the prover
  brings these (the field `twoSided` of `MeaningAt`, `Johnson/Goal/Meaning/NextToken.lean`;
  `TypedProof`, `Ladder.lean`). In the statements on completeness and zero knowledge the condition
  stands in `CanServe` (`VerifiableInference/CanServe.lean`; L27) or, where a statement is written
  in the model's result, in `requestResult` (`VerifiableInference/RequestResult.lean`), which
  `modelResult` and `requestOutcome` read.

Basis: proved (the theorems named) · by reading (the definitions, docstrings and heads named; no
theorem says it) · not shown in this repository (the two runs of the program on the table of scales,
and that they had one scale file, by checksum; the Python program's runs on the weights).

### Valid settings need not suit any model

**L29.** Valid settings need not suit any model: the test on the model's settings,
`settingsAreValid`, asks conditions on the numbers alone, sizes, ranges and relations among them. At
`verify` the settings are what the reader makes of the parameter file and the scale file
(`VerifierAndGoals.settingsOfRead`, `Ladder.lean`), and whatever the reader returns is valid
(`VerifierAndGoals.valid_of_read`, `Ladder/Ties.lean`). At public files in scope whose settings make
no sense the soundness theorem on `verify` holds all the same, of a model that nobody meant.

`settingsAreValid` and `weightsAreValid` are the tests, and `ModelWeights settings` is the type of
the arrays that pass the second (all in `VerifiableInference/ModelWeights.lean`). All valid settings
have one set of sizes (`hasModelSizes`, same file); the quantization parameters vary. Valid settings
make the table of scales lawful (`lawful_scalesOf`), and they are exactly the settings of the lawful
tables (`settingsAreValid_iff`; both in `IntegerModel/Arrays/OfIndex.lean`).

The test on the weights fixes sizes and ranges too, not the model. Lean's weights are whole numbers
in fixed ranges (`weightsInRange`, the same file as the tests): every weight but the embedding's
lies in -4,096 .. 4,095 (the range of a 13-bit signed number); an entry of the embedding lies in
-2,155,905,152 .. 2,139,062,143 (four signed bytes, at 2^0, 2^8, 2^16, 2^24), which is wider. The
width is a parameter of no statement. `layerWellFormed` does not test `softmaxShift`; its range (4
to 12) is `layerSettingsInRange`'s (ModelWeights.lean, inside `layerSettingsInRange`). No theorem is
about a weight file, in whatever width it stores its numbers, and no theorem says that a real
model's converted weights pass the test (L7). Some valid settings make every layer add nothing:
those of the lawful table `Cm.sIdle` (`Cm/Rel2Idle.lean`), at weights of 13 bits. That is an
argument written outside Lean, no theorem. The like of scale files in scope:
[THEOREM.md](THEOREM.md), "Look first at four things", 3.

So inspect the settings.

Basis: proved (`Cm.lawful_idle`; `settingsAreValid_settingsOf`; `VerifierAndGoals.valid_of_read`;
`lawful_scalesOf`; `settingsAreValid_iff`; that the quantization parameters vary:
`validSettings_two`, `VerifiableInference/ModelGuards.lean`) · by reading (the two tests and their
docstrings; `hasModelSizes`; `weightsInRange`; the heads of `ModelWeights.lean` and `Rel2Idle.lean`;
the statement of the soundness theorem on `verify`; no theorem says it) · computed (that no
statement has the width as a parameter: a search of the files' text).

### How the model differs from the public model

**L44.** No theorem of the library says how far the integer model's outputs lie from the
floating-point model's.

The head of `IntegerModel/Model.lean` lists what differs from the public model, Llama 4 Maverick's
text model, and what is left out. That head says that the distance is not said there, and that
docs/model.md reports no measurement of it. One measurement is told on `docs/limits.md`; it is no
part of any proof.

Basis: by reading (that head, from "What differs" through "What is left out"; the head of
`VerifiableInference/ModelWeights.lean`, "Limits").

### Completeness is stated only where CanServe holds

**L27.** The form of completeness that this library proves, of the final system, speaks only of
prompts and outputs that meet a side condition, `CanServe`, and whose output tokens are the model's
(`CompleteOn`, `VerifiableInference/Steps.lean`; L93), and so does the library's form of zero
knowledge on a set of requests in the theorems that conclude it of the final system
(`ZeroKnowledgeOn`, `VerifiableInference/MoreStatements.lean`; L18, L93). The final statement's
field `complete` (L93) does not name the condition: it is written in `ProofAcceptedWhere`
(`VerifiableInference/AtEveryRequest.lean`) and speaks of well-formed requests whose model result is
their claimed output, which is the same statement (`finalComplete_iff_completeOn`,
`Johnson/Face/Checks.lean`). Of `verify`'s own system these goals on completeness are stated:
`PackageComplete` (`Ladder/Package.lean`), `Complete` at all files in scope, which is not expected
to hold (the bullet "Not `Complete`" below), by itself and again as a part of `PackageBundle` (the
same file); and `G3'pol` (`Ladder.lean`): it names the condition too, and asks that every output be
accepted that can be served and meets the files' policy, the model's own or not, at the two named
sets of files. Neither form is proved of `verify`'s own system, nor is any of these goals, and no
theorem shows the condition at a real model's weights. What is proved of the final system (the same
protocol and the same verifier): L93. It matters because a verifier that rejects everything is also
sound (L9).

- **What is proved.** Of the final system: L93. Beside it Lean has a reduction: if thirteen named
  hypotheses hold at given public files, the system with `verify` as its verifier and a prover side
  given by parameters is complete on the requests that meet `CanServe`
  (`FlashProve.completeOn_last`, `Johnson/Goal/Conditions/HomeLast.lean`). The thirteen are shown to
  hold together only at idle provers, which stop at every verifier message, and at an error of at
  least 3, where a bound says nothing ([GAPS.md](GAPS.md), 52). `CanServe`
  (`VerifiableInference/CanServe.lean`) asks three things: every token is in the vocabulary, the
  output is not empty, and the model has a value on the whole window of 1,024 tokens: the first
  1,024 tokens of the list that consists of the prompt, then the output tokens, then token 0
  repeated. `CompleteOn` is on one proof under a fresh commitment. The weights, the public files,
  the prompt and the output are fixed before the hash function is sampled.
- **Not `Complete`.** `Complete`, as `VerifiableInference/Statements.lean` defines it, speaks of
  every output that is the model's, and the empty output is the model's on every prompt. It is
  false, for every error below 1, of every system whose verifier rejects one such request whatever
  the hash function, the commitment and the proof (`not_complete_of_rejected`,
  `VerifiableInference/NotComplete.lean`). That `verify` rejects one is an argument, no theorem (the
  docstring of `PackageComplete`, `Ladder/Package.lean`; [GAPS.md](GAPS.md), 39). No theorem says
  which conditions of `CanServe` are needed.
- **Lengths.** The three conditions of `CanServe` alone do not bound the lengths; at valid settings,
  with the output the model's, they imply a prompt that is not empty and at most 1,025 tokens
  together (`wellFormed_and_result_iff`, `VerifiableInference/WellFormedRequests.lean`).
- **Where a theorem shows it to hold.** All weights that a theorem shows by name to meet `CanServe`
  are made up. Where a theorem concludes `CanServe` with no premise on the weights, all layers of
  its weights are zero (`canServe_exists`, `canServe_atVotingWeights`,
  `VerifiableInference/ModelGuards.lean`), but for one set at the settings of the reference table of
  scales, in which the attention block of one layer computes (`canServe_atAttentionWeights`,
  `VerifiableInference/ModelGuardsAtReference.lean`). What computes in that set is not in the
  theorem's statement: it rests on comments and definitions. Every example that these theorems show
  has one token of prompt and one of output, but for that last one: 1,024 tokens of prompt and one
  of output. Weights at which the model has a result on every well-formed request: the bullet on
  them below. None of these theorems shows an acceptance (what is known of acceptance: L9).
- **At real weights: a count, no theorem.** At weights of the type `ModelWeights settings`, that the
  model has a value on the whole window means that every range condition holds at every one of the
  window's 1,024 positions. On each of some hundreds of windows of 1,024 tokens a run of the
  integer-model package (`integrations/vllm/integer_model/`) found that to be so, on Llama 4
  Maverick's public 4-bit weights (a third party's conversion to GGUF, which
  `examples/maverick/README.md` names; the run checked its five files by their sizes alone, not by
  their checksums), under a parameter file that is not in this repository. That the package which
  ran has the range checks of the package in this repository is not shown here. The parameter file's
  table of scales is the file whose SHA-256 `examples/maverick/expected.txt` gives for
  `config/KL.bin`, which the fit of `examples/maverick/run.sh` makes from the public weights (by one
  comparison, not shown here); its `policy.txt` was not compared. A window is a prompt of 524 tokens
  cut from WikiText-2 (`THIRD_PARTY.md` has that corpus), a stored or altered reply, then token 0.
  What the count does not show:
  - (a) The windows come from far fewer prompts than there are windows: they are not independent
    texts. About a dozen further passes, of a block of the run that was cut off, are not reported
    here.
  - (b) Whether the replies are the integer model's own was not counted, and completeness speaks
    only of output tokens that are the model's.
  - (c) It is the package's arithmetic, not Lean's evaluation. Lean has seven tests for its eight
    range conditions (the eighth has no test of its own). That the package's intervals are Lean's or
    narrower in all seven, and that the window's fill is Lean's, rests on one comparison of the
    package with a written account of what `CanServe` asks, not with the Lean files. That the two
    compute the same values rests on both following `docs/model.md`, not on a comparison.
  - (d) That the weights lie in `ModelWeights settings` was not tested as such: by the same
    comparison the package's loader checks bounds on every entry that are Lean's or narrower, and
    refuses the file otherwise; the arrays' sizes were not traced.
  - (e) The model's tables were not compared entry for entry.
  - (f) `settingsAreValid` at that parameter file was not tested.
  - (g) The parameter file as used was the run's own copy of that file with one line added, `temp
    256`. By the package's text the forward pass does not read that line (it enters the noise of
    seeded scores and the file's validation alone). It is not known whether Lean's reader takes a
    file with such a line, whether that file is in the scope of the soundness theorem on `verify`,
    or whether it is at exact match: no Lean program was given the file, and its lines `C`, `theta`
    and `cap` were not recorded.
- **Where it holds nowhere.** At the settings of the reference table (L7) there are also valid
  weights at which no prompt and output meet `CanServe`: at these weights no request can be served
  (`canServe_nowhere_atHaltingWeights`, `VerifiableInference/ModelGuardsAtReference.lean`). There a
  statement of completeness on `CanServe` says nothing, and one of zero knowledge speaks of the
  commitment alone.
- **Weights at which the model never fails.** At weights that pass the first worst-case check, or
  the least-bound check with numbers that hold (`PassesSomeWorstCaseCheck`,
  `VerifiableInference/Bounds/SomeWorstCaseCheck.lean`) the model has a result on every well-formed
  request (`modelNeverFails_of_passesSomeWorstCaseCheck`, the same file; `ModelNeverFails`,
  `VerifiableInference/ModelNeverFails.lean`; L93, the completeness theorem at weights that pass a
  worst-case check). Of that premise: its first arm is this library's own decidable test on
  settings, tables and weights; its second is a statement that numbers exist that hold together
  ("numbers that hold": each stretch bound that the least-bound check reads is at least 0, and no
  vector of whole numbers gets longer by more than that factor when it is multiplied with its
  matrix; which matrices, and what they are made from: `LeastBoundNumbers.Hold`,
  `IntegerModel/Bounds/LeastBoundCheck.lean`), and that with them a second test, the least-bound
  check, passes: a statement, not a test.
  - To pass the least-bound check is not enough: the test uses the numbers and does not test them,
    nor that they are not negative (the docstring of `PassesLeastBoundWorstCaseCheck`,
    `VerifiableInference/Bounds/LeastBoundNeverFails.lean`); at a small made-up model, with tables
    of its own, it passes with numbers that do not hold, at weights at which the model has no value
    on its one prompt (`control_leastBound_passes_with_zeros`,
    `control_leastBound_zeros_do_not_hold`, `IntegerModel/Bounds/LeastBoundCheckControl.lean`;
    `control_model_eq_none`, `IntegerModel/Bounds/LengthCheckControl.lean`). Neither check is
    `cp_commit`'s worst-case check (L7): no theorem relates either to a check that any program
    makes.
  - At all valid settings some weights pass the first check (`PassesWorstCaseCheck`,
    `VerifiableInference/Bounds/NeverFails.lean`;
    `VerifiableInference.Bounds.exists_passesWorstCaseCheck`): it is shown there of the weights with
    0 at every place, and at its widest of all weights whose layers' matrices are zero and whose
    embedding has every entry in -2^25 .. 2^25, the head matrix free, within `weightsAreValid`
    (`VerifiableInference.Bounds.passesWorstCaseCheck_of_zero_layers`,
    `VerifiableInference/Bounds/SomeWeightsPassAtValidSettings.lean`); layers of zeros compute
    nothing: at such weights the next token depends on the last token alone (that file's head); the
    weights of "Where it holds nowhere" do not pass it
    (`VerifiableInference.not_passesWorstCaseCheck_atHaltingWeights`).
  - At the library's written copy of the stored full-size files (L69), for all weights in which
    every entry of every matrix of every layer has magnitude at most 800 (the embedding and the head
    matrix are free; a weight of a layer may lie in -4,096 .. 4,095: L29), a theorem concludes of
    prompts what the completeness theorem at weights that pass a worst-case check concludes
    (`VerifiableInference.Compilation.complete_at_the_stored_files_at_weights_within_800`).
  - The weights that are shown by name to pass a check that gives the premise are made up, and no
    theorem says whether a real model's converted weights lie within the bound of 800. No theorem
    says whether a real model's weights meet the premise: the count told above under "At real
    weights" is of some hundreds of windows, and is no theorem.
- **Not hidden.** Whether a request meets `CanServe` depends on the weights and is not hidden. A
  range condition of the integer program can fail at a position after the output: `Cm.filler`
  (`Cm/RelTrueExp.lean`) shows that at made-up weights, for a window whose last token is 1; for a
  window filled with token 0, which is the window of `CanServe`, no example is proved (the docstring
  of `CanServe`). In `ZeroKnowledgeOn` whoever chooses the requests may know the weights and is the
  same in both experiments, and outside the condition nothing is said about what the honest prover's
  output shows (`VerifiableInference/MoreStatements.lean`).

It says nothing about the prover programs (L1).

Basis: proved (the theorems named) · by reading (`CompleteOn`, `ZeroKnowledgeOn` and the definitions
named, with their docstrings; the heads of the two files of guards; for the clause on zero
knowledge, the docstring of `canServe_nowhere_atHaltingWeights`; that no theorem says more) ·
computed (a search for `CanServe` in the library's Lean files) · tested (the count at real weights,
on the conditions told above) · not shown in this repository (that run and its parameter file; that
the package which ran is the package here).

### The compiler and the proof files differ in two places

**L21.** The library's general compiler, `Compile.Batch` (`Compile/Batch/`), and the format of the
programs' proof files put different things into a hash query in two places, by reading the two
texts; two more are not settled. Read "two places" as: at least two. So, beside L1, a statement on a
verifier that this compiler makes is no statement on what the C++ programs decide on a proof file;
the ties of `verify-on-bytes` end at such a verifier, `Compile.Batch.verifyOneProtocol` (L22;
`OnBytes/THEOREMS.md`). `innerCompiledVerifier`, and through it `verify`, is made by a second form
of the compiler's verifier side, under `OnBytes/TypedOracleCompiler/` and
`Johnson/TypedOracleCompiler/RecCompile/`, which is written otherwise at both places. No theorem
carries a statement from one form to the other (the head of
`OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean`). Of `verify` this entry says nothing more
([THEOREM.md](THEOREM.md)).

The compiler has the same outline as that format. A proof may serve a batch of requests, and then
some rounds are shared by all of them. No way of coding or parsing the files removes these
differences:

- A round of a proof file can hold several roots of hash trees. A round of the compiler holds at
  most one for each of its two parts.
- In the format, the leaf of the tree that binds the requests of a batch holds a salt and its place.
  In the library it holds the bare value.

Two more are not settled:

- The first shared round. In the library's code the Fiat–Shamir query of the first shared round
  (`Head.f4`) holds external roots, the commitments, and a query of a shared round behind the
  joining round (`Head.f5`) holds none (`Compile/Batch/Oracles.lean`). In the format, only the first
  such query holds the root of the first encoding of the weights. That the external roots in the
  library's first shared query are that root is shown nowhere (`Compile.Batch.recomputeChain`,
  `Compile/Batch/Verifier.lean`). What the library's query at this round means for the comparison is
  told on no page, and the reading under "Basis" was made on a copy of these files in which the
  library's code at this round differs from this repository's; what this bullet tells of the code is
  this repository's.
- Where the reply sits. (The like, of the two IOPs of `Johnson/Flat/TwoSizes.lean`: V2, "The
  reply".)

"Two places" counts what a query holds, not how it is spelled as bytes: no written coding spells a
query of a shared round behind the joining round (F5 in `Compile/Batch/Oracles.lean`) as the
programs' hash query. Such a query and a query F2 with an empty field `xl` have the same fields, so
a coding must tell them apart by the kind of round. Whether one leaf of a hash tree holds the same
things on both sides has not been compared.

The model's last segment. By a comparison by reading of the text of the programs' verifier (no
theorem; nothing was run; that the text which was compared is, in this part, the text of the
programs in this repository is not shown), at every policy that their verifier admits, exact match
among them, the programs run one head with nine families of lookups and, at each position, a cost
ledger. That head has the shape of `Inst/Model/Head/`, though not all of its numbers; exact match is
there a choice of numbers (L5).

Basis: by reading (the library's source, above all `Head` and `FbIn` in
`Compile/Batch/Oracles.lean`, `Compile.Batch.actOf` and `Compile.Batch.recomputeChain`; the head of
`OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean`; the format's page; the text of the
programs' verifier; proofs were not read; no theorem says it, and nothing was run) · not shown in
this repository (the text which was read at the first shared round: the library's code at this round
differs from it; that the text of the programs' verifier which was compared is, at the last segment,
the text of the programs in this repository).

### Lean functions on bytes, and `verify-on-bytes`

**L22.** No statement on soundness follows from the Lean functions on bytes in `Fmt/` and `Run/`,
and no theorem ties `verify-on-bytes`, the Lean text in `OnBytes/`, to `cp_verify`, the programs'
C++ verifier. What runs on the real files is the command `lean-verify`, which runs the executable
form of `verify` inside Lean ([THEOREM.md](THEOREM.md); `tools/lean-verify/README.md`). In `Fmt/`
and `Run/`, for small test files of toy protocols, a function that reads bytes is proved equal to
one of the functions that the compiled verifier applies (`Run.M1RunTie.vbs_A` and its five fellows,
`Run/M1RunTie.lean`; `Run.M2Tie.vbs_T`, `Run.M2Tie.vbs_F`, `Run/M2Tie.lean`).

Both sides of that equation are Lean functions; neither is a program of this repository. It is not
the whole verifier, it checks no key, and it stops before the protocol's own key file and proof
file. The toy protocols are rendered at one answer to an out-of-domain sample, as the files' heads
say. The programs' own files of three toys stand in the library as data, beside files of the
library's own making. No run shows that the functions of `Fmt/` and `Run/` pass the files that the
tools write for the toy with a key file and a copy's file (`OnBytes/Entry/RecordToyFiles.lean`):
`Key.check` and `Entry.check` of `OnBytes/` do, in tests. The programs' own files of the other two
toys, as far as the library holds them, are among those whose checksums the programs' own list in
this repository expects (compared by checksum; in one run the tools in this repository wrote these
two toys' files with these checksums). By their own comments, some 130 of the Lean files under
`Fmt/` and `Run/` were written or held against an edition of the byte format's page
(`docs/format/FORMAT.md`) that is not the one in this repository. That their renderings, tests and
known answers fit the page in this repository is not shown.

No file of this library computes the declared structure (`Declared`, `Decl/Declared.lean`: what is
public before any proof) from the public files. The values of that type in the library are made up
for tests (`Fmt/ParsedKnown.lean`, `Fmt/TestChainStm.lean`), or take the files as given and leave
the other fields at fixed values (`declaredOf`, `Fmt/TestRequestItem.lean`). A verifier is meant to
compute the structure from its own copy of the public files and never to take it as an input (the
head of `Decl/Declared.lean`, 4). By the same head the two theorems of `Fmt/ChainStmSmall.lean` that
take `Declared.entryFormOk` as a premise have no premise that ties the declared structure to the
public files, and a made-up one can pass that test.

What is proved of `verify-on-bytes`, and what is not, is told on that directory's own pages. Below,
"the program" is a stand-alone program built from that text; this repository builds none.
`OnBytes/README.md` has it in short ("What is proved"). `OnBytes/THEOREMS.md` says from which calls
each of its theorems starts, what the object at the road's end is, and at which parameter strings a
test in Lean accepts a file. `OnBytes/LIMITS.md` says what a passing result of the program is worth,
and where the program and the programs that it is compared with have differed. `GLOSSARY.md`
explains the terms.

Limits on that program:

- No theorem on soundness reaches a call that checks a real proof. So no theorem says what a yes of
  `verify`, `verify -key` or `verify -leaf` is worth (these are commands of this program, not the
  Lean verifier `verify` of [THEOREM.md](THEOREM.md)). No theorem bounds the chance that the program
  accepts a false file.
- The program is a different verifier from the library's "compiled verifier" (a term of the
  library's Lean theory: "compiled" there means made by the library's own compiler of protocols).
- No theorem ties the program, without hypotheses that are unproved, to the verifier of any
  soundness theorem of the library (`OnBytes/THEOREMS.md`). One tie of that kind is stated, from the
  exit status 0 of `verify-on-bytes` to `innerCompiledVerifier` at a general input, on the
  statements that its free parameter `Served` admits, at Lean's BLAKE2b in the sampled function's
  place, under hypotheses that are proved at no input and may be false
  (`OnBytes.K.exit_innerCompiledVerifier`, `Johnson/Top/TieInnerCompiledVerifier.lean`).
- The soundness theorem on `verify` speaks of that Lean function and its executable form, which this
  program does not run: it says nothing of this program, and these limits are not limits of it.
- The program follows `cp_verify`'s source text, so the two programs are not independent: where they
  agree, that is not independent evidence.

How `main` stands to the text of which that directory's theorems are stated: point 24 of
[OnBytes/LIMITS.md](OnBytes/LIMITS.md).

Basis: by reading (the statements and the files' own heads; of the files told below, those that have
the word "edition": three use it in another sense (`Fmt/M2Types.lean`, `Fmt/M2ParOfLaws.lean`,
`Fmt/Plan.lean`), and for the others the sentence around the word was read; `OnBytes/THEOREMS.md`;
no theorem says what is proved nowhere) · computed (the two toys' files against the programs' list
of checksums; that some 130 files hold "edition", most of them in one sentence with "the one that
ships" or "the page that ships": a search of their text) · tested (one run of the tools, built from
a copy of the sources that differs from this repository's, on these two toys; none of a build of
this repository's) · not shown in this repository (that run's output).

## 4. The commitment, and what soundness alone is worth

### What the commitment does not bind

**L28.** `verify`'s commitment is 256 bits. No theorem ties it to one set of public files or to one
policy, and it does not cover the copies of the table. It is the hash function's answer at the key's
code: a fixed byte string made from the key, which no two keys share (`LPFD.Full.code_told`,
`Johnson/Top/Fire/Code/NamedReal.lean`; the paper's code(k, dg_Z)), not an error-correcting code. By
reading, that code holds six numbers for the table's shape, the hash function's digest of the three
public files, the root of the hash tree over the first encoding of the weights, and that table's OOD
sample, seed and answers (`PV.EncId.encF`, `Johnson/Top/Fire/Code/Vals/EncId.lean`; the key:
`KeyRoot`, `Johnson/TypedOracleCompiler/RecCompile/FrontRoot.lean`).

- **The public files and the policy.** `verify` is given the three public files beside the
  commitment; the policy is three numbers of the parameter file. Their digest stands in the code, so
  one commitment would pass at two sets of files only with a collision of the hash function: that is
  a reading and an argument on paper, and no theorem bounds it. The soundness theorem on `verify`
  speaks of one set of files, fixed before the hash function is sampled; files that are picked after
  the hash function are not covered ([GAPS.md](GAPS.md), 5, 54 (f), 69).
- **The extractor.** It takes the public files as an argument, beside the commitment and the
  committer's hash queries (the field `extractor` of `Description`, `Ladder.lean`). Nothing excludes
  that one commitment, read under two sets of public files, gives different weights; no theorem
  shows that it happens ([GAPS.md](GAPS.md), 69).
- **The copies.** The key file's one-time proof and each copy of the table (its root, its OOD
  sample, its link proof and its number) are no part of the code: they travel in every proof and are
  the prover's (`OfflineLinkOnlineProof`, same file as `KeyRoot`). So the commitment binds neither
  how many copies there are nor which of them a proof names; what ties a copy to the first table is
  its link proof ([GAPS.md](GAPS.md), 10, 41).

So take the commitment, and the three public files with it, from a source that you trust, and check
the policy's three lines ([THEOREM.md](THEOREM.md), "Look first at four things", 1 and 2). Whose
weights a commitment stands for: L2, L32, L61.

Basis: by reading (the definitions named; that only a collision lets one commitment pass at two sets
of files: an argument on paper; no theorem says it).

### Opening a commitment

**L32.** The statements on openings bind only a commitment that somebody opens, and whether an
opening counts is a check that no verifier and no program does. To open a commitment is to name
weights and randomness. The experiment runs the argument system's own committer on them once more,
under the same hash function, and the opening counts only if it returns that commitment. That
committer is a mathematical object. Nothing follows for a commitment that nobody opens.

The four statements are definitions, general in the argument system (`SoundAndBinding`,
`SoundOpened`: `VerifiableInference/Statements.lean`; `BindsWith`, `NoTwoOpenings`:
`VerifiableInference/MoreStatements.lean`):

| definition | what it says |
|---|---|
| `BindsWith` | Whoever opens a commitment opens it to the weights that the named extractor returns. |
| `NoTwoOpenings` | Nobody opens one commitment to two different arrays of weights. |
| `SoundAndBinding` | The first, and soundness, for the same extractor, at one error. |
| `SoundOpened` | Soundness for a commitment that its maker opens. Its statement has no extractor, and the verifier is not given the opening. It follows from `SoundAndBinding` at twice the error (`soundOpened_of_soundAndBinding`, `VerifiableInference/Checks.lean`). |

How far they go:

- One argument system, and with it one set of public files. Nothing is said of a commitment that is
  opened at another system's committer, or at other public files.
- One opening in a run; two in `NoTwoOpenings`, which says nothing of two different randomnesses for
  the same weights.
- Binding is to the arrays of weights.
- The committer's runs inside the experiment are not among the adversary's hash queries: an error
  has to cover them.
- Nothing is proved about a program that makes commitments, or about files.

**What is proved of them.** Of the Lean verifier's own system, nothing: its committer is a constant
one: it returns 256 zero bits at all weights, so that `BindsWith` and `NoTwoOpenings` are false
there at every error below 1 (an argument on paper). `BindsWith` and `NoTwoOpenings` are proved of
illustrative systems. Each of these keeps `verify` and has a committer that is written in Lean and
tied to no program; none has an honest prover, and no theorem shows `verify` accepting a proof under
such a committer's commitment. `SoundAndBinding` and `SoundOpened` are proved at exact match of the
illustrative system `theWideDigits`, whose honest sampler is the constant 0
(`soundAndBinding_level_digits_of_verify_at`, `soundOpened_level_digits_of_verify_at`,
`Johnson/Goal/Skeleton/SoundOfVerifyMore.lean`), the first at about 124 bits per hash query and
never below about 2^-100, the second at twice that error. `BindsWith` and `NoTwoOpenings` are proved
of further illustrative systems, `Bind.Cpp.theCpp` among them (L61). Of the final system (the same
protocol and the same verifier, with the honest committer and prover that the compiler makes)
`SoundAndBinding`, `SoundOpened`, `BindsWith` and `NoTwoOpenings` are proved, at public files in use
(`FinalSoundAndBinding`; `bindingOf_value`, `AtFullSide/Face/FinalBindingAtTheValue.lean`; L93).
System by system, with each error: [GAPS.md](GAPS.md), 55; see also 10, 72 and 78. A system whose
verifier rejects everything meets `SoundAndBinding` too (L9).

Basis: proved (the theorems named) · by reading (the four definitions and their docstrings; the
constant committer: `Johnson/Goal/Description/Honest.lean`; that two of them are false of it: an
argument on paper; what no theorem says).

### One honestly made commitment in the experiment

**L42.** Four definitions, `ZeroKnowledgeOn`, `ExtractsCommittedWeights`,
`SoundAfterHonestCommitment` and `CompleteOn`, each have one honestly made commitment in their
experiment. The first three are defined in `VerifiableInference/MoreStatements.lean`, the last in
`VerifiableInference/Steps.lean`. Of which system each is proved: L18.

On hiding. `ZeroKnowledge` and `ZeroKnowledgeOn` say nothing of a second commitment to the same
weights, and nothing of renewing one. Lean has no statement on hiding for more than one commitment:
the conditional theorem on index privacy has one run of its committer too (L64); L93's lines are for
one commitment, and L91 speaks of one commitment's life and names no committer. The technical report
([CREDITS.md](CREDITS.md)) has a written proof that covers several commitments on four conditions
that no program checks; that proof is not machine-checked, and it is not settled.

On soundness a second commitment is nothing special. The soundness theorem on `verify` holds for
each commitment, whoever made it (L2). A list of commitments from one run of a committer: L19.

Basis: proved (the soundness theorem on `verify`) · by reading (the four definitions, with
`realExperiment`; `ZKCP.Gen.realExp`, `ZKCP/Gen.lean`) · not shown in this repository (the report's
written proof).

### Soundness alone says little

**L9.** Soundness alone says little: a verifier that rejects everything is sound too
(`rejectAll_sound`, `VerifiableInference/Checks.lean`). So read the soundness theorem on `verify`
beside what is known on whether `verify` accepts.

That `verify` accepts the Lean prover's proofs is proved in the random-oracle model: at public files
in use, at every well-formed request whose claimed output is the model's own result, `verify`
rejects the Lean prover's proof with probability at most 2^-40 (`FinalComplete`, a field of
`VerifiableInference.Compilation.theFinalStatementOneBitHolds`, equivalent to the line
`completeOnCanServe`; L93). At BLAKE2b no theorem shows an acceptance: there, that `verify` accepts
is tested by runs. Every proof that it has accepted was made on synthetic weights: no proof made on
a real model's weights has been put to it ([GAPS.md](GAPS.md), gap 57). 109 calls of the reference
run were made over this repository's Lean files, and so were further calls of that run
([CHECK-RESULTS.md](CHECK-RESULTS.md)). Other calls were made on copies of the Lean files that
differ from this repository's. By those runs (evaluated, not proved), at the two stored sets of
public files, at the real hash function, `verify` did not reject everything
([THEOREM.md](THEOREM.md), "What it does not say" and "What has been run").

At public files in scope that are not in use, and at BLAKE2b at all files but those that were tried,
the soundness theorem on `verify` may hold only because `verify` rejects everything
([THEOREM.md](THEOREM.md), "Its reach"; L69). Further statements that a verifier which rejects
everything meets: [GAPS.md](GAPS.md), 52 (a); the theorem on `innerCompiledVerifier`: V6, V8.

The system of `rejectAll_sound`, `rejectAll`, which has one value of weights, also meets
`SoundAndBinding` (`rejectAll_soundAndBinding`, same file); by an argument a verifier that rejects
everything meets `SoundOpened` too (both are defined in `VerifiableInference/Statements.lean`). What
would set a system apart:

- Completeness sets a system apart from the verifier that rejects everything. In the form on the
  requests that can be served (`CompleteOn`, `VerifiableInference/Steps.lean`, at `CanServe`,
  `VerifiableInference/CanServe.lean`) it does so only where `CanServe` holds (L27). What is proved
  of `verify`: L93; what else Lean has toward it: L65; [GAPS.md](GAPS.md), 52.
- By an argument, not a theorem, a bound on the verifier's hash queries sets a system apart from the
  scheme with empty proofs, whose verifier searches all indices and which is complete too (L35). Of
  `verify` no bound on its hash queries is proved (L35).

Such a bound is on hash queries, not on computation. What it does not rule out is in L41.

Basis: proved (`rejectAll_sound`, `rejectAll_soundAndBinding`; `theFinalStatementOneBitHolds`: L93)
· by reading (arguments, no theorems: on `SoundOpened`; on what sets a system apart) · tested (the
runs of the executable form of `verify`, of which the reference run's calls were made over this
repository's Lean files: [THEOREM.md](THEOREM.md), "What has been run").

### A system whose proof is simply the weights

**L41.** By an argument, and no theorem, a system whose proof is simply the weights and the
committer's randomness meets `Sound` (`VerifiableInference/Statements.lean`) and `CompleteOn`
(`VerifiableInference/Steps.lean`). Its commitment is the hash of a code of the weights and the
randomness. Its verifier hashes what the proof holds, compares the answer with the commitment, runs
the model at these weights and compares the output. An honest proof always passes, and an accepted
output that is not the model's at the weights which the extractor reads off the committer's hash
queries needs a collision or a guessed answer of the hash function.

A bound on the verifier's hash queries (L9) does not set a protocol apart from that system: a hash
query counts as one whatever its length, and no theorem bounds the size of a proof (L13). By the
head of `Ladder.lean` (point 7) it would meet every goal of that file and of `Ladder/Bits.lean`,
binding of the commitment and the bound on the verifier's own queries among them, if it is written
for the compiler.

What rules such a system out is zero knowledge: `ZeroKnowledge`
(`VerifiableInference/Statements.lean`), or `ZeroKnowledgeOn`
(`VerifiableInference/MoreStatements.lean`) on the requests that meet `CanServe`
(`VerifiableInference/CanServe.lean`). Neither is proved of the Lean verifier's system; of the final
system, which has `verify` as its verifier, the second is (L18). What is proved in other forms, of
the protocol and of the final system: L91, L93. And a result on zero knowledge rules that system out
only beside completeness of the same provers: provers that send nothing hide everything (L63, L64).

Basis: proved (`VerifiableInference.zeroKnowledgeOnCanServe`: L18) · by reading (arguments, no
theorems; the head of `Ladder.lean`, point 7; the definitions named; that `ZeroKnowledge` is proved
of no system with `verify`, and `ZeroKnowledgeOn` of no other than the final system: L18).

## 5. What else is proved

### What is proved, and what is not

**L18.** A definition in `Statements.lean`, `MoreStatements.lean` or `Steps.lean` (all in
`VerifiableInference/`) is not a theorem. The table says of which system each is proved. *`verify`'s
own system* is `VerifierAndGoals.systemOfRecord` at `theDescription` (`Ladder.lean`). Its honest
side is a constant one: a committer that returns one constant and a prover that hands over empty
files, whatever the weights (`FlashProve.fixedCommitterAndProver`,
`Johnson/Goal/Tie/DescriptionOfData.lean`). So a definition that reads the honest side can be typed
of that system, but has no content there. An *illustrative system* keeps `verify` and its extractor
and has an illustrative committer: one written in Lean beside the IOP, not the final system's (L61;
[TERMS.md](TERMS.md), table 3). What is proved of completeness and zero knowledge of the protocol,
at the honest provers written in Lean and of the final system, which has the same protocol and the
same verifier, with the honest committer and prover that the compiler makes in place of the constant
ones, is told at L88 to L93; the rows below say how far it reaches these definitions.

The same in the terms of the definition that the library follows, with every theorem by name and
file: [TERMS.md](TERMS.md), table 2 and its notes. Names that end in `_of_verify_at` are in
`VerifierAndGoals.AtTheName` (`Johnson/Goal/Skeleton/`). "In scope" stands for: at public files that
are in scope and are read.

| definition | of `verify`'s own system | of an illustrative system, or elsewhere | limits |
|---|---|---|---|
| `Sound` | Proved, in scope, at exact match: the soundness theorem on `verify`, `sound_of_verify_at`. | It is true too of a made-up system that rejects everything (`rejectAll_sound`, `VerifiableInference/Checks.lean`). | [THEOREM.md](THEOREM.md); L38, L9 |
| `SoundFor`, `SoundForWith` | Proved, in scope, for the claim that the output meets the files' policy, with the extractor named: `soundUnderPolicy_of_verify_at`. | | L5 |
| `SoundManyProofs` | Proved, in scope, at exact match, by a union bound: N times the error, at the whole list's queries (`soundManyProofs_union_of_verify_at`). | | L4; [GAPS.md](GAPS.md), 70 |
| `SoundSeveralCommitments` | Not stated by name. | It follows from `Sound` for every system, at the error times the number of commitments. | L42 |
| `SoundAndBinding`, `SoundOpened` | No content. | Proved of one illustrative system, `theWideDigits`, in scope, at exact match (`soundAndBinding_level_digits_of_verify_at`, `soundOpened_level_digits_of_verify_at`). The first is true too of the system that rejects everything (`rejectAll_soundAndBinding`). `SoundAndBinding` and `SoundOpened` are proved of the final system, at public files in use (`FinalSoundAndBinding`; `bindingOf_value`; L93). | L32, L61, L93 |
| `BindsWith`, `NoTwoOpenings` | No content: both are false of the constant committer at every error below 1 (by reading). | Proved of illustrative systems (`FlashProve.bindsWith_atOlder`, `FlashProve.noTwoOpenings_atOlder`, `FlashProve.G9_digits`, `Bind.Cpp.bindsAt`, `Bind.Cpp.noTwoOpenings_live` among them), each under its own condition on the public files, and of the compiled system at the Lean honest part, at public files in use (`bindingOf_value`; L93). System by system: [GAPS.md](GAPS.md), 55. | L32, L61 |
| `ExtractsCommittedWeights` | No content: it is false of the constant committer at every error below 1 (by reading). | Proved of one illustrative system, `theCpp`, in scope, where the tests on the public files pass (`Bind.Cpp.extractsCommitted`), and of the compiled system's committer, at public files in use, at 2^48 hash queries, about 2^-155 (`finalExtracts_value`; L93); of others only a form at each fixed choice of the committer's coins ([GAPS.md](GAPS.md), 55). | L61 |
| `SoundAfterHonestCommitment`, `SoundAfterHonestCommitmentFor` | It holds, for every claim, because the constant committer asks no hash query and the extractor then returns nothing (`Bind.Cpp.hollow_meets_join`): the form is no test of a committer. | Proved of `theCpp`, in scope: for the claim that the output meets the files' policy (`Bind.Cpp.soundAtCommitted`) and, at exact match, as defined (`Bind.Cpp.soundAtCommitted_exact`). | L61 |
| `Complete` | Not proved, and not expected to hold at an error below 1: it speaks of every request with the model's own output, and for some no proof is to be had, the request without an output token among them (an argument, no theorem: `Ladder/Package.lean`, its head and the docstring of `PackageComplete`). | Proved only of a made-up system that accepts everything (`acceptAll_complete`, `VerifiableInference/Checks.lean`). On the requests that can be served: the next row. | L27, L9 |
| `CompleteOn` | No content. | Proved of the final system at the Lean honest part, at public files in use, at the error 2^-40, on the requests that can be served: `FinalComplete` with `finalComplete_iff_completeOn` (`Johnson/Face/Checks.lean`); L93. Beside it a reduction, of a system with `verify` and a prover side given by parameters: from thirteen hypotheses to `CompleteOn` on the requests that can be served (`FlashProve.completeOn_last`). The thirteen are met together only at idle parameters (three provers that stop at every verifier message; made-up values for the rest) and an error of at least 3, which says nothing. | L9, L27, L65, L93 |
| `ZeroKnowledge`, `ZeroKnowledgeOn` | `ZeroKnowledge`: proved of no system. `ZeroKnowledgeOn`: proved of one system, the final system, on the requests that can be served (the next column). The first is typed as a goal (`VerifierAndGoals.PackageZeroKnowledge`, `Ladder/Package.lean`), which is proved of no IOP. | What else Lean has on hiding is stated in other forms and of other objects: the committed tables before hashing, the whole-key argument with fixed-message provers, the link proof before hashing, the protocol's honest provers before hashing (L91). Of the final system at the Lean honest part, which has the same protocol and `verify` as its verifier, `ZeroKnowledgeOn` on `CanServe` follows from one premise, `TermLeft` (`VerifiableInference.Compilation.served_at_T1`, `AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean`), and that premise follows from the two theorems on the IOP (L90, L91) and one inequality on their numbers (`termLeft_of_ends`, `AtFullSide/CompletenessAndZeroKnowledge/LinesAtFiles.lean`); at the Lean honest part and 2^-154 it is a theorem, at all public files in use (`termLeft_value`, `AtFullSide/CompletenessAndZeroKnowledge/OneBitAtHonestProversAndSettings.lean`). `VerifiableInference.zeroKnowledgeOnCanServe` (`AtFullSide/Face/TheSixLines.lean`) states the conclusion at all public files in use, with no premise beyond that: there is a bound that stays at or below 2^-154 up to 2^64 hash queries and 688,127 replies (`ZeroKnowledgeOn`'s own word for them is proofs; a reply: [TERMS.md](TERMS.md), table 6). The final statement's field on zero knowledge (L93), which follows from two of the six lines, is in another form, `ZeroKnowledgeBelowWhere`, with one bit for each request told to the simulator (its corollary: `ZeroKnowledgeShownBelowWhere`, with one label for each request told and shown); its proof goes through `ZeroKnowledgeOn` on `CanServe` of the same system (`zeroKnowledgeFollowsFromOn`, `VerifiableInference/AtEveryRequestFollows.lean`). No theorem carries either form back to `ZeroKnowledgeOn`: the statement that would carry the first (`ZeroKnowledgeGivesOn`, `VerifiableInference/AtEveryRequestGuards.lean`) is a definition without a proof. | L14, L62 to L66, L91, L93; the definition's own limits: L83, L84 |
| `CompleteSoundZeroKnowledge`, `CompleteSoundZeroKnowledgeOn` | No theorem concludes either of any system. | Three of the six lines (L93), `soundAndBinding`, `completeOnCanServe` and `zeroKnowledgeOnCanServe`, state the three fields of `CompleteSoundZeroKnowledgeOn` of one system at `CanServe`, the third for a bound that exists and stays at or below 2^-154 within its counts; no theorem puts the three together. Of the three fields of `CompleteSoundZeroKnowledge` the line `sound` states the first of that system; `Complete` and `ZeroKnowledge`: their own rows of this table. `FinalStatementOneBit` (`Johnson/Face/FinalStatementOneBit.lean`) is a structure of its own, no case of either. | L41, L93 |

Guards on the model and on the definitions:

| theorem | what it gives | conditions | limits |
|---|---|---|---|
| `validSettings_exist`, `validSettings_two` (`VerifiableInference/ModelGuards.lean`, as the next two lines) | Valid settings exist, also two different ones. | | L29 |
| `notModelOutput_exists` | Some output that is not empty is not the model's. | At all weights of any argument system. | |
| `canServe_atVotingWeights`, `modelNextToken_answers_one`, `modelNextToken_reads_weights`, `modelNextToken_reads_prompt`, `twoModels_serve_one_request_alike` | Further guards. | At all valid settings, at made-up weights whose layers are all zero. | L27 |
| `modelNextToken_reads_layer`, `modelNextToken_reads_earlier_token` (`VerifiableInference/ModelGuardsAtReference.lean`) | A layer counts, and an earlier token counts. | At Lean's `referenceSettings` alone (the settings of the library's reference table of scales: L7), at made-up weights. | That file's head lists what they do not reach. |

These four lines are guards: they show that the statements say something.

Basis: proved (each line's theorems) · by reading (the definitions; `fixedCommitterAndProver`; what
has no content at the constant honest side, and what is false of it; the docstrings in
`Ladder/Package.lean`; the guards' statements and docstrings) · computed (that `ZeroKnowledge`, the
two bundles and `SoundSeveralCommitments` are concluded of no system, and `ZeroKnowledgeOn`, with no
premise beyond the public files' being in use, of the final system alone: a search of the files'
text for these names and for the definitions that unfold to them).

### A scheme with empty proofs meets the definition

**L35.** To meet `ZKCP.IsZKCPArg` (`ZKCP/Defs.lean`: completeness, index binding and index privacy,
each with an error) says little by itself: for every relation over a finite set of indices, a scheme
whose proofs are empty meets all three clauses at small errors. That is a theorem, stated in the
form that names the extractor and the simulator and has the stronger privacy (`bf_main`,
`ZKCP/PlainTrivial.lean`, with its proof in `ZKCP/PlainTrivialProofs.lean`; the form:
`ZKCP.IsZKCPArgWith`, `ZKCP/Defs.lean`).

**The scheme.** The committer draws one of M + 1 salts and publishes as its key the hash function's
answers at K ≥ 1 strings that spell the index and the salt. The prover sends nothing. The verifier
searches all indices: it goes through all pairs of an index and a salt in a fixed order, asks the
hash function at each pair's K strings, stops at the first pair whose answers are the key, and
accepts if there is such a pair and the instance has a witness at its index. (A step of an algorithm
of `ZKCP/Defs.lean` is an arbitrary function, so it may decide that.) It is deterministic apart from
its hash queries. The extractor returns the index of the first pair whose strings stand among the
committer's queries with the key as their answers. The simulator publishes K uniform answers and
samples the hash function as it is asked.

**Its errors.** With n pairs and answers of λ bits: completeness, n / 2^(λK); index binding, t /
2^λ + n / 2^(λK) after t queries of the committer, whatever the prover asks; index privacy, t /
(M + 1) after t queries of the verifier, whatever the number of proofs. These are small where M is
large and K is chosen large enough for n. Its extractor fails on honest keys with probability 0
(`bf_E`), and under an honest key it accepts an instance that is false at the committed index with
probability at most n / 2^(λK), whatever the prover (`bf_W`; both in `ZKCP/HonestKeyVerBf.lean`). So
neither correctness of extraction nor soundness after an honest commitment sets a protocol apart
from it.

**What sets a protocol apart.** The definition bounds nobody's work, and the size of no key or
proof. A bound on the verifier's hash queries does set a protocol apart: this verifier asks up to K
· n strings (`bfV_qb`, same file), and where an instance is true at one index and false at another
that has the same public parameters and a true instance of its own, every bound q on its queries has
1 ≤ 2n / 2^(λK) + 2q / (M + 1) (`bfV_lower`, same file). Of `verify` no bound on its hash queries is
proved. What is proved counts typed queries: at most 2^20, at all public files
(`VerifierAndGoals.AtTheName.count_the`, `Johnson/Goal/Conditions/RowsAtTheRecord.lean`); no theorem
carries that count to hash queries ([GAPS.md](GAPS.md), 36 (e), 70 (c)). That a call of its
executable form ends is seen in runs ([THEOREM.md](THEOREM.md), "What has been run").

No scheme of this protocol is shown to meet the three clauses. Of `verify`, index binding is proved
([THEOREM.md](THEOREM.md), "The formal name, and how the theorem fills the definition in");
completeness and index privacy in this definition's form are not (L9, L61 to L66; in other forms:
L93). The like for the statements of `VerifiableInference/Statements.lean`: L41; [GAPS.md](GAPS.md),
39 (f).

Basis: by reading (the definitions of `ZKCP/Defs.lean` and their docstrings; that no theorem bounds
`verify`'s hash queries: the head of `Ladder/Bits.lean`, "Units") · proved (`bf_main`; `count_the`)
· tested (the runs: [THEOREM.md](THEOREM.md), "What has been run") · not shown in this repository
(what the scheme does under an honest key, and the bound on q).

### Hiding for batches: a definition, and no theorem on the protocol

**L49.** Nothing on hiding is proved for batches of requests, and batches are what the programs
serve. All that Lean has on hiding (L62 to L65, L91, L93) is for one request per proof. What a
client learns from a proof about the other requests of its batch no theorem says (L64, "One instance
in each proof"; [THEOREM.md](THEOREM.md), "What it does not say", 18). Soundness is another matter:
the statement of the soundness theorem on `verify` is of each request of a batch by itself, and its
error has no factor for a batch of up to 64 requests ([GAPS.md](GAPS.md), 29); in scope, where the
public files pass the verifier's own tests, the tree that binds a batch's requests has depth 6, so a
batch has at most 64.

The library has a definition of index privacy with batches (`ZKCP.Gen.HasIndexPrivacyWith`,
`ZKCP/Gen.lean`; on a range of indices `ZKCP.Gen.PrivacyOn`, `ZKCP/OnRange.lean`). The conditional
theorem on index privacy is stated in it, at batches of at most one request (`Spec.wholeKeyPrivacy`,
`Johnson/WholeKey/Statement.lean`). At larger batches it is not stated of this protocol, and several
requests in a proof need a new statement, not a corollary (L64).

The limits of the definition with batches apply to every theorem that concludes it: (1) one honestly
made key; (2) all batches under it count, whoever's, empty ones too, up to N in all; (3) a bound on
the entries of a batch, every one true, the others' too; (4) which entries are own is fixed when the
batch is named (somebody who gets hold of a further entry's proof afterwards is not covered); (5)
the number of batches, their order and where the run stops are given; (6) nothing on a second key
for the same index; (7) the definition is stated in this library, not in the cited definition, which
has no batches (what it follows: [CREDITS.md](CREDITS.md), "Further work").

Basis: by reading (the definition and its comments; the statement of `Spec.wholeKeyPrivacy`) ·
computed (that the definition is stated of this protocol at batches of one alone: a search of the
files' text under `E2E/` and `Johnson/` for its two names).

### The prover picks what is claimed

**L3.** The prover picks what is claimed: in the soundness theorem on `verify`, the prompt and the
output tokens. A yes is about the prompt that was handed to the verifier.

`verify` takes the prompt and the output as arguments and builds the request itself: the range of
checked positions starts at the prompt's last token and ends with the output's last, and all tokens
of the prompt and the output come from the claim. So the prompt is taken as given, and exactly the
output tokens are checked. Only the filling behind the output is the prover's. The proof brings a
padding (the "further tokens" of `TypedProof`, `Ladder.lean`) that stands behind the output in the
window of 1,024 tokens; the claim does not depend on it: the soundness theorem on `verify` and the
theorem under a policy (L5) judge each output token by the model run on the prompt and the output
tokens before it alone, and a theorem leads there from the padded request, for every padding
(`Policy.meetsPolicy_of_isTrueUnder`, `Policy/Front/TrueUnder.lean`; at the protocol's own builder,
`FlashProve.meaning_the`, `Johnson/Goal/Conditions/SoundAtThe.lean`). The range conditions are asked
at the padding's positions too, so a padding can make a request unprovable, never a wrong output
acceptable beyond the theorem's bound.

The advice below is about what a user hands to the verifier program, and no theorem says that this
program builds the request as the Lean verifier does (L1). A caller's request file holds the whole
window and names the range itself, by two numbers: an acceptance says nothing about the tokens up to
and including the one at the start of the range, and at each position in the range it is the next
token that is checked. In Lean the proof brings the padding behind the output; in `cp_verify`, the
programs' verifier, the caller's request file does. The Lean verifier's command reads the claim off
the same file, by functions that stand under no theorem, and lays the tokens behind the range into
the proof (`PV.Program.claimOf`, `PV.Program.formOf`, `Johnson/PVR/Program.lean`;
[GAPS.md](GAPS.md), 37). The Lean theorem holds for every padding.

So build the request yourself from the tokens that you sent and received. Otherwise compare the
whole request with those tokens: the start of the range, every token up to and including the start,
and the end of the range.

Basis: by reading (`Sound`; `verifyAt` and `TypedProof`, with their docstrings; `requestOfTokens`;
`IsTrueUnder`, `Policy/Rel/True.lean`, for the range conditions; `claimOf`, `formOf` and
`PV.Front.userOf`, with their docstrings; that `meaning_the` lies on the road of the theorem under a
policy: that theorem's proof names `soundUnderPolicyAtZ_of_two`,
`Johnson/Goal/Skeleton/TopAtZ.lean`, which names `meaning`, whose proof names it; no proof's inside
is covered; what a request file holds and who brings the padding in `cp_verify`:
`docs/format/FORMAT.md`, 12.2) · proved (`IntegerModel.requestOf_some`;
`tokensOfRequest_requestOfTokens`; for every padding, the two theorems that are named).

## 6. How far the checking goes

<a id="the-second-checker"></a>

### The independent checker

**L25.** The independent checker has been run over a build of this repository's files; what it
accepted: [CHECK-RESULTS.md](CHECK-RESULTS.md). The Lean verifier's reference run has been made over
this repository's Lean files. The library's full check has been run over this repository's files but
the one added afterwards (the head of this page), and has passed. What has been run over this
repository's files: [CHECK-RESULTS.md](CHECK-RESULTS.md). The independent checker:
[CHECKING.md](CHECKING.md), "The independent checker". What such a checker's word is worth:

- It reads a text that an exporter writes from Lean's compiled declarations, so its verdict is only
  as good as that exporter. The exporter and two further programs, one that counts that text without
  Lean (the recount) and one that reads it back against the compiled library (the read-back), are
  this project's own programs.
- A verdict covers the theorems that the checker was asked by name and every declaration below them,
  and nothing else. An independent proof checker checks proofs. It does not check whether the
  statements of the adapted files say what their sources say (L15).
- The exporter is not in this repository, so a reader outside the project cannot run the independent
  checker over this repository's files.
- Where build, export and checker run as one user, on one machine, the same user as the library's
  own code, such a run catches mistakes, not files that are written to deceive it (L24).
- This library was taken by program out of a larger set of files, not all of which are in this
  repository. None of the checks that these pages tell covers a file that is not in this repository
  (a comment may cite such a file: L56).

Who wrote the library, and what has not been independently reviewed: L43.

**The word "noncomputable".** In several hundred files one line stands behind the imports:
`noncomputable section -- Lean tags what it cannot compile`. In these files Lean decides by itself
which definitions it compiles. Under that line a definition that Lean cannot compile is no error:
Lean tags it in silence and the build goes on. `Ladder.lean`, the file of `verify`, opens a plain
`noncomputable section`, under which the same holds, and Lean marks `verify` noncomputable: as typed
it cannot be executed, and what runs is its executable form (L53, row 0; [GAPS.md](GAPS.md), 56).
Some comments speak of markers that are not in the files.

Basis: computed (those files: a search of the files' text for that line) · by reading (the line in
`Ladder.lean`) · not shown in this repository (the exporter; that Lean marks `verify` noncomputable:
Lean's answer on a built copy; a reader who builds the library can ask Lean the same).

### The script that ships with the library

**L24.** The library's own script, `scripts/check.py` ([CHECKING.md](CHECKING.md)), catches honest
mistakes and the usual ways of writing an unproved claim; it is no defence against an attacker. Code
in the library runs while Lean compiles it, so anyone who can change a file or the build can change
what is built.

For most of the theorems that these pages name outside the table of
[CHECK-RESULTS.md](CHECK-RESULTS.md) and whose files lie in `VerifiableInference/`, the script
compares the compiled statement, to the letter, with a stored copy (`scripts/front-statements.txt`).
It does so only where the stored copy holds a block. Whether a name of that directory on these pages
has none: [CHECKING.md](CHECKING.md). That does not catch a change to a definition that a statement
names: the statement then reads the same and means something else. For a theorem in another
directory, `Policy/`, `OnBytes/` and `Johnson/` among them, the script compares the statement only
if the stored copy holds a block for it; no rule asks for one. The theorem on
`innerCompiledVerifier` has such a block. So have theorems on the Lean verifier `verify`, the
soundness theorem on `verify` among them (which: `scripts/front-statements.txt`). Some theorems that
these pages name have none, the theorems at the heads of L89 to L92 among them
([CHECKING.md](CHECKING.md)). A theorem there without a block would pass under its name with another
statement: the audit reports its statement and axioms by name, and compares the statement with no
stored copy.

Seven of the stored statements pin a name alone (`VerifierAndGoals.AtTheName.keySound_holds`,
`VerifierAndGoals.AtTheName.g8bits_of_verify`, `link_yes`, `VerifierAndGoals.filesRead`,
`wholeKeyPrivacy`, `strike_verdict`, `compiled_complete_atEveryCoin_holds`): the compiled statement
is one constant (for `link_yes`, one constant at a numeral; for `g8bits_of_verify`, one constant at
`theDescription`), and `check.py` compares no definition's body, so a change of that body would
pass.

The stored text of the blocks on the Lean verifier was not printed over this repository's files.
That it is what the audit prints over them is shown only by a run of the comparison, which can fail:
it would if a compiled statement differed from the stored one. What has been run of it:
[CHECK-RESULTS.md](CHECK-RESULTS.md).

A full check that runs as the same user as the processes that compile catches mistakes, but not
files that are written to deceive it. The library's full check is of that kind.

Some files, among them most of those in `VerifiableInference/` and many in `OnBytes/`, have lines
`#print axioms`. Such a line only prints: the file compiles whatever the list holds. The script, in
its step `build`, audits the axioms of every declaration of the library, printed or not.

The script has an extra audit of a theorem's statement: what it quantifies over, whether its objects
were obtained by the axiom of choice, and whether its hypotheses can be met at all. No theorem on
the script's list (`scripts/top-theorems.txt`) has a line of the kind that asks for it, so it is run
on no theorem, the soundness theorem on `verify` included (what a line of the list shows: L17).

Basis: by reading (the script and its lists; the head of `VerifiableInference/Axioms.lean`) ·
computed (the seven blocks, and that no line of `scripts/top-theorems.txt` is of that kind: a search
of the two files' text). What has been run of the full check: [CHECK-RESULTS.md](CHECK-RESULTS.md).

### Tests that change the source

**L26.** A test that changes the source alters one declaration and sees whether the build breaks. No
such test has been run over the files of this repository, and the library's own script runs none
(L76).

What such a test can show, wherever it is run:

- Of a hypothesis it shows only that a proof names it, and that with a weakened or emptied form the
  proof no longer checks against the statements of the general lemmas that it calls. That is no
  proof that a derivation needs it at full strength.
- It does not show that the hypothesis holds, is consistent, or is its source's statement.
- A weakened definition need not break any proof. For the definitions the only checks are a reading,
  and the guards (L18).
- A failure can show only that a proof's text uses the changed part, not that the claim needs it.

Basis: by reading (that the script runs none: `scripts/README.md`) · not shown in this repository
(that none has been run over these files: nothing here shows or checks it).

### Comments are not checked

**L23.** Lean checks statements and proofs, not comments, and not these pages. Source code can
mislead as well, because the library defines notations and macros: two notations look like Mathlib's
and are not, and some definitions are named `True` or are defined as plain `True`
([GAPS.md](GAPS.md), 18 (c); section 6, "The files"). The remedy is the audit's listing, which
prints compiled statements ([CHECKING.md](CHECKING.md)). The script makes it in a full check only,
for the theorems that its lists name. A number in a name or in a comment need not be the number in
the statement. Words such as "out-of-domain", "Merkle", "public-coin", "encoded index" and
"proximity test" in names and comments are the library's labels; no definition is checked against
the notion that the word names in the literature. How far a file's comments agree with its code
differs from file to file, and nothing here shows it. Some comments in the Lean files claim more
than is proved; the pages govern (L55; some of the places: L56 to L60 and L87).

So where a comment differs from the statement next to it, trust the statement.

Basis: by reading.

### Trusted, not proved

**L45.** Lean's kernel, the compilers, the operating system and the fetched packages are trusted,
not proved. The pinned version of Lean, 4.29.1, is older than the published fixes (from version
4.32.1 on) of soundness bugs in Lean's kernel and runtime and in the big-number library (GMP) that
its Linux builds link. No proof in this library is known to use such a fault; the proofs have not
been searched for one, and the check script's word list and audit would not detect one. These pages
tell no check of the library with a later version of Lean. Which version of Lean is used, and which
packages are fetched, stands in `lean-toolchain` and `lake-manifest.json`.

Beside these: the three axioms on which the theorems rest (L38), the exporter under the independent
checker's word (L25), and the reading of comments, notations and macros (L23). The statement on
codes is not on this list: where it stands in a statement it is a hypothesis, and this library
proves it, from files adapted from ArkLib and Mathlib (L15).

Basis: by reading (the two files; the public release notes, advisories, issues and pull requests of
Lean, as read in stored copies and search extracts; the check script).

<a id="who-wrote-it-and-who-has-read-it"></a>

### Who wrote it, and what has not been independently reviewed

**L43.** AI systems wrote nearly all of the Lean library, part of it adapted from credited
third-party code ([CREDITS.md](CREDITS.md)). Part of its files come from a larger Lean library of
this project, which is not in this repository; that they have the same compiled content there and
here is not shown in this repository.

The statements and definitions of the theorems that this page limits, other than the six theorems
and what lies beneath their statements, have not been independently reviewed. The same holds of the
definitions beneath the soundness theorem on `verify` that do not lie beneath the statements of the
six theorems, `theDescription` and `atSecondHashFunction` among them. `verify` and the definitions
beneath the statements are definitions: Lean's kernel checks proofs, not what a definition means, so
a reader of the statements must read those definitions. Nor does it check that a statement means
what a page says of it.

The readings, comparisons, searches and runs of which these pages and the files' comments speak ("by
a reading", "by inspection", "compared"), and the proofs and arguments on paper and the arithmetic
by hand, have not been independently reviewed or repeated, unless a place says otherwise.

The files under `ThirdParty/`, who adapted them and how they were compared with their sources: L15.

Lines in comments that name a reading: L75.

Basis: not shown in this repository (who wrote the files, and what has been reviewed: nothing here
shows or checks it).

### What is machine-checked on the agreement of Reed–Solomon codes

**L46.** Without the files under `ThirdParty/`, what the library proves on the agreement of
Reed–Solomon codes holds only within half the minimum distance. For larger radii, below the Johnson
radius, it proves the statement on codes in `Cb/Bridge/`, from files adapted from ArkLib and Mathlib
(L15).

It proves a statement of Theorem 4.1 of ePrint 2020/654, in integers: two words on a line, the
unique-decoding radius as an integer, plain Reed–Solomon codes (`Code.caOn_rsCode`,
`Code/Half.lean`). It proves the step from correlated to mutual agreement within half the distance
(`Code.CAOn.mcaOn`, `Code/Mutual.lean`), and the extension to any number of rows that agree on one
common set (`Code.mca_rsCode`, `Code/Half.lean`). The first and the third have one hypothesis, 2 e +
k + 1 ≤ n, over a finite field and distinct points; the second has its own: a minimum distance d, 2
e < d, and correlated agreement at e.

- That the library's statement is the published theorem's rests on a reading of the two texts; no
  theorem says it, and the two have not been compared clause by clause.
- That the programs' closeness rounds combine rows on lines in this way is a reading of the
  programs, not a theorem (L1).
- The further steps, by which the programs' accounting goes from a count of agreement to a round's
  bound, at any radius, are written proofs in the technical report, which are not machine-checked:
  one term more for a subcode, copied mask rows as part of a longer code, the sum over a group. (Of
  the second the library has a theorem of its own, that the copied codes are subcodes of the long
  ones: `Cb.Gl.glCp_sub`, `Cb/Gl/GlCopyProofs.lean`.) How a round's error follows from that count is
  the cited paper's round-by-round theorem, which the report restates and does not prove. The
  soundness theorem on `verify` does not go through the report: the limit is the programs' (L1).

Basis: proved (the three theorems; `Cb.Gl.glCp_sub`) · by reading (the comparison with Theorem 4.1
of ePrint 2020/654: the head of `Code/Half.lean`) · not shown in this repository (the technical
report's proofs).

<a id="theorems-under-an-assumed-statement"></a>

### Theorems under the statement on codes

**L15.** The statement on codes, `Cb.BCHKS46At` (`Cb/Gen/CodeListRSAt.lean`), is a bound on the
mutual correlated agreement of Reed–Solomon codes below the Johnson radius, for two words. This
library proves it: `Cb.Bridge.bchks46At` (`Cb/Bridge/CodeListRSProved.lean`), from files adapted
from ArkLib and Mathlib (`ThirdParty/`; [CREDITS.md](CREDITS.md)). Lean checks that proof. What goes
with it:

- **The adapted files.** Of the 141 Lean files under `ThirdParty/`, 139 are adapted from ArkLib and
  Mathlib ([CREDITS.md](CREDITS.md); the other 2: `ThirdParty/README.md`). The 126 files adapted
  from ArkLib come from a copy that is marked as commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13;
  that commit has not been looked up on ArkLib's public repository. AI systems alone adapted and
  built those files. They have been compared with their sources by program alone
  (`ThirdParty/scripts/`). Lean checks these proofs. It does not check that the adapted statements
  and definitions mean what the sources' do; that has not been independently reviewed.
- **That it is the published theorem.** The published theorem on codes is Theorem 4.6 of ePrint
  2025/2055, the full version of a paper published at STOC 2026; it is not this project's. The
  theorem is not in the proceedings, which state the plain form (their Theorem 1.5). The statement
  on codes is written to follow from the theorem's case of two words. That it follows from that case
  rests on a reading of the two texts; no theorem says it, nor that it is the bound which the
  protocol's written analysis uses. The paper's own form is not proved in this library's files that
  prove the statement on codes, and no proof of the theorem in its own form has been checked for
  this library.
- **Its form.** The hypothesis is `Cb.BCHKS46At Cb.Gl.F Cb.Gl.E` (in most statements it is named
  `hA`, and the two fields are written `GF` and `GE`: `Cb/Ent/CdPts.lean`), the form of `Cb.BCHKS46`
  at the protocol's two fields. It speaks of all block lengths, dimensions, and of every radius
  below the Johnson radius, not of the protocol's codes alone. It is a proposition that is stated as
  a definition. It is not one of Lean's axioms, so where Lean lists the axioms below a theorem, it
  does not show. A third form, `Cb.BCHKS46F` (`Cb/Gen/CodeListRSF.lean`), narrower than
  `Cb.BCHKS46`, wider than `Cb.BCHKS46At`, is the same statement for the finite extensions of one
  base field, with the points in that field; it stands as a hypothesis in each statement that uses
  it, and it follows from `Cb.BCHKS46` by `Cb.bchks46F_of_wide`. Some comments call the statement
  "the assumed statement" or "the assumed theorem", and some call it "the theorem on codes".
- **Theorems that take it as a hypothesis.** Where a theorem takes the statement as a hypothesis, it
  stands in that theorem's statement (at times inside a definition that the statement names). Such a
  theorem would say nothing if the statement were false; the library proves the statement (this
  entry's first lines). Under `Johnson/` and `OnBytes/` 172 lines of code bind it under the name
  `hA`, the forms at the two IOPs that take it as a hypothesis among them (the next bullet); other
  theorems have it under another name or inside a definition. This page does not follow what each of
  them says.
- **At the two IOPs of `Johnson/Flat/TwoSizes.lean`.** There the proof is applied in forms that do
  not have the hypothesis (`Johnson/Flat/TwoSizesCodes.lean`; their names end in `_codes`, among
  them `innerCompiledVerifierSoundFromDryRunAtFullSize_codes` and
  `innerCompiledVerifierSoundFromDryRunAtSmallSize_codes`). Nothing in this library applies the five
  theorems of that file, and their statements have not been independently reviewed. Under `Johnson/`
  and `OnBytes/` 33 files name `bchks46At`, in code or in comments, and files of other folders name
  it too; this page does not follow what each does with it. The ten theorems of
  `Johnson/Flat/TwoSizes.lean` that take the statement as a hypothesis
  (`innerCompiledVerifierSoundFromDryRunAtFullSize` and
  `innerCompiledVerifierSoundFromDryRunAtSmallSize` among them) use it for `entrySound` alone, and
  the theorem on `innerCompiledVerifier` itself keeps `entrySound` as a hypothesis (V8). For the
  theorem on `innerCompiledVerifier` the statement on codes is no premise of the statement itself:
  it enters wherever one of that theorem's named hypotheses is proved at or beyond half the code's
  distance (V8).
- **Theorems that rest on its proof instead.** Other theorems do not take the statement as a
  hypothesis because they rest on its proof: the forms whose names end in `_codes`, which apply it,
  the bound on the closed check of the copy's file (V13), and the soundness theorem on `verify`
  itself (the next bullet). Their statements show no trace of it.
- **The soundness theorem on `verify` rests on its proof too.** The soundness theorem on `verify`
  ([THEOREM.md](THEOREM.md)) does not take the statement as a hypothesis. It rests on the proof, and
  so on the files under `ThirdParty/`. At least six of the theorems that its proof calls depend on
  them: `P5J.k10_kind_free`, `H2K12.k12_kind_at_head`,
  `VerifierAndGoals.AtTheName.keySound_at_live_holds`, `P5J.five_at_free2_laid2`,
  `P5J.AtMgA.lastLeft_at_head_alone` and `FlashProve.entrySound`. The heads of four files under
  `Johnson/Goal/Skeleton/` (`SoundOfVerifyAt.lean`, `SoundOfVerifyMore.lean`,
  `SoundOfVerifyPolicy.lean`, `KindsLawsAtHead.lean`) say "five": they leave out the last (a fifth
  head, and what else these heads tell: `docs/known-errors.md`, "How many theorems behind the
  soundness proof use the third-party coding theory"). "Called" means here: named by a theorem of
  the folder `Johnson/Goal/Skeleton/` and lying outside it. Two separate programs found these six
  over compiled declarations. Each ran over a build of a copy of the Lean files that differs from
  this repository's; neither has been run over this repository's. `keySound_at_live_holds` (beside
  it `keySound_holds`; `Johnson/Goal/Conditions/KeyOpenHolds.lean`) is the soundness of the key
  file's protocol; `FlashProve.entrySound` (`Johnson/Goal/Conditions/EntrySits.lean`) is the row of
  the copy's file and its link, and its statement on codes is filled by `Cb.Gl.bchks46At`, which
  rests on those files. Their statements show no trace of it; a reader finds it at the calls of
  `Cb.Bridge.foldErr_ix` (`Johnson/Bridge/FoldErrIx.lean`) and `Cb.Gl.bchks46At`
  (`Cb/Bridge/GlCodesProved.lean`).
- **How far the library stands on these files.** By import lines, 7 Lean files of this library
  outside `Cb/Bridge.lean`, `Cb/Bridge/` and `ThirdParty/` import a module of `Cb/Bridge/`, and
  thousands more stand above them, under `Ask/`, `AtFullSide/`, `E2E/`, `Johnson/`, `OnBytes/`,
  `ShapeLines/` and `VerifiableInference/`. From `lean/`, `find . -name '*.lean' -not -path
  './Cb/Bridge.lean' -not -path './Cb/Bridge/*' -not -path './ThirdParty/*' -exec grep -lE '^import
  Cb\.Bridge' {} +` lists the 7. Importing a module is not using its proof: which statements rest on
  the proof is told in the bullets above.

**Without the files under `ThirdParty/`,** what the library proves on agreement of Reed–Solomon
codes holds within half the distance (`Cb.Gl.agreeHalf`, `Cb/Gl/GlAgreeHalf.lean`; L46). No code
outside that file names `Cb.Gl.agreeHalf`.

Basis: proved (`Cb.Bridge.bchks46At`; `Cb.Gl.agreeHalf`) · by reading (the statements; that the
definition follows from the case of two words; the head of `Johnson/Flat/TwoSizesCodes.lean`) ·
computed (which lines bind the hypothesis, that no code outside its own file names
`Cb.Gl.agreeHalf`, that nothing applies the five: a search of the files' text, which does not see
uses that Lean fills in by itself; the counts of files and the import lines, by program) · not shown
in this repository (the six: the two programs and Lean's compiled files are not here).

### Five definitions that take a default value where an input is missing

**L51.** Among the definitions behind the proximity test's error bound (`Johnson/Desc/K12/`, among
the files that the file of the soundness theorem on `verify` imports) five, in four cases, fall back
to a harmless-looking value where an input is missing: `errJ` and `εAt`: errors 0 where the plan has
no chain; `batV0`: 0 without a first round; `listMax`: 0 outside the Johnson radius; `johOk`: yes at
a test without a stage. A bound at such a value holds but says nothing of the test. `ClosedL` asks
`chain`, `joh` and `bat` together, which shuts out all four cases; one alone does not.

Basis: by reading (the definitions and their own comments: `listMax` in `Cb/Gen/JohnsonList.lean`,
the others under `Johnson/Desc/K12/`). This entry follows no proof, and it does not say whether some
theorem assumes one of the three alone: no search was made for one.

### At the proximity test 2^-128 is one round's figure

**L52.** At the proximity test (`Johnson/Desc/K12/`, among the files that the file of the soundness
theorem on `verify` imports) "2^-128" is one round's figure: `ChainAt` and `batPriceOk` say that a
round's error count is at most 2^-128 of that round's own verifier messages. Neither adds the rounds
up: it is not the chance of a forgery and no security level. Proof of work is counted in (L12): 32
bits at the three of the key file's four tests whose places are written there (the fourth, the test
on the ranges in its first chain, is not among them), 28 at the proof file's two shared tests, 20 at
its two others. The error of the soundness theorem on `verify` itself: [THEOREM.md](THEOREM.md).

Basis: by reading (the two definitions and the written places of the tests, under
`Johnson/Desc/K12/`). "Neither" speaks of the two statements named: no search for a theorem that
adds the rounds up stands behind it.

### Statements without a proof

**L16.** Of eleven statements that the library writes as definitions, ten have no theorem that
proves them outright; the eleventh, `rec_bcs`, has one (the third bullet). Each one's docstring says
of what kind it is. These eleven are not all: the propositions of `E2E/TheHonestProverNotTaken.lean`
that no theorem proves are further ones (L96); that there are no others is not shown. The library
writes many statements twice: a definition under `Spec` states a proposition, and a theorem of the
same name proves it.

- Six are conditions with parameters, which other statements and theorems use: they are not claims.
- Two are properties of Reed–Solomon codes that the library proves only from `Cb.BCHKS46`, the
  statement on codes's form for all fields (`Cb.Spec.RsProx`, `Cb.Spec.RsListProps`; by `Cb.rs_prox`
  and `Cb.rs_listProps`, `Cb/Gen/CodeListRows.lean`; L15).
- Three are statements on the index binding of a compiled scheme (in `CompileK/RecBindSpec.lean`;
  L14): a theorem concludes one of them, `rec_bcs` (`Johnson/RecCompile/Bcs.lean`), and no theorem
  concludes the other two.

Further statements are proved in two steps: one theorem concludes the statement from further
statements, and other theorems prove those. Outside these stands also `Cb.Gl.AgreeJ`, agreement of
codes below the Johnson radius, which the library does not prove outright and derives only from the
statement on codes (`Cb/Gl/GlFinalAg.lean`, at `AgreeJ` and `glAg_ofAt`). Outside the eleven stand
too the six definitions in which the statement on codes is written: `Cb.BCHKS46`, `Cb.BCHKS46Rows`
and their forms ending in `F` and `At` (L15).

A definition proves nothing by itself. One of these can enter a proof only as a hypothesis, or
through a chain of theorems that proves it. A hypothesis then stands in the theorem's statement,
perhaps inside a definition that the statement uses.

Where the eleven are used this page does not follow. That a name occurs in a proof does not mean
that anything is assumed. Two of the six conditions show it: an invariant that the proofs establish
where they use it (`Compile.Batch.Spec.InvD`, `Compile/Batch/ChallU.lean`), and what two rounds ask
of three codes (`Cb.Spec.CodesOK`, `Cb/Ld/LdSumStepStage.lean`); where proofs establish
`Cb.Spec.CodesOK`, Lean's kernel checks them.

Basis: by reading (each one's docstring, which says of what kind it is; what the first of the two
is) · computed (a search of the docstrings for "not itself a claim": six definitions, the six
conditions) · not shown in this repository (that no further statement of this kind is left beyond
those named here).

### Conditional theorems

**L17.** Many theorems are conditional: such a theorem holds for any protocol, code or object that
meets a list of hypotheses, and by itself it says nothing on whether its hypotheses can be met
together.

On the road to the soundness theorem on `verify` these hypotheses are proved in Lean, or they come
down to the theorem's own three hypotheses on the public files and to sixteen tests inside `verify`:
where one of these tests fails, `verify` rejects everything. At which files all of them are known to
be met: [THEOREM.md](THEOREM.md), "Its reach". (Two conditional files beneath the soundness theorem
on `verify`: L57.)

For a theorem off that road, that its hypotheses can be met is shown only by a guard: a theorem that
meets them at a concrete instance. Many such theorems have no guard in this library, and the guards
off the road that are here stand at toys. (The guards on the model stand apart:
`canServe_atVotingWeights` and the theorems beside it (`VerifiableInference/ModelGuards.lean`) stand
at all valid settings, at made-up weights; `canServe_atAttentionWeights`,
`canServe_nowhere_atHaltingWeights` and the theorems beside them
(`VerifiableInference/ModelGuardsAtReference.lean`) at the settings of the library's reference table
of scales alone: L18.) Some comments under "Limit:" or "Limits:" say that the library has no guard
for a theorem; where there is no such comment, nothing is said either way.

One hypothesis the library proves at one round alone: `ZKCP.Gen.MissLe` (`CompileK/TotalExt.lean`),
a premise in the statement of `compileWireT_any` (`CompileK/WideMain.lean`). It is proved only for
the round j = 0, with the bound 0 (`missLe_zero`, `CompileK/WideZero.lean`); for every other round
nothing says whether it holds for any bound below 1.

One hypothesis that no theorem was found to show of any numbers: `Compile.Budget`
(`Compile/Spec.lean`: two inequalities on a protocol's numbers), a premise in the statement of
`Compile.Batch.mainBatchKE2` (`CompileK/Defer2Main.lean`) and of the theorems beside it under
`Compile/`, `CompileK/` and `Top/` that take it. No theorem was found that concludes it. It stands
as a field of a record that asks for it (`Compile.Batch.FitK`, `CompileK/Main.lean`), and its two
inequalities, written out, as fields of a second (`TopC.TargetFit`, `Cond/ObjBounds.lean`); one
theorem leads from each record to the other (`TopC.target_fit_iff`, the same file), and every value
of either that was found is made from the hypothesis itself or from such a record (a search of the
Lean files' code for these names, their fields and the inequalities' terms, each place read). It is
not `budget₀` and `budget₁` of `OnBytes.WholeKey.PremW` (`Johnson/WholeKey/Premises.lean`), which
are another record's, over other numbers. These theorems are off the road: by import lines the file
of `mainBatchKE2` lies beneath neither the file of the soundness theorem on `verify` nor the final
statement's, and neither the soundness theorem on `verify` nor the final statement reaches one of
the others (by a walk over the constants of the build of this repository's files that
[CHECK-RESULTS.md](CHECK-RESULTS.md) tells as made in seven calls, proofs included: a program's
finding, no theorem).

`Iop.IOR.Good` (`Ior/Chain.lean`), the library's notion that an interactive oracle reduction with
its honest side leads from one pair of relations to the next, bounds the games by the numbers of a
record that stands beside the reduction (`Iop.IOR.Nums`, the same file: a list of errors and two
bounds on probabilities). It does not say how large these numbers are. The same holds of
`Blocks.Stage.Props` (`Blocks/Stage.lean`), all properties of a stage: it bounds the games by the
stage's own fields (its list of errors and two bounds on probabilities), and it does not say how
large these fields are.

So what does it show that a theorem stands on the script's list? That the theorem is there, that it
is a theorem, that its statement mentions a declaration of the library, and on which axioms it
rests. For a theorem on an ordinary line of the list, and that is every theorem on it (L24), the
script gives no verdict on what the statement quantifies over, on which scheme it speaks of, on the
use of choice, or on whether its hypotheses can be met together. As far as the list shows, a listed
theorem may hold of nothing.

Basis: by reading (the statements and the library's comments; what the script's list shows: the
script and `scripts/top-theorems.txt`) · computed (what was found of `Compile.Budget`: a search of
the Lean files' code, which can miss a term that names none of the words searched; what lies beneath
what: by import lines; which constants a theorem reaches: the walk, whose tables are not in this
repository).

## 7. Verifiers by name, and what comments say

### What is called a verifier in this library

**L53.** Several things are called a verifier here, and a theorem on one is no theorem on another.

| | What | Who runs it | Ships as a program | What is proved of it |
|---|---|---|---|---|
| 0 | `verify` (`Ladder.lean`) at `theDescription`: row 3 at that IOP, behind a test on the public files, two public readings and a parser | as typed it cannot be executed; `lean-verify` evaluates an executable form of it inside Lean | as a command that runs inside Lean, not as a stand-alone program | the soundness theorem on `verify` (THEOREM.md) |
| 1 | the C++ verifier, `cp_verify` | clients run it | yes | nothing in Lean: the C++ programs are tested, not formally verified |
| 2 | `verify-on-bytes` | nobody as a program: this repository builds no stand-alone program from it; one test (`tools/accepts/`) compiles it and has Lean load the compiled code while it evaluates files of `Ask/`; it is written to read the real files and to call BLAKE2b | no | nothing on soundness. It follows `cp_verify`'s source text, so a shared mistake would not show: tested, not proved; known to differ ([OnBytes/LIMITS.md](OnBytes/LIMITS.md)). It is a second Lean verifier, used as a test tool |
| 3 | `innerCompiledVerifier`: what the compiler makes of an IOP | it takes typed values, not files | no | the theorem on `innerCompiledVerifier` (V2 to V9) |
| 3′ | `verify` (`Johnson/Top/OnFiles.lean`) and `verifyAt` (`Johnson/Top/OnFilesAt.lean`): other forms of row 3. A reader who looks up "verify" finds these first; they are not `innerCompiledVerifier` | they take typed values, not files | no | `verify_sound`, under 22 named hypotheses. How many of them are open, whether anything ties these forms to another row, and whether they have run on real files is not sorted (L82). No page rests a claim on them |
| 4 | the copy's file's closed check, `verifyEntryFull` and `verifyEntrySmall` (`OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean`): a check of the copy's file alone | Lean's evaluator, by one command: `Ask/EntryRecord.lean`, which is no part of the library | no | a bound of its own (V13). It does not see the commitment ID; that it is `innerCompiledVerifier`'s part for that file is shown by nothing |
| 4′ | `verifyGuard` (`OnBytes/Maker/Page/GuardVerify.lean`): the verdict of `verifyOneProtocol`, the compiled verifier of one IOP, through a run that gives no value once a query is asked which a test turns away | tests | no | nothing on soundness: it tests |

Many more definitions are called `verify…` or `…Verifier…` (sub-protocols, toys, helpers). They are
not sorted. "verify()" is a word in comments: it stands for `innerCompiledVerifier` (row 3) under
`OnBytes/` and `Ask/`, and for `verify` (row 0) elsewhere, on [GAPS.md](GAPS.md) among them.

Basis: by reading (the files named).

### Hiding under a tolerant policy

**L54.** Under a tolerant policy such as the clipped gap no Lean theorem covers what the outcomes
(served or failed) tell about the model's scores (L5, "What a client learns"). None proves hiding
under such a policy for the protocol's three provers (key file, link proof, request) together (L91
is stated at such files too, but of requests whose claimed output is the model's own result alone),
and, a commitment's audit apart (`docs/limits-all-rows.tsv`, rows H13.7 and H15.2), no test of
hiding has been run under one. The result on the committed tables (L62) is stated at public files
with such a policy too; it reads no verifier's decision.

Basis: by reading (the statements under `E2E/`; the heads of the files under `Policy/`) · tested
(the audit: the two rows).

### Comments may say more than the library shows

**L55.** Lean does not check comments (L23), and not every comment has been held against the code.
Some are out of date, wrong, contradict themselves, or say more, or warn less, than the code bears,
and there is no list of these places. A line number behind a file's name in a comment may not fit
the file here: some are known not to, and not every one has been tested against the line that it
cites. Several files call a theorem of their own "the main theorem": what is said of it there is
said of it alone.

- In the comments of the files under `Johnson/Road/`, `Cb/Pv/` and `OnBytes/Tie/`, "the verifier"
  means the program of `OnBytes/Model/` (`verify-on-bytes`), not the `verify` of the soundness
  theorem on `verify`. That rests on a reading of 79 of the more than 1,000 files under
  `Johnson/Road/`; of the other two folders it has not been checked.
- Some comments say of another file that it was not in the library's build when they were written.
  Every Lean file here except the 13 under `Ask/` and those under `ShapeLines/` (L69) is in one of
  the two libraries that a plain `lake build` compiles. Being in the build is not being used in the
  proofs of what THEOREM.md states.
- **That a statement says what is meant.** Lean checks that each theorem follows from the
  definitions that it names and, for each, a build reports no axiom beyond Lean's three standard
  ones (over which Lean files such a build has been made: L88); Lean does not check that these are
  the right definitions. That is read off the statements and the definitions under them.
  [STATEMENTS.html](STATEMENTS.html) prints them for that, as far as it goes: three values are black
  boxes there.
  - The statements: `sound`, `soundAndBinding`, `completeOnCanServe`, `zeroKnowledgeOnCanServe`,
    `refusedHandsOutNoProof`, `repliesFit`, with the definition `leanVerifier`
    (`AtFullSide/Face/TheSixLines.lean`: L93). These seven are this library's own wording of what is
    to be proved.
  - So are the statements of soundness, completeness and zero knowledge as an IOP, which
    [STATEMENTS.html](STATEMENTS.html) does not print: those of `Hiop/SoundAsIOP.lean`
    (`Iop.HolographicProtocol.IndexKnowledgeSoundIOP`, `Iop.HolographicProtocol.SoundInParts` and
    `Iop.HolographicProtocol.WholeRunSound`); `E2E/SoundAsIOPAtFiles.lean`
    (`AtPublicFiles.AtFiles.SoundAsIOPAtFiles`); `E2E/SoundAsIOPProbabilityAtFiles.lean`
    (`AtPublicFiles.AtFiles.ConclusionFails`); `Johnson/Face/CompleteAsIOP.lean`
    (`VerifiableInference.Compilation.CompleteIOP` and
    `VerifiableInference.Compilation.CompleteInParts`); `Hiop/CompleteCore.lean`
    (`Iop.FailsRarely`); `E2E/CompleteAsIOPAtFiles.lean`
    (`AtPublicFiles.AtFiles.CompleteOnServedRequests`); `E2E/CompleteAsIOPAtTheTerm.lean`
    (`AtPublicFiles.AtFiles.HonestTerm.TheProverIsCompleteAsIOP`);
    `VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean`
    (`VerifiableInference.Compilation.HonestVerifierZeroKnowledge`); and
    `VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean`
    (`VerifiableInference.Compilation.ZeroKnowledgeOnServedRequests`), each with the definitions of
    its file in which it is written.
  - What has not been independently reviewed: L43.

So do not take from a comment what is proved: where a comment and Lean's printed statement differ,
the statement counts. Where this page names a file's head or a docstring as the place of a theorem's
limits, these limits hold. The comments in the Lean files are notes for whoever builds on the
proofs, and so are some strings in the code of about twenty of those files: those in the field
`whose` of table rows (`Johnson/Desc/First/Borders.lean` and others), and messages that some
functions return, which a few lemmas under `Johnson/Desc/ProofFile/` and `Johnson/LPFPol/SkR/` state
word for word. Some of these strings say "TO CONFIRM" or "A GUESS", or call the verifier of
`OnBytes/` "the older verifier". They are code, but a search of the Lean files finds nothing that
reads the field `whose` by name, and what holds of a row or a function is what the theorems on it
state, not what such a string says.

Basis: by reading (not machine-checked) · computed (which folders the two default targets of
`lakefile.toml` cover; that nothing reads the field `whose` by name: a search of the Lean files'
text).

### How to read a comment that cites a file

**L56.** With the mark "[not in this library]" or without it, what a comment says on the strength of
a file that is not in the repository is not proved, or not tested, here, and no proof here depends
on it. Two kinds are excepted:

- a path under a shorter folder name (`ToldDesc/` for `Johnson/ToldDescR/`), whose file may lie in
  another folder. Search for the file's name; that the file so found is the file meant is not
  checked;
- a path into another library's sources. ArkLib and VCV-io are not among the pinned packages, and
  `ThirdParty/MathlibBackport/` cites another Mathlib than the one pinned: what a comment says on
  the strength of such a file is not shown here, except where `ThirdParty/` holds its text in an
  adapted form.

Basis: by reading (the comments that bear the mark; `lake-manifest.json` for the pinned packages) ·
computed (that a cited file is not here: a search of the library's file names).

### The limits of two conditional files beneath the soundness theorem on `verify`

**L57.** The statements of `Johnson/Flat/Told/Dec/TAtLaws.lean` and
`Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFieldsO.lean`, which the soundness theorem on `verify`
uses, are conditionals: `keySound`, `entrySound`, `proofSound`, the meaning, `carries` and `hext`
are premises there (`Dec/LayoutsAtDescriptionOfFieldsO.lean`, with `hk`, `wK`, `dK`, `wP`, `dP`,
`ownParser` and `bound` among the further premises around them), and neither file proves one of
them. At one instance they are proved elsewhere: `keySound_at_holds`
(`Johnson/Goal/Conditions/KeyOpenHolds.lean`) proves `keySound` at `dataAtFiles flashProveData`, at
every set of public files in scope at which `protocolDataWellFormed` says yes, under that file's own
limits, among them that a theorem may be vacuous; `entrySound`: `FlashProve.entrySound` (L15). On
`proofSound` and the others: `Johnson/Goal/Skeleton/SoundOfVerifyAt.lean`, `SoundOfVerifyMore.lean`
and `SoundOfVerifyPolicy.lean`; what these prove, and on what it rests: [THEOREM.md](THEOREM.md),
[GAPS.md](GAPS.md). The opening comments of the two files point here for their limits, and that of
`Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean` sends to `TAtLaws.lean`'s head. These
limits are:

- The public files are fixed before the hash function is drawn.
- `G`, `DK`, `DP`, `runK`, `runP` and `h₀` are fixed, no functions of `d`: the theorem
  (`innerCompiledVerifier_sound_byPublicReading`,
  `Johnson/Top/InnerCompiledVerifierByPublicReading.lean`) says something only where they name no
  answer of the hash function.
- Every statement is general in `runK` and `runP`: it stands at "yes to all" and at "no to all"
  alike. At "yes to all", `keySound` and `proofSound` are false at any error below 1 (by an
  argument; no theorem), so the conditional holds vacuously there and says nothing for that
  verifier. At "no to all" the premises can hold, and the conclusion is true because that verifier
  accepts nothing: it says nothing, as every soundness statement does of such a verifier.
- The instance that would do harm is the degenerate one (`D := Unit`; a reading that asks nothing;
  true digests typed into `m`). It is barred by `at_toldD` and `fitsD`
  (`Johnson/Flat/Told/Dec/TAtLaws.lean`) with `reads`
  (`Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean`).
- At `DescriptionData.filler`, a coding that encodes nothing
  (`Johnson/Goal/Tie/DescriptionOfData.lean`), the extractor finds nothing, and `hext` fails there
  unless the named extractor finds nothing too.
- The starting values are no part of `d`.

Basis: by reading (the files named).

### A comment that reads brighter than two theorems bear

**L58.** The opening comment of `Johnson/P5J/K03OneOwnAt.lean` says of three named tests that each
is had from the head in another file. Two of the three theorems that it names, `oneC_at_head` and
`k03_offC_at`, stand at the second hash function (`OnBytes.secondHashFunction`) alone, while the
file's fields are typed for any hash function. Read it as: had from the head at
`OnBytes.secondHashFunction`. That is the hash function at which the forms of the soundness theorem
on `verify` take their head.

Basis: by reading (the three theorems' statements; the statements of the forms of the soundness
theorem on `verify`).

### Three premises that are not shown to be met here

**L59.** The theorems of `Johnson/Road/K4/K4PinsEndFirst.lean` take three public premises: la = 16,
the size of the vocabulary, and `EmbNums`. The three are proved of what `publicOf` returns, at all
public files in scope that are read, by `scope_la` (`Johnson/Road/K4/RefInScope.lean`) and
`emb_public_in_scope` (`Johnson/Goal/Meaning/EmbScope.lean`); where `publicOfO o` returns,
`EmbScope.emb_public_in_scopeO` proves the last two, and la = 16 is one of the 41 numbers of
`ScopeCore.core_of_scopeO` (both in `Johnson/Goal/Numbers/PublicAtMeaning.lean`). The calls are not
made in that file, so there the three stay premises; and by the head of `PublicAtMeaning.lean` no
theorem says that `publicOfO o` returns a value at any files in scope.

Basis: by reading (the four statements; the head of `PublicAtMeaning.lean`) · computed (that the
calls are not made in that file: a search of its text for the four names, which stand in its opening
comment alone).

### A named theorem whose file is not here

**L60.** A docstring in `Johnson/Desc/First/Att/Door/OwnersAreOurs.lean` names a theorem,
`offer_freeAbove`, and gives `Johnson/Desc/First/Att/Door/OfferIsLayer.lean` as its file. That file
is not in the library, so it is not shown here. There are more places of this kind: where a comment
names a file or a theorem that this library does not have, read it as not shown here.

Basis: by reading (that docstring) · computed (a search of the library's file names).

## 8. The illustrative committers, and Lean's results on index privacy

L61 tells what Lean proves of an illustrative system: a system that keeps the Lean verifier's
verifier and extractor and has an illustrative committer. L62 to L66 tell what Lean proves on hiding
at the default setting with fixed-message provers and of the link proof; what is proved of the
protocol's own three honest provers is told at L91 and L93. `lean/GAPS.md`, the appendix on gap 15,
(1) to (12), tells what is missing from these results on hiding, which of Lean's statements on
hiding can be met trivially as typed (the goal `PackageZeroKnowledge` among them), and what is
argued on paper for a toy alone (the simulated tree). Each of these entries says what the theorem
says, of which object and under which hypotheses, and then what goes with it. L67 to L75 are single
limits: on the statement of the soundness theorem on `verify`, on the public files, and on further
statements of the library. All of it is about Lean terms; nothing here is proved of the released
programs (L1). Terms: [TERMS.md](TERMS.md). Paths in this part that open with `lean/` or `examples/`
are from the repository's top; the others are from `lean/`, or, where one is a bare file name or a
sub-folder, from the folder that its entry names.

### Properties of an illustrative system

**L61.** Of an illustrative system, which keeps the Lean verifier's verifier and extractor and has
an illustrative committer (it models one part of `cp_commit`; no theorem ties them), Lean proves, at
that system's own extractor, correctness of extraction, binding of the commitment (in the opening
form) and no two openings, at files in scope where the tests on the public files pass. It proves
soundness after an honest commitment: after that committer has committed to fixed weights w, no
prover makes the Lean verifier accept an output that does not meet the files' policy at w, but for
the stated error, on average over honest commitments. That is no test of the committer. These
theorems do not say that the tests pass or anything is accepted. The committer is
`Bind.Cpp.cppCommit`, in the system `Bind.Cpp.theCpp` (`lean/Johnson/Bind/Cpp/Defs.lean`); that the
extractor is the IOP's own: `Bind.Cpp.cpp_is_of_verify` (`lean/Johnson/Bind/Cpp/OfTie.lean`). The
library's other illustrative committers: `lean/GAPS.md`, gap 55. What goes with it:

- **Whose committer.** It is an illustrative committer, in an illustrative system: the Lean
  verifier's own system keeps its constant committer, and of that system none of these properties
  can be stated with any content. It models one part of `cp_commit`; no theorem ties them. It has
  been compared with that program in values alone. At the small stored example's public files, on
  synthetic weights, under one public seed, a faster text of it, proved equal to it, with two
  further Lean texts, for the table and for the coins, of which no theorem on the committer speaks,
  gave all 2^23 leaf digests, the root, the 256 OOD answers and the commitment of two runs of
  `cp_commit`: one by a production build, one by a build made for the tests. That is an agreement of
  values, no theorem. Neither the two runs nor the two builds are in this repository: a reader
  cannot repeat the comparison, and nothing here shows that the two builds were made from the
  sources that lie in it. Nothing compares the table at weights as the theorems take them, any other
  size, any other seed, or a real model's weights.
- **Which files.** Correctness of extraction, binding of the commitment (in the opening form) and no
  two openings are proved at files in scope where the tests on the public files pass; soundness
  after an honest commitment, for the files' policy, at all files in scope that are read. At the
  library's written copies of the two stored sets of public files
  (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`, Lean terms that no theorem ties
  to the files on disk: L69) the tests on the public files (`protocolDataWellFormed`) pass, by
  theorems of a side library, outside the main library and with that library's own limits: so there
  these three hold by theorems, and of the two cases of soundness after an honest commitment (where
  a test fails, the Lean verifier rejects everything) the live one is the one that holds. No theorem
  shows the tests passing at any files without the side library beneath it, and no theorem says that
  the Lean verifier accepts a proof at either copy under this illustrative committer's commitment.
- **The verifier may accept nothing.** Nothing says that the Lean verifier accepts any proof under
  such a commitment: the committer returns the commitment alone, no key file, and no honest prover
  is written for this illustrative system. So completeness, index privacy and anything else that
  needs an honest prover are not proved of it, and no case in which soundness after an honest
  commitment forbids anything is shown by theorems alone (no theorem shows `verify` accepting a
  proof under that commitment; that the files' policy by itself rules some outputs out, under "The
  policy may bar nothing", is another matter).
- **One-sided.** Soundness after an honest commitment is no test of the committer: the constant
  committer of the Lean verifier's system meets it for every claim. What distinguishes this
  committer from it is correctness of extraction: the constant committer fails that by hand, no
  theorem; a committer in its place that does not read the weights fails it by a theorem
  (`lean/Johnson/Bind/Cpp/Controls.lean`). That the statement, taken with completeness, would
  distinguish them is proved only for committers that do not read the weights and keep the count of
  queries, and, without a further premise, only for the claim "is the model's output"; beyond these
  it is an argument, no theorem.
- **The policy may bar nothing.** Some policies in scope put no condition on the counted tokens; the
  second stored set's policy does rule something out: under some made-up weights an output does not
  meet it (`VerifierAndGoals.AtFiles.exists_output_not_meeting_gap`
  (`lean/Johnson/Goal/Files/MeetsPolicyAtFiles.lean`)), and in an output of at most 99 counted
  tokens that meets it every counted token's gap is below 25,600
  (`Policy.gaps_of_meetsPolicy_qExample_short` (`lean/Policy/Front/MeetsPolicyAtGap.lean`)); and
  from 100 counted tokens on, an output meets it even when one of its tokens is arbitrary, provided
  that every other token is the model's next token, that no range condition fails on the output, and
  that its token after a full window, if any, is the model's first choice
  (`Policy.meetsPolicy_qExample_of_one_free` (`lean/Policy/Front/MeetsPolicyAtGap.lean`)); what a
  policy bars depends on w too (under all-zero weights every well-formed output no longer than one
  window meets many policies); the scores are the library's integer model's; and the policy is not
  the test of the public paper on Token-DiFR.
- **What is outside the statement.** That a given commitment was made by this committer is outside
  soundness after an honest commitment. That statement speaks of one commitment and one proof, as a
  joint probability, on average over honest commitments. Weights, public files and the prover's
  strategy are fixed before the hash function is sampled; the second hash function is one fixed
  function.
- **Where it stands.** At the full size alone, where this committer's text cannot be run (about 2^72
  multiplications); the Lean verifier stands at the full size alone, so no run at any size tries
  these statements (the runs told under "Whose committer" compare values of the committer's
  definition at a small shape; they try no theorem). No test of correctness of extraction, of
  binding of the commitment (in the opening form) or of no two openings has been run; for one, none
  in which one commitment of this illustrative system is opened in two ways. How a seed becomes
  coins is a free parameter (the generator `g` in the theorems' statements: no theorem reads what it
  is); how weights become the table is the library's own, compared with the programs' nowhere. The
  Lean verifier is not `cp_verify`, the C++ verifier that users run. A small set of public files is
  written in Lean for tests that run at each build (`Bind.Twin.Anchor.policy`,
  `Bind.Twin.Anchor.layout`, `Bind.Twin.Anchor.scales` (`lean/Johnson/Bind/TwinAnchor.lean`)); the
  runs told under "Whose committer" read the files themselves, which have the same bytes, not this
  copy; no theorem of these results names it. What stands at its shape is the equality of the
  committer's fast text with its plain one and of its columns with the library's tables at that
  size, not correctness of extraction, the opening form or soundness after an honest commitment,
  which stand at the full size alone.
- **How much.** Correctness of extraction holds up to about 2^-89 at the committer's own 2^35
  queries; binding of the commitment (in the opening form) at 124 bits per query, never below about
  2^-101; soundness after an honest commitment at 124 bits per query of the prover, never below
  about 2^-88 (the committer's queries counted as the prover's). No figure is 128 bits. All
  probability is that of other files' theorems, in part over coding theory adapted from third-party
  Lean (L15). Who wrote these files: L43. The statements and definitions of these theorems, and of
  the files beneath them, have not been independently reviewed.

Binding of the commitment in the opening form, with correctness of extraction, and what Lean has of
index privacy at the default setting are proved of different systems: the first of illustrative
systems (`verify`'s system with an illustrative committer), the second of the whole-key argument
with fixed-message provers. Of the Lean verifier's own system and the illustrative systems, none has
both. The line `soundAndBinding` and the theorem `zeroKnowledgeAtEveryRequest` (L93) are of one
system, the compiled system at the Lean honest part; the latter is in another form than index
privacy (`lean/GAPS.md`, gap 55).

The theorems: `Bind.Cpp.extractsCommitted` (`lean/Johnson/Bind/Cpp/TheTie.lean`) ·
`Bind.Cpp.bindsAt` (`lean/Johnson/Bind/Cpp/TheTie.lean`) · `Bind.Cpp.soundAtCommitted_own`
(`lean/Johnson/Bind/Cpp/SoundAtCommitted.lean`). At these three the independent checker cannot give
a verdict (L80).

Further theorems of this result: `Bind.Cpp.noTwoOpenings_live`
(`lean/Johnson/Bind/Cpp/NoTwoOpeningsAtLive.lean`); and, with no premise on the files, at the
library's written copies of the two stored sets, by a side library:
`AtFullSide.Tie.extractsCommitted_zFull`, `AtFullSide.Tie.extractsCommitted_zGap`,
`AtFullSide.Tie.bindsAt_zFull`, `AtFullSide.Tie.bindsAt_zGap`, `AtFullSide.Tie.noTwoOpenings_zFull`,
`AtFullSide.Tie.noTwoOpenings_zGap` (`lean/AtFullSide/Bind/TheTieAtNamed.lean`).

Basis: proved (the theorems named) · by reading (what no theorem says; that the constant committer
fails correctness of extraction; what the statement parts beyond the committers named) · computed
(about 2^72 multiplications) · tested (the agreement of values under "Whose committer": one small
shape, synthetic weights, one seed) · not shown in this repository (the two runs of `cp_commit`,
their builds and the Lean run beside them).

### The committed tables alone, before any hashing; no prover's message

**L62.** Lean proves, for Lean's encoder and with fixed-message provers, that what is shown of the
committed tables, within a budget of columns, has the same distribution whatever the weights. It
holds before any hashing, under fresh randomness, and is tied to no program. It covers no message of
a prover, so it is not zero knowledge, and it is not index privacy. It holds at the interactive
oracle proof (IOP) from which the Lean verifier is compiled, at the default setting, at the 400B
model's shape, for each table's out-of-domain (OOD) sample and up to 44,040,191 of its columns. As a
whole it is stated at that shape and nowhere else. It supposes, for each table, an OOD seed chosen
from nothing hidden, then fresh uniform pads (which mask the OOD answers) and encoding randomness,
and one OOD sample. A prover's messages are what the IOP's provers send in their rounds; the
committed tables, their OOD samples and the columns of these tables that a proof opens are not among
them. What goes with it:

- The provers are fixed-message provers: they send the same messages whatever the weights. No
  message of a real prover is covered, alone or together with the tables. At the edge of the budget
  every random value of a table is spent (by reading, no theorem), so none is left to cover what a
  real prover says of that table. That must be covered by the run's own random values. For the link
  proof Lean proves that, before hashing and for an honest verifier, given the two tables' OOD
  answers and opened columns (L65). For the key file's and the request's provers: L91.
- It stops before any hashing: roots, salts and paths are outside it. Each table's OOD seed is
  chosen before that table's random values are drawn, and seeds and opened positions depend on
  nothing hidden. As run, both are hashes over roots that depend on hidden values; that step is no
  part of this result. The conditional theorem (L64) carries the single-table statement past
  hashing, for fixed-message provers. With the link proof's honest prover, as written in Lean, among
  them, it does so at one fixed public-files digest, at which `verify` is not proved ever to be
  called. In both cases that is proved for one request per proof, not for batches, and of the
  argument whose key is the whole key (L64, "Where all 20 are proved"), not of the Lean verifier's
  own system. After hashing Lean's scheme too gets the points by hashing the root; its random values
  stay fresh.
- It supposes uniform pads and encoding randomness, fresh for each table, one OOD sample a table,
  and one set of public files for a table's random values. As run, these values are derived from the
  committer's secret seed by a pseudo-random function, so hiding can be computational at best there.
- The budget, 44,040,191 columns over a table's whole life, has no slack, and nothing in Lean keeps
  count of it. The programs keep that count, in a file for each table. At one column more the same
  statement for a single table fails, at one OOD seed and one pair of matrices
  (`AtPublicFiles.AtFiles.not_hidE_own` (`lean/E2E/ObjectGuardsSeeded.lean`)). That the whole result
  fails there, or that anything of the weights would show, is not proved.
- A theorem says that the encoder and the protocols of this result are those of the input at which
  the Lean verifier calls the compiled verifier (`AtPublicFiles.AtFiles.objOwn_is_input`,
  `E2E/TablesAtOwnObject.lean`). But no verifier reads the encoder, the pads or the map that makes
  the OOD answers. That they are the protocol's rests on a comparison, by reading, with the format's
  pages; no theorem says it, and no program's file was compared.
- It is stated at the library's written copies of the two stored sets of public files, and at all
  public files of the one proof format and model size that the Lean verifier takes. Where the
  verifier's own tests on these files fail, the key file's and the proof file's verifiers open no
  column; the OOD samples, the columns that link proofs open and those that the environment picks
  itself are covered all the same. That they pass is proved at the library's written copies of the
  two stored sets of public files (Lean terms, tied to the files on disk by no theorem: L69), and at
  the first copy under every other policy in scope, in a side library. At all other files in scope
  it is not proved.
- The Lean statement says "any two matrices". Beyond the matrices that stand for weights this holds
  only because the provers send fixed messages: with real provers it must be cut to matrices in
  range (an argument, no theorem). Two matrices that differ only outside the base field have the
  same tables.
- In sum, no Lean theorem covers the OOD answers as the programs make them (from a seed, at hashed
  points). For the protocol's three provers together, as written in Lean: L91, L93.

The theorems: `AtPublicFiles.AtFiles.tables_own_named` (`lean/E2E/TablesAtOwnObject.lean`). The
statement for a single table: `AtPublicFiles.Table.HidE` (`lean/E2E/TableHides.lean`),
`AtPublicFiles.Reads.hidE_filesAt` (`lean/E2E/ReadsAtFiles.lean`).

Basis: proved (the theorems named; `tables_own_named` rests on Lean's three standard axioms alone;
how to check that: `lean/THEOREM.md`, "How to check it") · by reading (what the statement supposes
and leaves out; that every random value is spent at the budget's edge; the comparison with the
format's pages; the cut to matrices in range; what the programs do).

### The conditional theorem's conditions that read no prover or coin

**L63.** Of the conditional theorem's 20 conditions (L64) Lean proves 15, those that read no prover,
coin or simulator, at the input at which the Lean verifier calls the compiled verifier. (That counts
conditions, not work.) The conditions on the honest provers' messages, stops and coins are left to
theorems on the provers; for the protocol's own three: L91, L93. The other five conditions speak of
the three honest provers (key file, link proof, request), their simulators and coins: there hiding
itself must be proved. So index privacy does not follow from these 15 alone. What follows with
fixed-message provers is told at L64. The 15 hold up to 710,324 copies and 688,127 sessions a copy,
of one request each; five of them by type or default. What goes with it:

- What is left is every condition on the honest prover's messages, on their simulators, on its stops
  and on its coins, and that the tables that it holds are the encoder's. What is proved of the
  protocol's own three honest provers: L91, L93. The link proof's honest prover has, before hashing,
  an exact simulator for an honest verifier, given the two tables' OOD answers and opened columns
  (L65). Three shades on "read no prover, coin or simulator": one of the 15 bounds the honest
  prover's number of copies, and it holds because that number is supposed to be at most 710,324; of
  the 19 clauses of the condition on coins five name no prover and no coin; and one of the 15 reads
  the encoder's random values, as a uniform law and not as a prover's coins.
- What is left can be met by provers that say nothing of the weights. Provers that send fixed
  messages and never stop meet three of these conditions with errors 0, at every input
  (`OnBytes.WholeKey.silent_good` (`lean/Johnson/WholeKey/Foes.lean`)). Provers that send fixed
  messages meet all 20 conditions (by three theorems together), at the input at which the Lean
  verifier calls the compiled verifier. That covers nothing that the three provers would compute
  from the weights in their rounds: here these messages are fixed. The theorems that bound the
  conditional theorem's error ask at least 256 free bits in a leaf's salt; the figure stands at 320
  of a salt's 576 bits. With no free bit in a leaf's salt the conditional theorem's error is 1 or
  more (by arithmetic on the formula, no theorem). Fixed messages hide the weights for free, so on
  the provers' own messages a result on hiding counts only beside completeness of the same provers.
- With all 20 the conclusion is about an argument built at each fixed input, with a separate random
  oracle for each kind of query. It is not about the Lean verifier's system, whose verifier first
  reads that input off the hash function.
- One of the 15 contains, beside four counts of what the verifiers read, a clause that is no
  condition on a verifier: the statement for a single table beneath the result on the committed
  tables (L62), a law of the encoder and its random values alone. It says: as Lean's encoder makes
  them, with fresh randomness, one table's OOD answers and up to 44,040,191 opened columns have the
  same distribution whatever the weights. The result on all tables rests on that fact and is none of
  the 20 conditions. Every limit of that result goes with it. Its budget has no slack, and nothing
  in Lean keeps count of it: in the conditional theorem it is two conditions on numbers, and Lean's
  prover keeps no state.
- Of the 15, eight follow from the protocol's written data and the library's laws, two are
  arithmetic on the chosen numbers, and five hold by type or by default. One of these holds because
  no OOD seed is set aside; if the prover's side has to set some aside, that condition is a premise,
  and the count is 14.
- 710,324 and 688,127 are the most that fit the budget of 44,040,191 columns a table. The key file's
  verifier reads at most 62 columns of the first table, and each copy's link 62: 62 + 62 · 710,324 =
  44,040,150. A copy's link reads at most 62 columns of that copy, and each session 64: 62 + 64 ·
  688,127 = 44,040,190. One copy or one session more is over the budget
  (`AtPublicFiles.Premises.not_noProverSide_copy`, `AtPublicFiles.Premises.not_noProverSide_session`
  (`lean/E2E/PremisesAtFiles.lean`)). The counts 62 and 64 are upper bounds: that the verifiers ever
  read so many is not shown. These are sessions of one request each; of batches of two or more
  nothing is said. By the programs' own accounting a copy serves at most 688,127 batches of up to 64
  requests; no theorem ties that count to Lean's sessions. "No slack", in the result on the
  committed tables, is said of what the encoding randomness bears: 44,040,191 columns and not one
  more.
- The 15 hold at all public files of the one proof format and model size that the Lean verifier
  takes. Where the verifier's own tests on these files fail, the key file's and the proof file's
  verifiers read nothing and (by reading, no theorem) reject everything; that the link's verifier
  rejects everything there, and with it the Lean verifier as a whole, are theorems
  (`FlashProve.theLay_dec_dead`, `FlashProve.theDescription_dead_all`). What the 15 say of these
  verifiers is empty there. That they pass is proved at the library's written copies of the two
  stored sets of public files (Lean terms, tied to the files on disk by no theorem: L69), and at the
  first copy under every other policy in scope, in a side library. At all other files in scope it is
  not proved.

The theorems: `AtPublicFiles.Premises.noProverSide_description` (`lean/E2E/PremisesAtFiles.lean`) ·
`FlashProve.theLay_dec_dead` (`lean/Johnson/Goal/Description/Dead.lean`) ·
`FlashProve.theDescription_dead_all` (`lean/Johnson/Goal/Description/DeadParser.lean`).

Basis: proved (the theorems named; `noProverSide_description` and `theLay_dec_dead` rest on Lean's
three standard axioms alone; how to check that: `lean/THEOREM.md`, "How to check it") · by reading
(which conditions read what; how each of the 15 holds; that two verifiers reject everything where a
test fails; the programs' accounting) · computed (the two sums; the error with no free bit in a
leaf's salt).

### Conditional theorem on index privacy: not the whole protocol

**L64.** Lean proves a conditional theorem. If 20 conditions hold for an IOP's honest provers and
their simulators, the non-interactive (hashed) argument made from them has index privacy in the
random-oracle model, up to an error. It is stated at general inputs, the default setting's among
them. For fixed-message provers, at full size, where the tests on the public files pass, that error
is at most 2^-135 (one copy, one request, 2^64 hash queries). There proofs come out under the same
proof-of-work limits. These limits are 2^40 + 1 tries a search; a copy is a further committed table
of the same weights, with masks of its own, against which requests are proved. For more copies and
requests the bound is a formula, which no theorem evaluates there. That these tests pass is proved,
in a side library, at the library's written copies of the two stored sets of public files (L69). For
the protocol that the programs are written to run, as Lean describes it ("this protocol" below),
what is proved of the protocol's own three honest provers is told at L91 and L93. Alone this theorem
does not cover the key file's proof or a request's. What the IOP hides is a condition, not a result.
It is not called zero knowledge. What goes with it:

- **Conditional, and not about the whole protocol.** For any interactive oracle proof (IOP) of the
  type of the Lean verifier's IOP, and any honest provers: if the conditions hold, the hashed
  argument made from them, with its whole key published once, has index privacy, over typed random
  oracles, one instance a proof, on a stated range of indices, up to a written error. It says
  nothing of a protocol until all 20 conditions are shown there, for one choice of honest provers,
  simulators and range. All 20 are proved together for toy examples and, for Lean's form of this
  protocol, in two cases (the next bullet); inside the proof of L93's line on zero knowledge they
  are met too by the protocol's own three provers, made to refuse a request that is not served, at
  public files in use and at one copy of the table (`lean/GAPS.md`, gap 75). A toy is a small
  made-up protocol that is written in Lean alone. A toy's index is not weights. At the two toys that
  do not leak, at least three of the five parts of the written error are zero. What is proved of the
  protocol's own three honest provers: L91, L93. Of batches these results say nothing. Hashing's
  share of the error is bounded, by a formula, for any three provers.
- **The two cases, with a number.** Provers that send fixed messages meet all 20 conditions (by
  three theorems together), at the input at which the Lean verifier calls the compiled verifier, at
  the error named above. That bound has content: under the same limits on proof-of-work search the
  provers do hand out proofs. So after hashing, against any verifier within these bounds, what the
  public key and the fixed-message provers' proofs show of the committed tables (roots, OOD answers,
  opened columns) can be simulated without the weights. That covers nothing that the three provers
  would compute from the weights in their rounds: here these messages are fixed.
  - The bound and the proofs hold too with the link proof's honest prover, as written in Lean (L65),
    at one fixed public-files digest, at which `verify` is not proved ever to be called. Of the
    conditions' clauses on the link prover only the one on its simulator has content, so all else
    there holds for any link prover that never aborts, whatever it sends; and there is no negative
    test: the statement is not proved to fail, at these parameters, for a link prover that sends the
    index (`lean/E2E/LinkLaidPrivacy.lean`). Then, against any verifier, the theorem's simulator,
    given the request but not the weights, makes the whole view up to that error: this link proof
    included, the other two provers' messages fixed. There the public bits of its salts are zeros by
    choice. Wherever a link proof comes out, proof of work passes and, where the tests on the public
    files pass, the link's own verifier accepts at the hashed challenges. That it accepts there is
    proved in a side library. That the hashed verifier accepts, even where proof of work passes, is
    not proved.
  - That the view holds the tables' roots, OOD answers and opened columns is read off the
    definitions, not proved. That each produced proof opens such a column is proved for the scheme's
    own run and for one verifier that asks no hash query, not for every verifier
    (`AtPublicFiles.Shown.allAtOnce_description`, its clauses 4 and 7,
    `E2E/StringsOpenInGame.lean`).
  - In both cases the key file's and the request's provers send fixed messages: nothing that these
    two would compute from the weights is covered. Both cases are proved at full size, where the
    tests on the public files pass.
- **Where all 20 are proved, it is about another argument than the Lean verifier's.** Its key is the
  whole key: the first table's root, OOD sample and proof, and every copy with its link proof. Its
  inputs are fixed before the oracles are sampled. The Lean verifier's key is the 256-bit commitment
  alone, and that verifier first reads parameters off the hash function. What holds of the final
  system, whose commitment has 256 bits: L93. Of this argument, no theorem covers the reading of
  parameters.
- **Alone it says little.** Honest provers that send fixed messages and never stop can be simulated
  with error 0, for every IOP of the theorem's type (`OnBytes.WholeKey.silent_good`). So of the
  provers' own messages the theorem says something only beside completeness of the same honest
  provers, at a small stated error. No theorem shows that provers that send fixed messages fail
  completeness. Alone it is not called zero knowledge: completeness of the same provers stands
  beside the theorems of L91 and L93.
- **One instance in each proof, and a bounded number of proofs for each key.** The programs prove
  instances in batches, and nothing is said of what a client learns about the other instances of a
  batch. Several instances in one proof need a new statement, not a corollary: by reading, not
  proved in Lean, with two instances in a proof the statement with this simulator would be false.
  Past the number of copies of the committed table times the number of sessions that a copy serves,
  the error is 1 or more (by hand, no theorem). With two copies or more it is large before that
  number is reached, since the prover draws its copy at random (the head of
  `lean/Johnson/WholeKey/Zeta.lean`; by hand, no theorem). At one copy the formula's term for a copy
  that is overrun is 0 up to that number (by hand, no theorem); of the final system, whose honest
  part has one copy, the error of `zeroKnowledgeOnCanServe` stays at or below 2^-154 up to that
  number, within that line's limits (L93).
- **The error is a formula, and only below 1/2 does the theorem begin to say something of two
  indices.** For two indices of the range with the same public parameters, under one environment
  that is valid at both, the real views are only shown to be within twice the error
  (`OnBytes.WholeKey.real_real`). So an error below 1/2 is necessary, not enough. A prover that
  tells its index in all but a share of its proofs is ruled out where twice the error plus that
  share is below 1 (`OnBytes.WholeKey.FoeScheme.one_le_of_event`) and, by arithmetic that is not
  proved in Lean, no sooner. A quote gives the error as a number, at named numbers of hash queries
  and of sessions.
- **The range, by name.** A quote says which range of indices it means. The range must hold two
  indices or more, and every index that has a true instance. Nothing is said of an index outside the
  range, and no part of the error accounts for that.
- **Ideal coins, typed random oracles, no program.** The coins are uniform and independent, so coins
  that are derived from a secret seed by a pseudo-random function aren't covered. Each kind of hash
  query has a random oracle of its own; corollaries state the like over one hash function, at the
  same error or at one query more (`wholeKeyPrivacy_overOne`, `wholeKeyPrivacy_withId`,
  `privacy_wholeOne`, `privacy_wholeId`, `lean/Johnson/WholeKey/Main.lean`). The committer, the
  prover and the verifier are Lean terms, and no theorem ties them to a program. A committer that
  publishes its key only after a check of its own has passed, or that starts again after a stop, is
  another committer, and no part of the error accounts for it. Nothing is said of time. The
  simulator's running time is not bounded. Nothing is said on what the public inputs themselves tell
  of the index.
- **What it rests on.** The proof rests not only on this theorem's own files and on the rest of the
  library, but also on 26 Lean files under `lean/OnBytes/Prover/` and `lean/Johnson/Prover/`
  (counted by the import lines beneath `lean/Johnson/WholeKey/Main.lean`), which hold the hashed
  argument's general prover: a Lean term that plays whatever honest provers of an IOP it is handed.
  It is no prover of this protocol. What the theorem is about is decided there. These 26 files have
  not been independently reviewed (the statement and its definitions: L66).

Further limits of this theorem: `lean/GAPS.md`, gap 75.

The theorems: `OnBytes.WholeKey.wholeKeyPrivacy` (`lean/Johnson/WholeKey/Main.lean`) ·
`OnBytes.WholeKey.silent_good` (`lean/Johnson/WholeKey/Foes.lean`) · `OnBytes.WholeKey.real_real`
(`lean/Johnson/WholeKey/Half.lean`) · `OnBytes.WholeKey.FoeScheme.one_le_of_event`
(`lean/Johnson/WholeKey/FoeScheme.lean`) · `AtPublicFiles.ZetaAt.privacyWithNumber_description`
(`lean/E2E/ZetaAtCaps.lean`) · `AtPublicFiles.LinkLaid.linkLaidAtOnce`
(`lean/E2E/LinkLaidPrivacy.lean`).

Basis: proved (the theorems named; how to check them: `lean/THEOREM.md`, "How to check it") · by
reading (what the statement supposes and leaves out; what the view holds; that the statement with
this simulator would be false at two instances in a proof) · computed (the 26 files, by the import
lines; where the error reaches 1; that a prover that tells its index is ruled out no sooner).

### The link proof's honest prover, written in Lean, and its files

**L65.** This entry is about the link proof's honest prover (all three: L88). The link proof shows
that a copy and the first table encode the same weights. Before hashing, at full size, Lean proves
perfect honest-verifier zero knowledge for it (`homeExactAt`). A written simulator is given the two
tables' OOD seeds and answers, the verifier's challenges and the columns opened in the two tables.
It produces exactly the distribution of what the link proof's honest prover, as written in Lean,
discloses. That holds for all weights, all encoding randomness and every challenge, with no error
and no premise. So, to an honest verifier, its messages add nothing to what these columns and
answers already show. This is no statement that the weights are hidden: answers and columns are
computed from them. At full size, where the tests on the public files pass, the link's verifier
accepts the same prover at every challenge that passes proof of work, for all weights, at one fixed
public-files digest, at which `verify` is not proved ever to be called. What the conditional theorem
says with this prover beside two fixed-message provers: L64.

Its files lie under `lean/Johnson/Prover/`, and what states their conditions under
`lean/Johnson/Goal/Conditions/` and `lean/Johnson/Goal/Meaning/`. By name:
`Johnson.Prover.Link.link_yes` (`lean/Johnson/Prover/Link/LinkJoinF.lean`), `FlashProve.linkFits_at`
(`lean/Johnson/Goal/Conditions/LinkFitsAt.lean`), `FlashProve.dec_at_D`
(`lean/Johnson/Goal/Conditions/LinkDecAt.lean`) and `FlashProve.completeOn_last`
(`lean/Johnson/Goal/Conditions/HomeLast.lean`); the theorem of honest-verifier zero knowledge before
hashing, `OnBytes.LinkSim.AtHome.homeExactAt` (`lean/Johnson/LinkSim/AtHome/HomeExactAll.lean`).

On hiding: none of these files says how likely any random value is. Every pad, tail, mask and salt
in them is a free letter or, where the file says so, a written constant. Where they say that such
values "fit", they mean lengths, ranges and the format's own tests on bytes, which constants can
meet too. No result on hiding in this library rests on them alone.
`lean/Johnson/Prover/Link/LinkCoin.lean` fixes the finite type of the link prover's own pads, tails
and masks; salts are not in it. The statement of zero knowledge that rests on these files,
`homeExactAt` (`lean/Johnson/LinkSim/`), draws those values uniformly and holds for all encoding
randomness of both tables. Files with Toy in their names are tests on made-up numbers: their "coins"
are a written formula.

Basis: proved (the theorems named; how to check them: `lean/THEOREM.md`, "How to check it") · by
reading (what the prover's files say and do not say of random values; what `LinkCoin.lean` holds;
the files with Toy in their names).

### Statements on hiding that have not been independently reviewed

**L66.** The statements of the results on hiding at the default setting (L62 to L65, L91; of L93,
the corollary at every request and the field `zeroKnowledge` in its two forms), and the definitions
beneath them that do not lie beneath the statements of the six theorems, have not been independently
reviewed. Lean's kernel checks their proofs.

Basis: not shown in this repository (a sentence on what has not been done; nothing here can check
it).

### That `verify` rejects no other policy rests on a reading

**L67.** The soundness theorem on `verify` speaks at parameter files whose policy asks that every
output token be the model's own: `Inst.Model.AcceptancePolicy.exact`
(`lean/Inst/Model/ProgramR.lean`), the three numbers 256, 256 and 0. Exact match is a premise on the
parameter file, not a test in the text of `verify`; files with other policies are in scope (a
theorem at the second written copy: `VerifierAndGoals.filesRead`
(`lean/Johnson/Goal/Files/FilesReadProof.lean`)), and at one of them, the second stored set's, the
executable form of `verify` accepted proof files of the programs' prover, at full size, on synthetic
weights (evaluated, no theorem; that an honest run of the prover made them is shown by nothing in
the files: `lean/THEOREM.md`, "What has been run"). That nothing deeper inside `verify` rejects
other policies rests on a reading of its text; no theorem says it. So a user has to check the policy
in the parameter file (`lean/GAPS.md`, gap 44).

Basis: proved (`VerifierAndGoals.filesRead`) · by reading (that `verify` holds no test of the
policy) · tested (the accepts under the second stored set's policy: `lean/THEOREM.md`, "What has
been run").

### The set of possible weights sets the limit

**L68.** This entry is about the index binding that the soundness theorem on `verify` states. If the
set of possible weights held weights under which every instance counts as the model's output, index
binding would rule out nothing. It rules out an accepted output that the one extracted index does
not explain; for a single proof, read from outside, that says no more than: some index of the set
explains it. What it adds to that is the order: the index is settled by the commitment and the
committer's hash queries, at the given public files, before any proof.

Basis: by reading (the statement of `VerifierAndGoals.AtTheName.sound_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyAt.lean`); no theorem says it).

### The library's written copies of the public files

**L69.** The public files (`VerifierAndGoals.PublicFiles` (`lean/Ladder/Stored.lean`)) are
parameters of the argument and of the relation. They are fixed before the oracle is sampled,
although whoever commits writes the scale file. The library holds, as Lean terms, written copies of
two sets of them, a full-size set that states exact match and the same set with a tolerant policy:
`VerifierAndGoals.storedPublicFiles`, `VerifierAndGoals.zGap` (`lean/Ladder/Stored.lean`). These two
sets are "the two stored sets of public files" of these pages, and the two Lean terms "the library's
written copies" of them. No theorem ties the copies to files on disk. The command `lean-verify`, at
run time and inside `verify`'s scope test, compares the layout file whole, and the parameter file
but for its eight free numbers, with the first copy's text; it compares the scale file with nothing,
and it never tests that the files on disk are one of the two copies. From outside Lean,
`lean/scripts/check_stored_examples.py` compares the two terms' text with the example files under
`examples/full-size/config/` and `examples/full-size-clipped-gap/config/`; by its own head it
catches accidents and drift, and is no defence against a change that is made to deceive it.

That the tests on the public files (`FlashProve.protocolDataWellFormed`
(`lean/Johnson/Goal/Description/Live.lean`)) pass is proved at the two copies, and at the first copy
under every other policy in scope (with only the policy's three numbers changed, within the four
bounds that `theLive_zAt` asks of them), in a side library: `AtFullSide.Top.theLive_zFull`
(`lean/AtFullSide/Top/LiveAtFull.lean`), `AtFullSide.Top.theLive_zGap`, `AtFullSide.Top.theLive_zAt`
(`lean/AtFullSide/Top/LiveAtPolicies.lean`). That this repository's files equal these copies is
checked by a script (`lean/scripts/check_stored_examples.py`: 90 comparisons, 11 of them against
this repository's example files), not by a theorem; run over this repository's files, it passed. The
three speak of one layout file, one scale file and one setting of five of the parameter file's eight
free numbers, those of `VerifierAndGoals.storedPublicFiles`. Only the policy's three numbers vary:
exact match (`VerifierAndGoals.storedPublicFiles`), (25856, 512, 1) (`VerifierAndGoals.zGap`), and
every `C`, `theta`, `cap` with 2^8 ≤ `theta` ≤ `C` < 2^32 and `cap` ≤ 1,024
(`VerifierAndGoals.zAt`). At files in scope with another scale file, or with other values of the
five numbers, that the tests pass is not proved: there the soundness theorem on `verify` may hold
only because `verify` rejects everything. `protocolDataWellFormed` reads no proof: a yes is no sign
that `verify` accepts any proof (`lean/GAPS.md`, gaps 52 and 73; what is known of acceptance: L9).
It is one of the conditions on the public files under which most statements of [TERMS.md](TERMS.md),
table 6, are stated.

At `theLive_zFull` the independent checker cannot give a verdict (L80). Some constants beneath the
side library's theorems fail in Lean's kernel at the default thread stack and pass at a larger one,
at which that library is compiled; `leanchecker`, which has no option for the stack, fails on them,
so the script does not hand them to it: all twenty-three modules of that library that are shown to
need the larger stack, with every other module of `AtFullSide/` and `ShapeLines/`, are sent past
`leanchecker` by the script, to Lean's own replay at the wider stack ([CHECKING.md](CHECKING.md)).
(Seen for twenty-two in runs over Lean files that differ from this repository's, `lean/GAPS.md`, 73,
and for `AtFullSide/Layout/TieRfl.lean` on two machines, `scripts/RULES.txt`.) All twenty-three pass
at that stack (nine under `AtFullSide/K12/`, seven under `K14/`, three under `K10/`, one each under
`K2/`, `K13/`, `M1/` and `Layout/`; by name: `lean/GAPS.md`, 73).

The soundness theorems, on `verify` (`sound_of_verify_at`), the compiled statement of soundness at
files that are taken (`finalSound`), the executable form's two (`theForm_eq_verify`,
`sound_of_the_form_events`), and soundness as an IOP with its figure, do not depend on these
constants: no file beneath any of these theorems imports the side library (`lean/GAPS.md`, gap 73);
the line `sound` (L93) is `finalSound` at a `PublicSetup`'s files, but its own file,
`AtFullSide/Face/TheSixLines.lean`, is of the side library, and by import lines modules of all
twenty-three lie beneath it. The theorems that show the stored full-size files meet
soundness-as-an-IOP's three conditions rest on at least one of these constants, by way of
`theLive_zFull` (`filesInUse_stored`, `statementAtStoredFiles_holds`,
`AtFullSide/E2E/SoundAsIOPAtWritten.lean` and `AtFullSide/E2E/SoundAsIOPNumbersAtWritten.lean`).

By import lines a module of at least one of the constants beneath the side library's theorems that
fail at the default stack lies beneath the module of each of `complete_in_scope`,
`zkOnServedRequests_inScope`, `completeOnServedRequests_at_every_files_in_use`,
`finalAtT1_filled_withRoom`, `finalZeroKnowledgeOneBit_value`, `threeAtFiles_in_use`,
`theFinalStatementHolds`, `finalRefusedHandsOutNoProof_value` and `theFinalStatementOneBitHolds`,
and of `offline_at_one_protocol` (L90) and
`VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes` (L93;
its premise: the first worst-case check, or the least-bound check with numbers that hold), and of
`finalSoundAndBinding_value` and `finalHandsOutNoProof_value`. By a walk over the constants of the
build of this repository's files that [CHECK-RESULTS.md](CHECK-RESULTS.md) tells as made in seven
calls, proofs included (a program's finding, no theorem; it takes as given the twenty-three modules
that `lean/GAPS.md`, 73, names, and measures no stack), `finalSoundAndBinding_value`,
`finalHandsOutNoProof_value` and `finalRefusedHandsOutNoProof_value` (and `rejectsNoProof_value`,
which this entry does not otherwise name) reach no constant of these modules, and each of the others
reaches at least one. By import lines modules of all twenty-three lie beneath the module of the six
lines of L93 too (`AtFullSide/Face/TheSixLines.lean`); the walk over the constants says nothing of
the six. No module of the side library lies beneath those of `sound_of_verify_at`, `finalSound`, the
executable form's two (`theForm_eq_verify`, `sound_of_the_form_events`), `soundAsIOPAtTheProtocol`
and `probabilityInScope` (modules, not constants).

`ShapeLines/` is a third library of the Lake file; it is not itself a default target (the side
library reaches all its files but three through its imports, so the default build compiles all but
those three), and it has a larger thread stack of its own: closed equations, each resting on one
evaluation by Lean's kernel, on how the structural checks of the proof file's chains run at the full
size of the stored example: they read no field element and show no step to accept. All its files but
three (two of controls, and `LastChain/LastRunAtBorder358.lean`: L95) lie beneath the theorems of
L90 to L93, and no independent checker has replayed them (`lean/ShapeLines/README.md`, "Limits").

The library's full check names all three libraries of `lakefile.toml` in its build step,
`ShapeLines` too, three of whose files no other target reaches, and hands Lake a bound on parallel
work, which that library's heavy files need; the modules of that library and of the side library are
replayed by Lean's own replay under a wider stack, not by `leanchecker`
([CHECKING.md](CHECKING.md)). It has been run over this repository's files but the one added
afterwards (the head of this page), and has passed ([CHECK-RESULTS.md](CHECK-RESULTS.md)). The
script's last line also says that no theorem got a verdict on binders or on `Classical.choice`:
every line of `scripts/top-theorems.txt` says "general" (L24).

Basis: proved (the three theorems named) · by reading (what `lean-verify`, the scope test and the
script compare; that no theorem ties the copies to files on disk) · tested (the kernel at the two
stacks, and `leanchecker`: over copies of the Lean files that differ from this repository's; over
this repository's the kernel at the larger stack alone, in the full check's replay:
`lean/GAPS.md`, 73) · computed (what lies beneath what: by import lines; which constants a theorem
reaches: the walk, whose tables are not in this repository).

### The digest checks on the written copies are evaluations

**L70.** Five compiled `#guard` checks (among the files' other guards) ask that a digest equal a
written value: one for each copy (`lean/Ladder/Guards.lean`), and three, against sums taken of the
example's files outside Lean, on `zStoredFull`, a third term whose layout and scale fields are
`storedPublicFiles`'s own (`lean/Ladder/Stored.lean`) and whose policy is written as another term
(`lean/Johnson/Top/Own/OwnStoredFull.lean`); the three checks are in
`lean/Johnson/Top/Own/OwnStoredFullRun.lean`. A sixth, a control in the same file, asks that a
turned layout's digest differ from the written value. They are evaluations, not theorems.

Basis: by reading (the `#guard` lines of the two files) · computed (the count, by a search of the
files' text).

### `SoundFor` says as much as its claim says

**L71.** `SoundForWith` is the text of `Sound` with the claim as a parameter and the extractor as an
argument; `SoundFor` says that there is such an extractor, and `Sound` is `SoundFor`'s case at the
claim that the output is the model's: `VerifiableInference.sound_iff_soundFor`
(`lean/VerifiableInference/MoreStatements.lean`). It says as much as the claim says: a claim that
some weights meet at every prompt and output makes `SoundFor`, in which the extractor is not named,
true of every system (an argument; no theorem states it).

Basis: proved (`sound_iff_soundFor`) · by reading (the argument on `SoundFor`).

### `SoundForWith` and the definition's form: two arrows, no stated equivalence

**L72.** Between `SoundForWith` and the definition's form with the extractor named,
`ZKCP.HasIndexBindingWith` (`lean/ZKCP/Defs.lean`), a theorem leads each way, general in the system
and the claim, and none states the two as one equivalence:
`VerifiableInference.soundForWith_of_indexBindingWith`
(`lean/VerifiableInference/AgreementWith.lean`),
`VerifiableInference.indexBindingWith_of_soundForWith`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`).

Basis: proved (the two theorems) · by reading (that none states an equivalence).

### Refined completeness: where it is proved

**L73.** The refined form of completeness, with the committer's and the prover's errors apart, is
`ZKCP.HasRefinedCompletenessError` (`lean/ZKCP/Defs.lean`). By a search of the files' text, no
theorem states it of a scheme of this protocol. What is proved of it is general or of made-up
schemes: perfect completeness gives it, at the errors 0 and 0, where instances and witnesses are
countable (`ZKCP.refined_of_perfect`, `lean/ZKCP/RefinedOfPerfect.lean`); a toy scheme meets it
(`ZKCP.toy_refined`, `lean/ZKCP/Sanity.lean`); a made-up scheme fails it (`ZKCP.sep_not_refined`,
`lean/ZKCP/Sep41.lean`). No definition or statement in a file under `lean/VerifiableInference/`,
`lean/Ladder/`, `lean/Johnson/` or `lean/Policy/` names it; two comments under `lean/Johnson/` name
its general form, `ZKCP.Gen.HasRefinedCompletenessError`, to say that their files do not speak of
it.

Basis: proved (the three theorems named) · computed (a search of the files' text).

### Two theorems on the guard speak of the first chain's run alone

**L74.** The guard in `verify` is `VerifiableInference.Desc.Chain.guarded`
(`lean/Johnson/Desc/SeatGuard.lean`), laid by `VerifiableInference.Desc.First.firstChain`
(`lean/Johnson/Desc/First/Driver/Chain.lean`). After every step of the proof file's first chain
except the one that receives the next token, the verifier checks that its own stored value of that
token is unchanged, and rejects the proof if it has changed. It is a test on the verifier's own
bookkeeping, not on anything that the prover sends. The definitions lay the same test at two more
places: on what is joined behind a step, and on the first half of the step that receives the token,
so that only the decision of the half that receives it is free: `ProofFile.chainBy`
(`lean/Johnson/Desc/ProofFile/Frames1.lean`), `ProofFile.h1Own`
(`lean/Johnson/Desc/ProofFile/Lots/H1.lean`). That the guard only rejects more is a theorem, general
in the sub-protocols that are laid in, under one premise on the batching, which is proved of the one
batching that is laid in. That the first chain's run is the same without it is a theorem under
premises, which are shown of the proof file's own sub-protocols. The two:
`VerifiableInference.Desc.First.firstChain_chainAt`,
`VerifiableInference.Desc.First.firstChain_strike` (`lean/Johnson/Desc/Sound/GuardAtDriver.lean`).
Both speak of the first chain's run, and of the test that `firstChain` lays alone. The guard, whole:
`lean/GAPS.md`, gap 68.

Basis: proved (the two theorems) · by reading (where the definitions lay the test).

### Lines in comments that name a reading

**L75.** A comment in a Lean file may name a reading of its file. Such a line is no independent
review: the reading was made within this project; the line tells of that reading alone, and of the
part of the file that it names; and it does not say that the proofs were read (Lean's kernel checks
those). Nothing in this repository backs such a line. The line may be older than the comments beside
it. Where a file names no reading, none is claimed; the files under `lean/ThirdParty/` name none.
The comments have not been independently reviewed. Nothing hangs on such a line: a comment is not
checked by Lean, and where a comment and a statement disagree, the statement holds (L23, L43).

Basis: not shown in this repository (what such a line stands for; nothing here can check it).

## 9. Further limits

Paths in this part are from `lean/`, but for those that begin with `verifier/` or `docs/`, which are
from the repository's top.

`Entry.check` and `Key.check` take the table's shape from their caller and do not test it; the
parameter reader does.

### What the full check does not build, replay or test

**L76.** `scripts/check.py` reads the 13 files under `Ask/` by its checks of the files' text alone:
it does not build, replay or audit them. Mathlib and the other packages are used as they lie,
neither rebuilt nor replayed.

The script pins twenty-nine files by checksum (`GOAL_SUMS_TEXT`), all alike, byte for byte. Nineteen
of them state the goals, or statements, definitions and stored terms that the goals are written in:
`Ladder.lean`; `Bits.lean`, `Package.lean` and `Stored.lean` under `Ladder/`; `CanServe.lean`,
`ModelWeights.lean`, `MoreStatements.lean`, `RandomOracleModel.lean`, `Statements.lean`,
`Steps.lean`, `AtEveryRequest.lean`, `AtEveryRequestGuards.lean`, `RequestResult.lean` and
`WellFormedRequests.lean` under `VerifiableInference/`;
`VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean`; `Checks.lean`, `FinalStatement.lean`
and `FinalStatementOneBit.lean` under `Johnson/Face/`; and `AtFullSide/Face/TheSixLines.lean`. One,
`VerifiableInference/StatementsNonEmpty.lean`, states further forms of those statements, in which no
goal is written. The form `CompleteOn` (`VerifiableInference/Steps.lean`) is that of the line
`completeOnCanServe` (`AtFullSide/Face/TheSixLines.lean`); theorems in other pinned files tie that
form to the others in which the goals are written (among them `completeOn_iff_proofAccepted`,
`Ladder/Ties.lean`, and `finalComplete_iff_completeOn`, `Johnson/Face/Checks.lean`). The other nine
state no goal: they hold theorems and tests about the goals and about what the goals are written in,
and a few definitions of their own, some named by theorems (the error term `levelError` in
`Ladder/PackageBits.lean` is one) and some only by tests; among them is `ArgumentSystem.ofArgument`
(`VerifiableInference/OfArgument.lean`), on which the goals' verifier is built. The script pins
nothing beneath the twenty-nine, though the goals name definitions that lie beneath them,
`innerCompiledVerifier`, `settingsAtRef`, `requestOutcome` and `compile` among them (what that pin
is worth: below, at "Some of its lists are made by a program").

The script compares the stored statements of the twenty theorems of
`AtFullSide/Face/TheSixLines.lean`, the six lines among them, like the others
(`scripts/front-statements.txt`: 188 blocks); it does not ask that they be stored: that rule covers
files under `VerifiableInference/` alone; the list of stored statements is held by its checksum in
`check.py`. Only the statement is compared; the definitions that it names are not. The files in
which the statement of the completeness theorem at weights that pass a worst-case check, its premise
and the checks are written (`VerifiableInference/Bounds/SomeWorstCaseCheck.lean`,
`VerifiableInference/Bounds/NeverFails.lean`,
`VerifiableInference/Bounds/LeastBoundNeverFails.lean`,
`VerifiableInference/TheModelsOwnOutput.lean`, `IntegerModel/Bounds/Check.lean`,
`IntegerModel/Bounds/LeastBoundCheck.lean`, `IntegerModel/Bounds/LeastBoundLemmas.lean`,
`IntegerModel/Bounds/LengthCheck.lean`, `IntegerModel/Bounds/Lengths.lean`,
`IntegerModel/Bounds/DualColumnBound.lean` and `IntegerModel/Bounds/GramIteration.lean`) are not
among the twenty-nine.

The soundness theorem on `verify` is not among the theorems for which the audit lists the
definitions beneath the statement (`scripts/listing-for.txt`). The script plants no false name among
the named theorems, and its one planted control, a file that panics, is a control of the build. It
runs no tests that change the source (L26) and no independent proof checker (L25), its kernel replay
covers this library's modules alone, and it opens no page.

Some of its lists are made by a program from the very files that are checked: all of
`long-lines.txt`; some of the rows of `guards.txt`; the lines on `Johnson/` and `Ladder/` in
`IMPORTS.txt`; some of the characters of the table of allowed characters (`SIGNS`); the stored sums
of some of the pinned files, `Ladder.lean` and `VerifiableInference/Statements.lean` among them, and
of four of the 14 files under the guards of `verify-on-bytes` (`OnBytes/Guard/Program.lean`,
`OnBytes/Shell/Front.lean`, `OnBytes/Shell/FrontSame.lean`, `Run/Blake2b/LoadThm.lean`); and the
file named in many rows of `claimed-theorems.tsv`. For these a "passed" says only that files and
list agree: it guards against drift and cannot fail over this repository's files. Of the 188 blocks
of `front-statements.txt`, 184 are Lean's own print, with the audit's options, over a build of Lean
files that differ from this repository's nowhere but in comments, in docstrings and in the text of
43 strings; none of these was stored from a listing over a build of this repository's own files: so
the comparison fails only where Lean's print of a statement over this repository's build differs
from that print. The other four are the statements of the four theorems of
`AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean`, the file added after the runs (the head of
this page). The verdicts that can fail: the stored sums of the other pinned files, the barred words,
the rules on `verify-on-bytes` but for those stored sums, the other rows of `guards.txt`, the other
lines of `IMPORTS.txt`, the stored statements, the build, the kernel replay and the audit.

Basis: by reading (`scripts/check.py` and its lists) · not shown in this repository (which rows and
sums a program made from the files: nothing in the lists tells them apart).

### The order of draws in one sumcheck of the C++ verifier

**L77.** This is a limit of the C++ verifier, not of Lean. In the sumcheck whose claimed sum (`C` in
the code) names entries of `U3`, a vector committed later (`verifier/src/vf_layers_check.inc`;
`docs/format/11-1-machinery.md`), the points that define the `U3` tables named by the claimed sum
and the summand must be drawn before the first challenge, eps, or those entries are not functions of
the cells alone. `verifier/src/vf_sumcheck_psc.h` states the general rule as the caller's duty: eps
must come after everything that `C`, the summand and the variables' weights depend on; of that,
`pscBegin()` checks only that each slot that occurs in `C` has its hidden value. No flaw is known:
that the verifier keeps the rule at this sumcheck rests on a reading of the code. No test or
self-check enforces it, so a change of the code could break it unnoticed.

So add that condition when changing the verifier or formalising this step.

Basis: by reading (the three files named; by reading, not machine-checked).

### A verdict of the typed verifier computed on bytes: an unchecked length, and a related case

**L79.** This is about `TypedOracleCompiler.Compile.Batch.verifyOneProtocol` run under the family
`gJ`, which turns a function on the format's byte strings into answers for typed queries and answers
zeros where the page, a datum of `gJ`, writes no string for a query (V10, "Families that answer
zeros"). It is not about `verify`, and neither `cp_verify` nor `verify-on-bytes` computes this
verdict: each runs its own text (of `verify-on-bytes`: by its import lines, which reach neither
definition; no theorem says it). Of the runs of the executable form of `verify`: V10, "Families that
answer zeros".

Once the hash chain has joined, `verifyOneProtocol` tests neither the length nor the contents of the
salt of the request's leaf. At a salt of another length the check in the request tree has one
verdict at every value of the slot (`reqCheck_hole`). No law says that this verdict is a yes; but
root, path and slot are fields of the prover's own proof string, so, by reading the check's text, a
prover can make it one, and the second chain's draws then do not depend on the first chain and the
request (by reading, not machine-checked).

A second unchecked case of the same kind stands at the leaves of a tree: at leaves for which the
page writes no string, two checks of `verifyB` along one path to one root have one verdict
(`runCheck_hole`), and the digests that `verifyOneProtocol` asks are zeros (`leavesV_hole`); neither
is carried to a verdict of `verifyOneProtocol`. Whether a prover's string can reach such a leaf is
not said.

What a prover could gain from either has not been worked out. No false proof is known. The theorem
on `innerCompiledVerifier`, whose oracles are typed and random, is not touched: there another salt
is another leaf. But no theorem carries a yes computed under `gJ` to that theorem, and no law names
such a yes as its premise; the laws that hold at every family say nothing of a drawn hash function.

The wrapper `verifyGuard` (`OnBytes/Maker/Page/GuardVerify.lean`) refuses every other length of that
salt. It states nothing on soundness; its yes is carried to no drawn hash function; with it, too,
zeros are answered at a chain's first query for the blocks before the last, where the page's `seeds`
and `link` write nothing: always under the proof file's tag; it always says no on a copy's file (by
reading, not machine-checked); and that any real file gets a yes from it, or that an honest file
passes its test of the salt (`rsaltFit`), is not proved (a run on the stored small example's parsed
files: [Ask/README.md](Ask/README.md)).

Basis: proved (`reqCheck_hole`, `runCheck_hole`, `leavesV_hole`) · by reading
(`OnBytes/Maker/Page/GuardLaws.lean` and `GuardVerify.lean`, with their comments; no theorem says
it) · computed (the import lines beneath `OnBytes/Main.lean`, followed by program).

### Four theorems at which the independent checker gives no verdict

**L80.** But for the independent checker's passes on the soundness theorem on `verify` and on three
of the six lines, none of what follows was run over this repository's files. At
`Bind.Cpp.extractsCommitted`, `Bind.Cpp.bindsAt` and `Bind.Cpp.soundAtCommitted_own` (L61) and, of
the side library, at `AtFullSide.Top.theLive_zFull` (L69) the independent checker cannot give a
verdict: what they depend on outgrows a limit of its own, a table of 2^31 entries. That is no
refusal, and more memory would not help with this binary. For these four theorems there is Lean's
own kernel alone.

Over a build of this repository's files the independent checker (that the compiled files that its
passes read were that build's is known from a report alone; Lean's own files were not compared with
a list of checksums) has accepted the soundness theorem on `verify` (`sound_of_verify_at`), with
every declaration beneath it, and nothing that does not lie beneath it, in a pass on that theorem's
export alone ([CHECK-RESULTS.md](CHECK-RESULTS.md); what such a yes is worth, and why a reader
cannot repeat it: L25). Of the six, the independent checker has accepted `sound`, `repliesFit` and
`refusedHandsOutNoProof` by name, over a build of this repository's files; over such a build the
three on binding, completeness and zero knowledge have been checked by Lean's kernel alone. So, but
for the soundness theorem on `verify`, these three and those on which they rest, no theorem of this
repository has more than Lean's own kernel over this repository's files: not the results on hiding
of L62 to L65, not the other three of the six lines, not the theorems on completeness and zero
knowledge of L88 to L93. No run shows the checker's binary refusing a wrong proof: none was made.
The binary was compiled by this project, offline and with locked dependencies, from an archive of
the checker's public source (nanoda_lib 0.4.13, commit 418320295890faed83a96fd97907b12a3b6728c2).
Not compared: that archive against the public repository itself; the libraries that it is built
with, beyond their locked checksums; the compiler and the linker. The declarations of Mathlib, of
two further packages and of Lean itself are read from the copies on the machine where it runs (L25).

Basis: by reading ([CHECKING.md](CHECKING.md), "The independent checker") · not shown in this
repository (the checker's passes over a build of this repository's files:
[CHECK-RESULTS.md](CHECK-RESULTS.md) quotes their prints; the prints, the exports and the exporter
are not here).

### The soundness proof runs by list decoding

**L81.** The soundness proof runs by list decoding up to (just inside) the Johnson radius. Where a
sampled oracle message is committed at a radius of at least half the code's distance, its Merkle
root fixes only a short list of codewords, and the out-of-domain sample picks at most one of them,
but for a chance of a clash that the bound includes. That the proof takes this road is read from its
text and from the list of what the compiled theorem depends on; no theorem says it. At all written
pairs of shape and radius of the proof file the radius is at least half the distance (where a
stage's rows lie in two codes, the smaller of their two distances): theorems on the written numbers:
L89. (The coding theory on which that rests: L15.)

Basis: by reading (the proof's files) · proved (on the library's written lists: the files that L89
names) · not shown in this repository (the list of what the compiled theorem depends on).

### Further limits of the named hypotheses of `innerCompiledVerifier_sound`

**L82.** These are limits of the theorem on `innerCompiledVerifier` (V3, V9 to V11) and, in the last
two bullets, of `OnPublicFiles.verify_sound` and of `verify-on-bytes`. None is a limit of `verify`.

- **`commitment` is of another kind** than the other named hypotheses: its premise follows from
  them, so under them it asserts its conclusion outright, index binding of the whole scheme behind
  the commitment. It binds every committer and prover within their query bounds, so it is a
  hypothesis on a cheating prover, not a fact about a map, and the road of the theorem on
  `innerCompiledVerifier` takes that step as a hypothesis and does not prove it (where the
  implication is a theorem: V11).
- **`commitment`.** `CompilerSoundnessConditionStatements.commitment` holds of itself where its
  error `εId` is infinite, and where the key's code is not one to one this library does not prove
  it. The hypothesis `Hole.commitment` (of `OnPublicFiles.verify_sound`, below) is a theorem where
  no two keys have one code, at the library's extractor, which inverts the code by choice, and at
  the error (t + 2)² / 2^256 (`Hole.commitment_of_code`, `Johnson/Top/OnFiles.lean`); where the code
  is not one to one it is open.
- **`proofSound` and batches.** At the two IOPs (`innerCompiledVerifierSoundFromDryRunAtFullSize`,
  `innerCompiledVerifierSoundFromDryRunAtSmallSize`)
  `CompilerSoundnessConditionStatements.proofSound` is asked of every `G`: a depth and rounds that
  nothing ties to the programs' plan. With more than one slot and rounds tuned to 2^-128 it may be
  false, and the theorem is then vacuous, because a shared round's error is the joint error of all
  slots and a union bound over the slots cannot reach it; by the union bound each shared round would
  need slack. By the design, which no theorem here shows, the slots' bad messages are one set behind
  the shared point and the plan's error has the number of slots as a factor at one round alone; the
  rule for that road (`sndBKT_of_links`, `proofSound_at_links`) has premises that are shown of no
  file. By the coarsest count of a batch, in which every round of the proof file's shared chain is
  counted once for each of the 64 requests, six bits are needed, the shared chain's tight rounds
  stand within hundredths of a bit of 2^-128, and the stated error is not reached at the default
  numbers. The hypothesis asks only the joint error over the slots and is not shown false; no
  counterexample is known. All this is of the two IOPs: at `theDescription` the hypothesis is a
  theorem (V10).
- **In bits.** These are figures of the theorem on `innerCompiledVerifier`, not of the soundness
  theorem on `verify`, whose own error is written out on THEOREM.md (about 124 bits for each hash
  query). The error of `innerCompiledVerifier_sound` is n · `εs` + 2 (n + 1)² / 2^256 + `εId`(t)
  with n = 5 · (t + v + 1), where t is the committer's and the prover's hash queries together and v
  bounds the verifier's own typed queries. If all 16 hypotheses hold with every round's error at
  most 2^-128, the proof of work counted, that is about 125.7 bits a query, not 128; by the coarsest
  count of a batch, 119.7; with the proof of work counted for nothing, 93.7 (32 bits of work less,
  at rounds of the key file and the copy's file) and, by the coarsest count, 91.7 (28 bits of work
  less, in the shared chain). Each figure takes a code under which no two keys agree (`εId`(t) =
  (t + 2)² / 2^256). The figures 125.7 and 93.7 take the key file's and the copy's file's request
  trees at one leaf, a depth of 0; at that depth the factor in `keySound` (V10) is 1, and the
  written layout of the hash queries does not lay the key file's depth at 0 (V10). Each figure is
  (t + v + 1) divided by the error, in bits, so the verifier's own typed queries count among the
  queries; it holds as printed up to some 2^110 queries, and near 2^124 queries the first figure is
  up to one bit lower. This is arithmetic on the formula, no theorem, and none of these figures is a
  proved security level. None of the differences is a known attack: each is what the proof can show.
- **`sound` at the small size** is proved at the claim `claimsTrue`
  (`meaningConditionFromDryRunAtSmallSize_paid`), where it is nearly a definition and all the weight
  lies on `proofSound`. That claim's model, `nextOfDigits`, is not the small example's model, and
  that it returns a token at any list is not shown: if it never does, the claim holds of no request
  and `sound` holds vacuously. The small example's scale file is refused as not lawful, by an
  evaluation that is in no file of this library, and the step from what sub-proofs check to the
  truth requires a lawful table; so `proofSound` at that example's files cannot be expected to hold
  (by reading, not machine-checked).
- **`sound` joins two steps:** from the relaxed relation to the exact one, and from the exact one to
  "the output is the model's". The first is a duty of the model, and it is false for a model where
  the slack can move an output. For `innerCompiledVerifier` it is not proved for every claim.
- **`sound` at the full size** is a theorem at written claims on one relation, `RelL s`
  (`meaningConditionFromDryRunAtFullSize_paid`, `meaningConditionFromDryRunAtFullSize_paid_req`), if
  the builder and the model are those two and the table of scales is lawful. That relation is shown
  to be non-empty only at all-zero weights, on a request with no counted position (`Flat.relL_met`,
  `Johnson/Flat/ThreeFull.lean`). That `buildReq` builds that request is not shown: the theorem
  shows that the claim is not empty, and no more.
- **`encId_oneToOne`** says nothing where no key has a code; under `ShapeRoom` every key has one,
  and the two written grounds meet it (`encId_hasCode`, `room_recordGround`,
  `room_smallRecordGround`, `Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean`).
- **What is no hypothesis.** The order of commitments and draws, the content of each chain's first
  query and the sameness of data across chains are properties of the IOP, not hypotheses of the
  theorem. Neither of the two IOPs (`innerCompilerInputFromDryRunAtFullSize`,
  `innerCompilerInputFromDryRunAtSmallSize`) is written out whole (V2), and a hypothesis that is
  silent on these properties is true or false by what is left open.
- **One commitment, one proof.** `innerCompiledVerifier_sound` and `OnPublicFiles.verify_sound` are
  each stated for one commitment and one proof. The library's step to many proofs under one
  commitment (`SoundForWith.manyProofs`) is not applied to them.
- **`VerifiableInference.OnPublicFiles.verify_sound`** (L53, row 3′), the theorem over another form
  of the compiler, is conditional on its own 22 named hypotheses. None of them says that its
  verifier accepts anything, and an IOP can make it say nothing (a builder that gives no instance,
  an encoder that gives no key a code, infinite errors, an empty relation). The 22 speak of five
  sub-protocols, where the 16 of the theorem on `innerCompiledVerifier` speak of the three files'
  whole protocols: the smaller count comes from where the hypotheses are laid, not from proofs (by
  reading: the structures `Core` and `CompilerSoundnessConditions`). Its `verify` is
  `OnPublicFiles.verify`, not the Lean verifier.
- **Of `verify-on-bytes`** no theorem states what the commitment ID binds: the key file's proofs,
  the copy's file, the request file, the output file and the proof file do not enter the ID. The
  number 128 in `main_zero_id` is what the options' field holds, also if the call names no bits;
  that any round's error is below 2^-128 is not stated ([OnBytes/LIMITS.md](OnBytes/LIMITS.md)).

Basis: proved (`meaningConditionFromDryRunAtSmallSize_paid`,
`meaningConditionFromDryRunAtFullSize_paid`, `meaningConditionFromDryRunAtFullSize_paid_req`,
`encId_oneToOne`, `encId_hasCode`, `room_recordGround`, `room_smallRecordGround`,
`Hole.commitment_of_code`) · by reading (the docstrings of the definitions under
`CompilerSoundnessConditionStatements`; the head of `Johnson/Flat/TwoSizes.lean`;
`Johnson/Top/OnFiles.lean`; no theorem says it) · computed (the six bits and the four figures:
arithmetic on the formula and on the written numbers).

### What `ZeroKnowledgeOn` covers, and what it leaves out

**L83.** `ZeroKnowledgeOn` (`VerifiableInference/MoreStatements.lean`) is the library's definition
of zero knowledge on a stated set of requests. It is proved of one system, the final system, on the
requests that can be served, at all public files in use
(`VerifiableInference.zeroKnowledgeOnCanServe`: L18, L93); the other statements on zero knowledge of
the protocol are in other forms, and each is told with its own limits (L91, L93). Seven limits are
the definition's own, and go with any theorem that concludes it. How a statement in this form can be
met trivially: [GAPS.md](GAPS.md), the appendix on gap 15, (7). All seven apply to L93's line on
zero knowledge, `zeroKnowledgeOnCanServe`, which is `ZeroKnowledgeOn` itself. To its corollary at
every request (`zeroKnowledgeAtEveryRequest`; the field `zeroKnowledge`) limits 1, 4, 5, 6 and 7
apply in full, and limit 2 but for its last sentence. Of limit 3 these apply to that corollary:
exact match alone; no batches; that what the prompts and output tokens themselves tell of the
weights is not covered; and that no theorem shows that a request to a real model is served; that
corollary speaks of every request (the one with the label shown, of every well-formed one).

1. It speaks of a system's honest committer and prover, which are Lean terms, not of the programs
   (L1).
2. It covers the weights alone. The scales (some 17 whole numbers a layer, fitted from the weights:
   L7), all sizes and all look-up tables are public. In the theorems that conclude it of the final
   system (`served_at_T1`, from one premise: L18; `zeroKnowledgeOnCanServe`, at public files in use:
   L93) the public files are fixed before the weights and are the same in both experiments, so what
   they tell of the weights is not counted (L7). What the simulator is handed of the weights
   (`publicParameters`) no clause bounds; at the final system it is nothing: that system has no
   public parameters (`Johnson/Face/Compiler.lean`).
3. It covers only requests in the stated set whose output tokens are the model's: in the theorems
   that conclude it of the final system (L18, L93), requests on which the integer model passes all
   its range checks on the whole window of 1,024 tokens (`CanServe`: L27). It says nothing about a
   request that fails or is rejected during proving, about the other proofs of a batch that holds
   such a request, or about outputs that another acceptance policy than exact match admits, where
   the answer itself tells how far a token lies from the model's choice ([GAPS.md](GAPS.md), the
   appendix on gap 15, (4)). Whether a request can be served depends on the weights and is not
   hidden, and at some valid weights none can be: there the definition speaks of the commitment
   alone (L27). Nothing shows that a request that the programs serve meets these conditions, and no
   theorem in the library shows that any request to a real model does (L27). So it cannot be said
   which real requests a theorem in this form would cover. What the prompts and output tokens
   themselves tell of the weights is not covered: the simulator is handed them.
4. The verifier's view is the commitment (256 bits), the proofs with their requests, the verifier's
   hash queries with their answers, and its own draws. What else a committer publishes, the key file
   with its OOD sample among it, is in the view only inside a proof, and not at all before the first
   proof.
5. The hash is taken as a random oracle, which the simulator answers in its place, and the honest
   side is taken to sample fresh uniform randomness at every step. Randomness that repeats is
   outside every statement: a mask or a pad entry that serves two runs is not covered, and hiding
   then fails, by a plain argument and no theorem: two values under one mask differ by a known
   combination of what they mask (for the programs: `docs/operators-duties.md`, rule 3). The
   programs derive their masks from a secret seed: there hiding can be computational at best, and
   the library defines no computational form (L62).
6. It assumes one commitment (L42), an honest provider without faults or restarts, one request per
   proof (L49), and somebody who counts all proofs made under the commitment (L84). Size and time
   are not modeled (L13), nor failures, memory, the order of work and what the proofs of one batch
   share.
7. Whether the definition says what a rendering in ordinary words says is by reading, not
   machine-checked (L50).

Basis: by reading (`ZeroKnowledgeOn`; `View`, `realExperiment`, `Simulator`,
`VerifiableInference/Statements.lean`; `CanServe`; the docstring of `PackageZeroKnowledge` in
`Ladder/Package.lean`; no theorem says it).

### What a bound on zero knowledge counts

**L84.** The bound in `ZeroKnowledge` and `ZeroKnowledgeOn` is a statistical distance at a given
number of the verifier's random-oracle queries and a given number of replies (`proofCount` in the
two definitions, which say "proofs"). It is not a security level. One figure for it is proved: of
the final system, on the requests that can be served, at all public files in use, there is a bound
that stays at or below 2^-154 up to 2^64 queries and 688,127 replies (L18, L93). The figures of L91
(2^-174, another 2^-135) belong to other statements, each over its own law; L93's 2^-154 for the
field `zeroKnowledge` (and the corollary `zeroKnowledgeAtEveryRequest`) is this same bound, carried
to another form at the same error (`zeroKnowledgeFollowsFromOn`); none of them is a security level
either. The conditional theorem's own error is of the same kind, a statistical distance between the
real and the simulated view at given numbers of hash queries and of proofs (`ZKCP.Gen.PrivacyFor`,
`ZKCP/Gen.lean`): its figure, 2^-135 (L64), is no security level either. All proofs under one
commitment count toward that number of proofs, and the definition's prover keeps no state, so it
keeps no count of them. Beyond the numbers at which a bound is stated nothing is said, of the proofs
already made either; that does not say that anything leaks. The programs' own limit of use counts
something else: batches of up to 64 requests, for each stored copy by itself. They stop a copy at
688,127 batches at full size, and no theorem ties that count to a number of proofs (L63).

The verifier is bounded only in its number of hash queries: its running time is not counted, and a
verifier's view has no field for time. At a bound of 1 or more the definition asks nothing
([GAPS.md](GAPS.md), the appendix on gap 15, (7)).

No bound in `CompleteSoundZeroKnowledgeOn`, the joint statement of completeness, soundness and zero
knowledge, is a security level either: its three numbers are error terms of three statements, each
under its own conditions.

The definition's other limits: L83.

Basis: by reading (the two definitions; `PrivacyFor`; `MaliciousVerifier.QueryBound`, `View`,
`ArgumentSystem.prove`, `VerifiableInference/Statements.lean`; the programs' accounting: L63; no
theorem says it).

### `Laid` and `LaidAlone` do not determine a block

**L85.** `Johnson/IMR/SeatForm.lean` defines the form in which a block stands in the proof file's
first chain. `Laid`'s second arm holds a block `q` that its equation does not determine: `q` stands
under "there is", and `Block.andThen` swallows its name and place. Where a statement needs `q`, a
seat at a link's first place hands it out by name (`seatedWith`); by that file's head `Laid` serves
`laid_planOk` and `yes_laid` alone. `LaidAlone` does not determine `b'` either: a statement is worth
its equation for `b'`, never `LaidAlone` alone. The file claims no soundness.

Basis: by reading (the definitions `seatedAs`, `seatedWith`, `LaidAlone` and `Laid`, and that file's
head; no theorem says it).

### Three comments under `Johnson/P1K8R/` say that premises follow from the head

**L87.** Comments of `Johnson/P1K8R/PieceAtRow.lean`, `WtBack.lean` and `BlindOwesAt.lean` say: "The
other premises here follow from the head; no file joins them to a member." In `k08_piece_at_row` the
premises `L`, `q₁`, `q₂`, `q₃`, `hG`, `hl`, `e3` and `hq` are taken beside the head in the
statement; the comments say they follow from it, and they do by lemmas elsewhere (`ground_at_head`,
`wt_back_at`, `k8Fence_at_head`, and, by reading, `k08_piece_at_maker` with `draw_at_flat`; the
fence at one base), but no file composes that derivation or joins them to a member.

Basis: by reading (the three comments; the statement of `k08_piece_at_row`; the statements of the
lemmas named, in `Johnson/P1K8R/` and `Johnson/Desc/First/K8/PieceEq.lean`).

## 10. Completeness and zero knowledge of the protocol

These entries tell what the library has on the protocol as a whole, at the honest provers as written
in Lean. What goes with each theorem is told under it. Paths in this part are from `lean/`, but for
those that begin with `guide/`, which are from the repository's top.

### How these theorems stand, and of what they speak

**L88.** The theorems at the heads of L89 to L93, and
`VerifiableInference.Compilation.finalAtT1_filled`,
`VerifiableInference.Compilation.theFinalStatementHolds` and
`VerifiableInference.Compilation.finalZeroKnowledgeOneBit_value` (L93), and with them
`VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes` (L93;
its premise: the first worst-case check, or the least-bound check with numbers that hold), are part
of this repository's Lean build, and for each Lean prints no axiom beyond its three standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

The theorem at the head of L89 stands in the main library. All the others, the two lines on
soundness among them (L69), stand in the side library (`AtFullSide/`), which rests on a third,
`ShapeLines/` ([ShapeLines/README.md](ShapeLines/README.md)): closed equations, each resting on one
evaluation by Lean's kernel, on how the structural checks of the proof file's chains run at the full
size of the stored example: they read no field element and show no step to accept. These two need
larger thread stacks and a large machine to build ([CHECKING.md](CHECKING.md);
[ShapeLines/README.md](ShapeLines/README.md), "How to build, and what it costs"); what goes with
that is told at L69. The independent checker has been run over a build of this repository's files;
what it accepted: [CHECK-RESULTS.md](CHECK-RESULTS.md). The Lean verifier's reference run has been
made over this repository's Lean files. The library's full check has been run over this repository's
files but the one added afterwards (the head of this page), and has passed. What has been run over
this repository's files: [CHECK-RESULTS.md](CHECK-RESULTS.md). For the theorems that this entry
names, but for `sound`, `repliesFit` and `refusedHandsOutNoProof` (L80), there is, over this
repository's files, Lean's own kernel alone: they do not lie below the soundness theorem on `verify`
(L80).

**The protocol and its honest provers, as written in Lean.** At given public files the protocol is
one Lean term, `AtPublicFiles.AtFiles.protocolAtFiles files` (`E2E/BridgeJoinAtFiles.lean`): an
interactive oracle proof (IOP) in three parts. Offline: the proof in the key file, on the committed
table. Link: from a further table (a copy) to the first. Online: the proof for one request, on that
further table.

Every committed table has an out-of-domain sample, offline and online: the verifier names a seed
(the sample's seed; the literature's "out-of-domain point"), and the sample is the seed with the
answers at it; the masking words that the provers send beside them carry none, by design.
("out-of-domain": see Words that this page uses.)

`protocolAtFiles files` is the object in the input at which `verify` calls the compiled verifier
(`object_description`, `E2E/DescriptionTie.lean`). The compiled verifier reads that object's
verifier side alone; that the encoder and the map to the out-of-domain answers are the protocol's
rests on their being fields of that term, on the decoder's clause at the matrices in range, and on a
reading of the format's pages that is not machine-checked — not on the verifier. It is built at the
format's second hash function, a fixed public function that the test on the public files reads too;
"before hashing" below means before the compiler's hash function, which is the random oracle of L93.

The honest provers are `AtPublicFiles.AtFiles.HonestTerm.honestProvers files (thePartsAt files)`
(`E2E/TheHonestProver.lean`, `E2E/KeyArgumentsAt.lean`). The theorems of L90 to L93 speak of this
triple with its online prover made to refuse a request that is not served
(`VerifiableInference.Compilation.theProvers`, `Johnson/Face/HonestProversWithCompiledPart.lean`).
The provers are Lean definitions, not programs that run: among other things the model's run on a
request is a specification, obtained by a non-constructive choice, and is not computed. Each theorem
below is about these definitions exactly as written, default values included. None of them says
anything of the released programs: the C++ verifier and committer and the CUDA prover.

**Their hypotheses.** Three tests on the public files; the completeness theorem at weights that pass
a worst-case check (L93) takes a premise on the weights as well: that they pass the first worst-case
check, or the least-bound check with numbers that hold; L92 and the compiled lines (L93) ask exact
match as well. The three tests: the files are in scope (`VerifierAndGoals.InScope files = true`: the
stored full-size layout file; the stored parameter file but for eight numbers, of which the policy's
`theta` is at least 2^8; any scale file that is read without error), they pass the test
`protocolDataWellFormed` on the public files (`protocolDataWellFormed (asDescriptionFiles files) =
true`), and they are read without error (`readFiles files = .ok parameters`). Public files that meet
the three tests and ask for exact match are called in use (`FilesInUse`,
`Johnson/Face/FinalStatement.lean`). L90 and L91 do not ask for exact match. An output that the
files' policy would accept and that is not the model's own is not served: L90 says nothing of it,
and at L91 the prover shows nothing there. The library's stored full-size files,
`VerifierAndGoals.storedPublicFiles` (`Ladder/Stored.lean`), meet all of these (`premises_zFull`,
`AtFullSide/Bind/LiveAtNamed.lean`; `filesInUse_stored`,
`AtFullSide/CompletenessAndZeroKnowledge/LinesAtStoredFiles.lean`). They are values written in Lean,
tied to no file on a disk. Of public files with another scale file, a real model's among them, the
library does not show that they pass the test on the public files (L69): of such files the theorems
on completeness and zero knowledge (L90 to L93) say nothing unless that is shown.

Basis: by reading (the statements and definitions named; what no theorem says).

### Soundness, as an interactive oracle proof

**L89.** Proved in Lean: `AtPublicFiles.AtFiles.soundAsIOPAtTheProtocol`
(`E2E/SoundAsIOPAtFilesProofs.lean`; the statement: `E2E/SoundAsIOPAtFiles.lean`). It is round by
round: each of the three parts is stated with a set of doomed partial transcripts and a bound on the
chance that one round's challenge leaves it. The knowledge in it is the committed weights: one fixed
decoding function reads them off the committed table, without rewinding the prover. Each round's
bound is at most 2^-128 of all that round's challenges, the proof-of-work bits among them. For one
run of the whole protocol (one committed table, one copy, one request) and against every prover, the
chance that all three verifiers accept while the weights decoded from the committed table are
missing, are not what the copy decodes to, or do not give the claimed output under the files' policy
is at most 67,391 × 2^-96, which is below 2^-79 (`AtPublicFiles.AtFiles.probabilityInScope`,
`probabilityInScope79`, `E2E/SoundAsIOPNumbers.lean`). That chance is over uniform out-of-domain
points and over uniform challenges whose proof-of-work bits are 0, the only ones at which the
verifiers accept. 67,391 is the number of rounds; 2^-96 is 2^-(128−32), 32 being the most
proof-of-work bits of any round.

*Limits.* It is a statement before hashing. It is not "128 bits a round": among the challenges that
pass the proof-of-work tests a round's bound is 2^-128 times 2 to the number of that round's
proof-of-work bits, so 2^-96 at 32 bits. Its figure is not the compiled system's, which is about
q/2^124 + 2^-101 after q hash queries, where each try at the proof of work counts as a hash query.
No running time is claimed for the decoding function, and nothing but the weights is extracted. The
prover in the bound on a whole run is a deterministic strategy. "Under the files' policy" is worth
what the policy forbids: some policies in scope leave every counted token free; at exact match it
says that each output token is the model's. It says nothing of whether an honest prover is accepted:
that is completeness.

The error of the proximity rounds is derived, not assumed: it rests on a theorem of correlated
agreement for pairs of words up to (just inside) the Johnson radius (`Cb.BCHKS46At`,
`Cb/Gen/CodeListRSAt.lean`; proved in `Cb/Bridge/CodeListRSProved.lean` from two theorems in files
adapted from the ArkLib library), together with a proved bound on the number of close code words;
the batching and out-of-domain rounds use the list bound alone. Three files hold facts on the radii,
as numbers. At the committed table, for all public files in scope, the decoding radius derived from
the files meets the library's Johnson condition (`Cb.InJohnson`) and is beyond half of the library's
distance of the table's code (`E2E/SampleAndJohnsonInScope.lean`). At each of the 43 stages of the
nine proximity tests and at each of the 207 sampled messages of the library's written full-size
lists the radius meets that condition and is at least half of the distance there; where rows lie in
two codes, that is the smaller of the two distances (`E2E/StagesAtOrBeyondHalfTheDistance.lean`,
`Johnson/G/PackLitArms.lean`). "Distance" is the library's number for a Reed–Solomon code: length
less dimension plus 1, times the number of repeats; that it is the code's minimum distance and no
more is not proved there. These files do not tie the two lists to `protocolAtFiles files`, and they
do not say which theorem bounds a round's error. That `Cb.BCHKS46At` follows from Theorem 4.6 of
ePrint 2025/2055 is a reading, not a theorem (L15).

*Beside the soundness theorem on `verify`.* The soundness theorem on `verify`
(`sound_of_verify_at`), and `finalSound` above it (L93), do not rest on this statement: by import
lines the file of its proofs lies beneath neither. The proof of the soundness theorem on `verify`
takes the round-by-round soundness of the key, copy and proof protocols one by one (`keySound`,
`entrySound`, `proofSound`, three of the compiler's named hypotheses; where each is proved at
`theDescription`: L57) and hands them to the compiler's theorem on `innerCompiledVerifier`, in the
form `verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor`
(`Johnson/Top/InnerCompiledVerifierByPublicReading.lean`); the soundness theorem on `verify` has no
hypothesis beyond those in its statement, so nothing more is assumed by that road. A second theorem
(`sound_of_verify_at_through_the_IOP`, `E2E/SoundAsIOPAtFilesProofs.lean`) has the statement of the
soundness theorem on `verify` to the letter, with no further hypothesis, and is proved through this
statement, not through that theorem: it draws the three from this statement and hands them to the
same theorem of the compiler. It adds little assurance: the three parts of this statement are
themselves proved from one lemma of the first proof and from sisters of the other two, which rest on
the same theorems: it is the same proof by another road, no second derivation. The law on the
out-of-domain point as it is made from hash answers is proved, by one lemma that both proofs use
(`entryFull_seedLawK`, `OnBytes/Flat/RecordSeed.lean`); soundness as an IOP gives nothing of it. The
second theorem does not go through `compile` (`Johnson/Face/Compiler.lean`).

Basis: proved (the theorems named) · by reading (the statements and definitions named; the text of
the two proofs; what no theorem says) · computed (what lies beneath what: by import lines).

### Completeness, as an interactive oracle proof, on served requests

**L90.** Proved in Lean: `AtFullSide.Honest.complete_in_scope`
(`AtFullSide/Honest/CompleteAtTheFiles.lean`). It follows from `complete_at_the_files` of the same
file, whose two further hypotheses two lemmas supply (`baseMaker_returns`, `headAtReturn_baseMaker`,
`AtFullSide/K1/HeadAtBaseMaker.lean`). It concludes, first,
`AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles files (thePartsAt files)`
(`E2E/CompleteAsIOPAtNamed.lean`), which is `CompleteOnServedRequests`
(`E2E/CompleteAsIOPAtFiles.lean`): the library's definition `CompleteIOP`
(`Johnson/Face/CompleteAsIOP.lean`) at the protocol.

*What it says.* For the Lean honest provers, the online one made to refuse what is not served, and
the interactive protocol's own verifiers, on served requests, each of the three runs (offline, link,
online) succeeds but for a small error, and the three errors add up to at most 2^-41. This holds at
each encoding randomness, each out-of-domain seed and each copy's number, not on average: the error
is over the provers' coins and the challenges that pass the proof-of-work tests, and nothing else.
The theorem also concludes a stronger form, at every single coin of the provers
(`OnBytes.Prover.CompleteAtEveryCoin`, `Johnson/Prover/All/CompleteAsIOPForTheCompiler.lean`), which
one of the compiler's two theorems on completeness takes (`compiled_complete_atEveryCoin_holds`,
`VerifiableInference/Final/CompilerComplete.lean`); the proof of L93 takes the first form. In the
stronger form, among the challenges that pass the proof-of-work tests, the link's run never fails.
Of the offline run another theorem says the like, at the index of a served request: among the
challenges that pass the proof-of-work tests the offline run never fails
(`AtPublicFiles.OneProtocol.offline_at_one_protocol`, its field `offlineComplete`;
`E2E/OneProtocolAtTheEnds.lean`). A run counts as failed if the prover stops, or if the verifier
rejects it under some choice of nonces. A request is served at given weights if it is well formed,
the integer model at these weights has a result on it, the claimed output is that result, and the
verifier's builder makes an instance of it. So "served" depends on the weights.

*Limits.* It is a statement before hashing, for one request per proof, and it speaks of served
requests alone: of the offline and the link run too it speaks only at weights at which some request
is served. Where the model has no result on a request, no claimed output is served, and the theorem
says nothing there (at weights that pass the first worst-case check, or the least-bound check with
numbers that hold, no well-formed request is of that kind: L93). It speaks of the challenges that
pass the proof-of-work tests: of all challenges nearly every one is rejected, and the searches for a
nonce are counted in the compiled line, not here. That some request is served is said by a lemma
beside it, at made-up weights (`someRequestIsServed_holds`,
`VerifiableInference/Final/ZeroKnowledgeAtTheProtocolLaws.lean`), not by the theorem.

The provers as written have default values at many places (L96 and L97 tell of some). The theorem
holds with these in place; it does not say that none of them is ever sent. Beneath it lie some
hundreds of closed equations that Lean's kernel evaluates; no independent checker has replayed them.
One test on values at member 354 of the proof file's first chain (`testV`,
`Johnson/AtFull/Shape/TestReturnsFrame.lean`; the words:
[ShapeLines/README.md](ShapeLines/README.md)) asks more than the one honest full-size run that has
been evaluated gives. At member 354 the theorem's proof does not ask that test to accept: acceptance
there comes from `ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_whole`
(`Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAcceptedWhole.lean`), which
`Johnson.AtFull.Shape.first_chain_whole` (`Johnson/AtFull/Shape/Scope/FirstChainWhole.lean`) applies
at that member (by reading the proof; no theorem says so).

`CompleteIOP` is this library's own definition of completeness of an IOP with proof of work. The
name `CompleteAtFiles` is declared twice: `AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles` is this
statement on the IOP, and `VerifiableInference.Compilation.CompleteAtFiles` is the compiled
statement that the field `complete` asks at given files.

Basis: proved (the theorems named) · by reading (the statements and definitions named; what no
theorem says).

### Honest-verifier zero knowledge, as an interactive oracle proof, before hashing

**L91.** Proved in Lean: `VerifiableInference.Compilation.zkOnServedRequests_inScope`
(`AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean`). It concludes `ZeroKnowledgeOnServedRequests files
… 0 0 2^-174` (`VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean`; the definition:
`HonestVerifierZeroKnowledge`, `VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean`).

*What it says.* It is about the same Lean honest provers, made to refuse what is not served, in the
same interactive protocol. The simulators are fixed first, and they never get the weights, a table's
randomness or a prover's coins. Run by run: what an honest verifier sees of each run (offline, link,
online; online at served requests) has exactly the distribution that the simulator makes from the
public files, the verifier's messages, the out-of-domain samples, the columns of the tables that the
verifier reads and, for a request, the request with its claimed output and the copy's number. The
one exception is where the prover stops for a private reason (a public stop reads the verifier's
messages alone; a private one may read the weights, a table's randomness, the seed and the request):
the chance of that is 0 offline, 0 for the link and at most 2^-174 for a served request, each over
the verifier's messages that pass the proof-of-work tests. Within the budget that the statement
calls the whole life of one commitment (one offline run, one link for each copy, up to 710,324
copies, up to 688,127 requests on each copy (each one run of the online IOP; after compiling, one
reply) and none on the first table, asked in any order and adaptively): what an observer that is
unbounded in computing sees of the honest provers on the real weights is within 2^-135
(`VerifiableInference.Compilation.life_number_at_most`,
`AtFullSide/CompletenessAndZeroKnowledge/LifeNumberAt135.lean`: 488,793,123,148 × 2^-174 is below
2^-135) of what it sees of the simulators working from tables of any other fixed weights. The
statement also says that some request is served, and that two different indices serve one and the
same request; both are shown at made-up weights.

*Limits.* It is a statement before hashing and for an honest verifier (its messages are uniform
among those that pass the proof-of-work tests, and it reads only where its rule says). It is
statistical, not perfect. 2^-174 bounds one online run; it is not the error of a commitment's life,
which is the 2^-135. This 2^-135 is not L64's, which is another statement's figure (fixed-message
provers, one copy, one request, after hashing). None of these figures is a security level (L84).
Nothing in the statement ties a committer or a prover to that budget, and nothing counts: beyond
these numbers it says nothing.

One bit for each request is not hidden: whether the request is served, which depends on the weights.
The simulator is given that bit (the observer must mark each request truly as served or not), and
where a request is not served the prover shows nothing. So what the statement hides, within the
numbers and the error above, is the weights beyond these bits. A bit says whether the claimed output
is the model's result on that request, so over many requests the bits tell what the model answers.

The statement says nothing of what the public files themselves tell of the weights (the simulators
may depend on these files), or of timing. In the run-by-run form, at all three runs, the simulator
is handed two things that are made from the weights, the out-of-domain samples and the columns read:
so that form alone does not speak of the weights. The clause on the whole life does: there the
samples and the columns are those of tables of the other weights. It holds within a budget of
44,040,191 columns read of each table, and the numbers above are the largest that fit it. It says
that simulators exist, names none, and claims nothing on their running time. It says nothing of
distributions conditioned on no stop. It is one request to a run: no batches. It is for fresh
uniform coins, not for coins derived from a short key, and for one commitment to the weights; the
programs derive theirs from a key (L14).

A statement of this form can be met trivially: a prover that sent fixed messages and refused what is
not served, or that always stopped for a public reason, would meet it. What shuts that out is
completeness of the same provers, so the two are to be read together, as about one triple of provers
and one protocol (L92).

`HonestVerifierZeroKnowledge` is this library's own definition. This entry tells what the theorem
says; what the release hides is told at [Weight hiding](../guide/weight-hiding.md).

*A label in the comments.* Comments in files beneath this theorem bear the label "NOT IN FRONT OF A
LAW OVER COINS" (the rule: the head of `Johnson/Bind/ForProver/FiveFieldsAt.lean`): it marks a lemma
with a premise that ties a run to its coins. The theorem has no premise beyond the three on the
public files, so Lean has checked that premise wherever its proof uses such a lemma.

Basis: proved (the theorems named) · by reading (the statements and definitions named; what no
theorem says).

### The three, of one protocol and one triple of provers

**L92.** Proved in Lean: `VerifiableInference.Compilation.threeAtFiles_in_use`
(`AtFullSide/Face/TheThreeAtTheFiles.lean`). It is a value of one Lean structure,
`ThreeAtOneProtocol`, at the public files (`ThreeAtFiles`, `E2E/ThreeAtOneProtocol.lean`), at all
public files in use (the three tests and exact match; the proof uses the three tests alone). In that
structure the protocol is a parameter that is bound once and read by the fields on soundness, on
completeness and on honest-verifier zero knowledge, each as an IOP. The triple of honest provers,
the proof-of-work bits and the served requests are bound once and read by the two fields on
completeness and on zero knowledge. So no value of the structure can speak of two protocols, or, in
these two fields, of two triples of provers. These three fields are filled from the theorems of L89
and L91 and, for completeness, from `complete_at_the_files` (L90's file), through
`threeAtFiles_of_ends` (`AtFullSide/CompletenessAndZeroKnowledge/ThreeAtFilesOfEnds.lean`).

*Limits.* Its proof only applies these theorems, and it adds nothing to them: each one's limits go
with it. It is before hashing, on served requests, for an honest verifier, and about the Lean
provers as written. The numbers stand over different distributions and are not to be compared:
2^-128 is a share of all of one round's challenges, the proof-of-work bits among them; 2^-41 is over
the provers' coins and the challenges that pass the proof-of-work tests; 0, 0 and 2^-174 bound the
provers' private stops, run by run, over the verifier's messages that pass the proof-of-work tests.

Soundness reads neither the provers nor the structure's proof-of-work bits: its bound is over all of
a round's challenges, those bits among them. It stands at a wider relation, in which the served
requests lie (a fourth field of the structure says so). The field on soundness is its form in parts,
which online speaks of a batch where the other two speak of one request; the whole run and its
67,391 × 2^-96 are L89's and no field here. The field on zero knowledge is the first part of that
statement, `HonestVerifierZeroKnowledge` (run by run, and the whole view at every budget that fits
the tables). The clause on the whole life at 710,324 copies and 688,127 requests on each, with its
2^-135, and the two clauses on served requests are L91's, not this structure's.

Nothing in the structure ties the encoder, which completeness and zero knowledge read, to the
decoder, which soundness reads. At the public files a theorem beside it does: at a served request
the extractor of soundness returns the honest index from the honest table and its sample
(`extract_at_served`, `E2E/ExtractorAtHonestTables.lean`). That the offline and the link prover
inside the triple are the honest provers' own is said by two statements of the structure's file
(`offline_prover_inside`, `link_prover_inside`); the online prover inside it has the honest online
prover's coins, tables, strategy and public stops by definition (`HonestProvers.refuseUnserved`,
`Johnson/Face/Protocol.lean`), and only its private stops are widened, at requests that are not
served.

Basis: proved (the theorems named) · by reading (the statements and definitions named; what no
theorem says).

### The compiled prover and verifier: the six theorems

**L93.** Proved in Lean: the six theorems of `AtFullSide/Face/TheSixLines.lean`:
`VerifiableInference.sound`, `VerifiableInference.soundAndBinding`,
`VerifiableInference.completeOnCanServe`, `VerifiableInference.zeroKnowledgeOnCanServe`,
`VerifiableInference.refusedHandsOutNoProof` and `VerifiableInference.repliesFit`. These pages call
them the six lines. Each is stated of `compile (flashProve setup)`, and `setup` is its one argument;
a `PublicSetup` is three public files in use with what they read as.

`flashProve setup` is `flashProveAtFiles` at the setup's files, at the settings that they read as,
and at `honestProversAndSettings` there. The system is `finalSystem honestProversAndSettings files
settings`, that is `compile (flashProveAtFiles files settings …)`: the protocol above, compiled with
a hash function, at the honest part `honestProversAndSettings` = `honestProversAndSettingsOf
thePartsAt` (`AtFullSide/Face/HonestProversAndSettingsValue.lean`), one closed Lean term. An honest
part is the provers with what compiling adds to them (`HonestProversAndSettingsAtFiles`: the
compiled settings, the range of the committer's coins, the sessions that one copy bears). The
provers inside it are the triple of L92, made to refuse what is not served, and the protocol over
which they are typed is `protocolAtFiles files` (`compiled_provers_are_the_triple`,
`compiled_protocol_is_the_bound`,
`AtFullSide/CompletenessAndZeroKnowledge/ThreeAtFilesOfEnds.lean`). Its committer and prover are
`compile`'s own. Its verifier is `verify`, whatever the honest part
(`compile_flashProve_verify_eq`).

The hash function is drawn at random: these are statements in the random-oracle model. These six
lines are the library's goals on the compiled prover and verifier; elsewhere on this page, but for
L76, "goal" means a proposition that `Ladder.lean`, `Ladder/Bits.lean` or `Ladder/Package.lean`
types for any IOP (`VerifierAndGoals.Description`). What the six lines say:

- `sound` (`Sound`): an output that is not that of the weights that an extractor reads off the
  commitment and the committer's queries is accepted with probability at most about q/2^124 +
  2^-101, where q counts the committer's and the prover's hash queries. It reads no honest part (at
  such files it is `finalSound`), and it is `Sound` of `verify`'s own system
  (`compile_flashProve_sound_iff`).
- `soundAndBinding` (`SoundAndBinding`): soundness with binding, of the same committer, at an error
  of about q/2^124 + 2^-100 (q: the maker's and the opener's queries; `finalSoundAndBinding_value`,
  `AtFullSide/Face/FinalBindingAtTheValue.lean`; what the line says and its fourteen limits: the
  head of `Johnson/Face/FinalBindingStatement.lean`; those on what an opening is and on what lies
  under the commitment: this entry's last paragraph).
- `completeOnCanServe` (`CompleteOn` at `CanServe`: L27): at all weights and every request that can
  be served and whose output tokens are the model's, the Lean verifier rejects the Lean prover's
  proof with probability at most 2^-40, over the hash function and the committer's and the prover's
  coins. Of a request outside `CanServe`, among them those at which the model has no result, and of
  an output that is not the model's, `completeOnCanServe` says nothing: together these are the
  requests that the prover refuses (`served_iff_canServe`,
  `VerifiableInference/AtEveryRequestGuards.lean`), and completeness is not promised for them.
- `zeroKnowledgeOnCanServe` (`ZeroKnowledgeOn` at `CanServe`: L18, L83): for one commitment with one
  copy of the table, up to 688,127 replies and 2^64 hash queries, against any verifier that gets
  proofs only for requests that can be served and whose output tokens are the model's, one
  simulator, fixed before the weights, which may depend on the public files and gets each request
  and the largest number of replies, and nothing of the weights (the final system has no public
  parameters: L83, 2), makes the commitment, the proofs and the hash answers, and the view is within
  a bound of the real one, in total variation: the theorem says that such a bound exists, and that
  within these counts it stays at or below 2^-154 (`finalZeroKnowledgeError`). Whether a request can
  be served depends on the weights and is not hidden (L27). `zeroKnowledgeOnCanServe` by itself says
  nothing of a refused request.
- `refusedHandsOutNoProof` (`HandsOutNoProof`): at a refused request every reply that the prover can
  return is the empty proof.
- `repliesFit`: 688,127 (`finalReplyCount`) is at most `onlineRunsPerCopy setup`, the number of runs
  of the online IOP that the honest settings give one copy; the columns that the proofs open fit
  each table's budget; and one run of the sampler, one of the committer and one of the prover
  together stay within 2^48 hash queries. It is a line on numbers: that number of runs is written,
  688,127 too, and `compile` does not read it; nothing in the prover enforces them (what such a
  number counts, and the programs' own 688,127, which counts batches: L84).

`VerifiableInference.sound` is `finalSound`, `VerifiableInference.soundAndBinding` is
`finalSoundAndBinding_value`, `VerifiableInference.refusedHandsOutNoProof` is
`finalRefusedHandsOutNoProof_value` and `VerifiableInference.repliesFit` is `repliesFit_value`, each
at a `PublicSetup`'s files. The other two, `completeOnCanServe` and `zeroKnowledgeOnCanServe`, are
the two halves of one theorem, `served_at_T1` (L18), at a `PublicSetup`, with its one premise met
(`termLeft_value`). Among the file's further theorems at a `PublicSetup` are
`VerifiableInference.zeroKnowledgeWithLabel` (zero knowledge at well-formed requests, with the
request's label set beside each proof) and `VerifiableInference.rejectsEmptyProof` (the compiled
verifier rejects the empty proof).

**The structure `FinalStatementOneBit`, beside the six lines.** Of the structure
`FinalStatementOneBit` (`Johnson/Face/FinalStatementOneBit.lean`) two fields, `binding` and
`repliesFit`, are two of the six lines; two, `sound` and `handsOutNoProof`, say what two of the
lines say at more public files (`FilesTaken`: that they pass the verifier's first test is not
asked); `complete` is equivalent to `completeOnCanServe` (`finalComplete_iff_completeOn`,
`Johnson/Face/Checks.lean`); and `zeroKnowledge` follows from two of the lines
(`zeroKnowledgeAtEveryRequest_of_lines`) and is not proved to give `zeroKnowledgeOnCanServe` back.

Proved in Lean: `VerifiableInference.Compilation.theFinalStatementOneBitHolds`
(`AtFullSide/Face/TheFinalStatementOneBitHolds.lean`). Its type is `FinalStatementOneBit
honestProversAndSettings finalZeroKnowledgeError`, with no hypothesis outside the fields: each field
binds its own public files (four of the six fields' definitions: `Johnson/Face/FinalStatement.lean`;
`FinalZeroKnowledgeOneBit`: `Johnson/Face/Checks.lean`; `FinalRefusedHandsOutNoProof`:
`Johnson/Face/FinalStatementOneBit.lean`). `FinalStatementOneBit` gives the statement with the label
shown, at every honest part and error (`finalStatement_of_oneBit`,
`AtFullSide/Face/TheFinalStatementOneBitHolds.lean`): so `FinalStatement honestProversAndSettings
finalZeroKnowledgeError` (`Johnson/Face/FinalStatement.lean`) holds too
(`theFinalStatementBothHold`, `AtFullSide/Face/TheFinalStatementOneBitHolds.lean`; also
`theFinalStatementHolds`, `AtFullSide/Face/TheFinalStatementHolds.lean`). That statement has the
same six fields, but that the two on zero knowledge and on the reply are in the form for a service
that says "failed" (a service: whoever runs the prover and sets the label beside its proofs; the two
fields: further below).

Two of the four fields that are none of the six lines, in full:

- `complete` (`FinalComplete`): at all weights and every well-formed request whose claimed output is
  the model's own result, the Lean verifier rejects the Lean prover's proof with probability at most
  2^-40, over the hash function and the committer's and the prover's coins.
- `zeroKnowledge` (`FinalZeroKnowledgeOneBit`): At every request, well-formed or not, for one
  commitment with one copy of the table, up to 688,127 replies and 2^64 hash queries, against any
  verifier, one simulator, fixed before the weights, which may depend on the public files and gets
  each request, the largest number of replies and, of the weights, only one bit for each request
  (served or refused), makes the commitment, the replies (each a proof or the empty proof
  (`noProofForm`: a form all of whose parts are empty)) and the hash answers, and the view is within
  2^-154 (`finalZeroKnowledgeError`) of the real one, in total variation. It holds at every error
  from 2^-157 + 688,127 · 2^-174 up (`finalZeroKnowledgeOneBit_at`), and so at 2^-154.

`TheSixLines.lean` has both as corollaries of the lines:
`VerifiableInference.completeAtWellFormedRequests` (equivalent to `completeOnCanServe`, by
`finalComplete_iff_completeOn`) and `VerifiableInference.zeroKnowledgeAtEveryRequest` (from
`zeroKnowledgeOnCanServe` and `refusedHandsOutNoProof`, within the same bar, the simulator told one
bit for each request, served or refused; that it gives `zeroKnowledgeOnCanServe` back is not
proved).

For a service that chooses to say "failed" there is, as a corollary, zero knowledge of the same
system with the three-valued label shown beside each proof. The field `zeroKnowledge` gives the
field with the label shown, at the same error and at every honest part
(`finalZeroKnowledge_of_oneBit`, `Johnson/Face/FinalStatementOneBit.lean`), and the field
`handsOutNoProof` gives the field on the reply with its label (`finalHandsOutNoProof_of_refused`,
`AtFullSide/Face/TheFinalStatementOneBitHolds.lean`). There a reply is the label beside what the
compiled prover returns (`reply`, `VerifiableInference/Labelled.lean`). The two fields of
`FinalStatement` in that form:

- `zeroKnowledge` (`FinalZeroKnowledge`): at every well-formed request, for one commitment with one
  copy of the table, up to 688,127 replies and 2^64 hash queries, against any verifier, one
  simulator, fixed before the weights, that gets each request and, of the weights, only one label
  for it (served, failed or other tokens) makes the commitment, the replies and the hash answers,
  and the view is within the error of the real one, in total variation: at every error from 2^-157 +
  688,127 · 2^-174 up (`theFinalStatementHolds_at`), and so at 2^-154 (`finalZeroKnowledgeError`),
  at which `theFinalStatementHolds` is stated.
- `handsOutNoProof` (`FinalHandsOutNoProof`): at every request the label in the reply is the one
  that the definition `requestLabel` gives, and outside "served" the form beside it holds no proof.

**The completeness theorem at weights that pass a worst-case check, beside the six lines.** Proved
in Lean: `VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes`
(`AtFullSide/E2E/CompleteWhereSomeWorstCaseCheckPasses.lean`) and
`modelNeverFails_of_passesSomeWorstCaseCheck`
(`VerifiableInference/Bounds/SomeWorstCaseCheck.lean`); the premise: `PassesSomeWorstCaseCheck` (the
same file): the first worst-case check, or the least-bound check with numbers that hold. At public
files in use and at weights that pass the first worst-case check, or the least-bound check with
numbers that hold, the model has a result on every well-formed request; and for every prompt that is
not empty and whose tokens are in the vocabulary, and every output length of at least 1 that fits,
there is exactly one output of that length that is the model's own, and the honest proof for that
prompt and that output is accepted except with probability at most the completeness error. It covers
no request that the completeness line does not already cover (that line holds at all weights, for
every request that can be served and whose output tokens are the model's, which at valid settings
are the well-formed requests whose claimed output is the model's result:
`wellFormed_and_result_iff`, `VerifiableInference/WellFormedRequests.lean`): it does not make
completeness hold where the model has no result; it names weights at which that case does not arise.
Of a request that claims other tokens neither says anything; to such a request the honest prover's
reply holds no proof, at any weights (`refusedHandsOutNoProof`).

The first arm of the premise `PassesSomeWorstCaseCheck` is `PassesWorstCaseCheck`
(`VerifiableInference/Bounds/NeverFails.lean`), and under that arm alone the same is proved apart
(`VerifiableInference.Compilation.theHonestPart_complete_where_the_worst_case_check_passes`,
`AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean`). The second half of this is also proved
under a premise that this one implies, that no range condition of the integer model ever fails at
the weights (`AtFullSide/E2E/CompleteAtEveryPrompt.lean`). No theorem says that the second arm holds
of any weights of which the first does not: the premise contains the first check (whatever passes it
meets the premise), and no theorem says that it is wider.

With the completeness theorem at weights that pass a worst-case check go:

- the premise's first arm is this library's own decidable test on settings, tables and weights; its
  second is a statement that numbers exist that hold together ("numbers that hold": each stretch
  bound that the least-bound check reads is at least 0, and no vector of whole numbers gets longer
  by more than that factor when it is multiplied with its matrix; which matrices, and what they are
  made from: `LeastBoundNumbers.Hold`, `IntegerModel/Bounds/LeastBoundCheck.lean`), and that with
  them a second test, the least-bound check, passes: a statement, not a test; as it is written the
  first check can be evaluated at small sizes; at the full sizes it cannot in practice (the head of
  `IntegerModel/Bounds/Check.lean`); the least-bound check, as its definitions stand, is costly to
  evaluate (the head of `IntegerModel/Bounds/LeastBoundCheck.lean`)
- to pass the least-bound check is not enough: the test uses the numbers and does not test them, nor
  that they are not negative (the docstring of `PassesLeastBoundWorstCaseCheck`,
  `VerifiableInference/Bounds/LeastBoundNeverFails.lean`); at a small made-up model, with tables of
  its own, it passes with numbers that do not hold, at weights at which the model has no value on
  its one prompt (`control_leastBound_passes_with_zeros`, `control_leastBound_zeros_do_not_hold`,
  `IntegerModel/Bounds/LeastBoundCheckControl.lean`; `control_model_eq_none`,
  `IntegerModel/Bounds/LengthCheckControl.lean`)
- neither check is `cp_commit`'s worst-case check (L7): no theorem relates either to a check that
  any program makes
- both checks are sufficient, not necessary: weights that do not pass may still never fail (the
  heads of `IntegerModel/Bounds/Check.lean` and `IntegerModel/Bounds/LeastBoundCheck.lean`); no
  theorem shows such weights
- no theorem says whether a real model's weights meet the premise
- nothing in a commitment, in a proof or in what a verifier does shows that the committed weights
  meet the premise
- the weights that are shown by name to pass a check that gives the premise are made up
- the files that carry the theorem are among the files that a build of this repository compiles, and
  the audit step, which looks the theorem up by name, has been run over such a build, within a whole
  run of the full check ([CHECK-RESULTS.md](CHECK-RESULTS.md))
- the prover is the Lean definition; nothing on the programs
- one commitment and one request; the exact-match policy; the random-oracle model.

Completeness, zero knowledge and the replies' numbers come from `complete_at_the_files` (L90's file)
and the theorem of L91, through the compiler's theorems
(`VerifiableInference.Compilation.finalAtT1_filled`, `finalAtT1_filled_withRoom`,
`AtFullSide/E2E/TheCompiledStepFilled.lean`; the field `zeroKnowledge`:
`VerifiableInference.Compilation.finalZeroKnowledgeOneBit_value`,
`AtFullSide/CompletenessAndZeroKnowledge/OneBitAtHonestProversAndSettings.lean`). That is the
structure's road. The lines `completeOnCanServe` and `zeroKnowledgeOnCanServe` rest on the same two
theorems: the one premise of `served_at_T1` follows from them and one inequality on their numbers
(`termLeft_value`, by `termLeft_at`; the general form: `termLeft_of_ends`, L18).

The fields `sound` and `handsOutNoProof` ask less of the public files than the six lines and the
other four fields: in scope, read and exact match, without the verifier's first test.

*Limits.* These lines and their corollaries (completeness; zero knowledge on `CanServe`, at every
request and with the label shown; the replies' numbers) are worth what the two theorems beneath them
are worth: everything that goes with those goes with these. One request per proof, one commitment,
one copy of the table, the exact-match policy, and the Lean prover as a definition, default values
included. The format's second hash function, a fixed public function inside the description, is no
random oracle. At BLAKE2b no theorem shows that `verify` accepts anything: there it is tested by
runs.

Where the model has no result, or another result than the claimed output, the line on completeness
says nothing: at a real failure the prover returns the empty proof, the same as for a claimed output
that is not the model's. That a request is refused is unchecked, as the label is: an empty proof
proves nothing, and a prover can return it at a request that it could serve. The compiled verifier
rejects it, under every hash function and at all public files (`rejectsNoProof_value`). A service
that chooses to say "failed" says it unproved. "Failed" is the prover's word: it isn't proved, and a
prover can say it falsely. The same holds of "other tokens": no proof goes with these two labels,
and the verifier checks nothing there.

The requests of which the line on completeness speaks are those that meet `CanServe` and whose
output is the model's (by its statement; the field `complete` speaks of the same requests:
`finalComplete_iff_completeOn`, `Johnson/Face/Checks.lean`), so the limits of that condition go with
it (L27). The completeness theorem at weights that pass a worst-case check does not change this: it
does not make completeness hold where the model has no result; it names weights at which that case
does not arise. All that goes with the line `completeOnCanServe` goes with that theorem too.

Refused requests are covered by the corollary at every request (`zeroKnowledgeAtEveryRequest`; the
field `zeroKnowledge`), up to one bit: there the simulator is told one bit for each request, served
or refused. How much the statement says depends on this function alone (`requestOutcome`): its value
is all that the simulator is told of the weights in the experiment (it may depend on the public
files). The bit depends on the weights, and it is declared, not hidden: for every request of its
choice a verifier learns whether the claimed output is the model's result. (It reads the bit off the
reply: a refused request gets an empty proof; so, with small probability, does a served one, where a
search for a nonce runs out.) So over many requests, chosen adaptively, it learns what the model
outputs on inputs of its choice: whoever tries each candidate token for a prompt learns the model's
next one from this bit alone, unless all are refused. Against three labels it hides one thing:
whether a refusal means that the model has no result or that its result is other tokens. It hides
that only from a verifier that asks few requests. A request's window of 1,024 tokens can itself be
sent as a prompt, with one more token as the claimed output, which the run does not read: a verifier
that tries every candidate for that token and is refused each time learns that the model has no
result on that window, and one that is served once learns that it has one (argued from the
definitions; no theorem states it). Each such search costs up to 202,048 (one for each token of the
vocabulary) of the 688,127 replies. A true output is refused if the model has no value further on in
the window. No statement bounds what many bits reveal together.

The reply is what the compiled prover gives, a proof or the empty proof, and nothing stands beside
it. In the corollary with the label, a label of three values is shown beside it: a true output can
be told "failed" on account of the padding, and nothing in `compile` emits the label: that reply is
a definition beside it, the label next to what the prover gives (`reply`,
`VerifiableInference/Labelled.lean`). All the strength of this statement lies in which function
`told` is: at the identity on the weights, a prover that sends the weights meets it. (Said of the
forms in which the corollary is written, `ZeroKnowledgeShownWhere` and
`ZeroKnowledgeShownBelowWhere`, the same file; an argument, no theorem: that file's head, 7.) With
the label a verifier learns, for every request of its choice, which of the three holds, and so, over
many requests, where the model has no result. No statement bounds what many labels reveal together.

The number of copies stands in no line's text: it lies inside the honest part's settings, and at
`honestProversAndSettings` it is one (`theSettings`,
`Johnson/CompletenessAndZeroKnowledge/TheSettings.lean`). The lines say nothing of an honest
committer that makes more. What the provers' committed rows hold at a shape that one test refuses,
and how it is known that the shape of these lines passes it: L98.

A statement of the form of the line on zero knowledge is met by a prover that hands out nothing, so
it counts only beside completeness, which is proved of the same system (`completeOnCanServe`). What
follows, to the end of this paragraph, is said of the line and holds of its corollary at every
request too. The simulator's running time is not modelled. The line says nothing of what the public
files themselves tell of the weights, of what is published beside the commitment, or of timing; the
simulator may depend on the public files. Nor does the line say anything of a party that learns the
committer's randomness or the weights by other means than the replies. Beyond 688,127 replies or
2^64 hash queries it says nothing. The simulator also gets the largest number of replies, and it
answers the hash queries in the hash function's place. The verifier has no hash query before the
commitment, and the weights and the public files are fixed before the hash function is drawn.

A nonce search that runs out is inside what is simulated: it shows as the empty proof at a served
request, which looks like the reply to a refused request; in the corollary with the label, as the
empty proof beside the label "served". All of L83's seven limits go with this line, which is
`ZeroKnowledgeOn` itself; with its corollary at every request go 1, 4, 5, 6 and 7, and 2 but for its
last sentence.

The compiled prover keeps no state: it draws its copy at random (at this honest part there is one),
nothing counts the replies, and all its coins are fresh and uniform; nothing is said for coins
derived from a short key or for batches. 2^-41 and 2^-40 are two bounds over two distributions: the
first before hashing, among the challenges that pass the proof-of-work tests; the second after
hashing, over the hash function and the coins, the searches for a nonce that run out included. No
figure here is 128 bits, and none is a security level (L84).

The committer is a Lean term that no theorem ties to a program; the commitment has 256 bits. The
commitment is made from the first table's Merkle root and its out-of-domain sample, with a part of
what is read off the public files; the offline proof, the copies and their link proofs are not under
it. So the key file is not under it. To open is to name weights and one number for the committer's
randomness. That names fewer openings than any choice of coins would: nothing is said of an opening
in which the salts of the first table's leaves have another public start or another length. The
extractor is a function, not shown computable; soundness and binding read no prover. Correctness of
extraction for this committer is proved beside it (`finalExtracts_value`, at 2^48 hash queries,
about 2^-155). Nothing is said of two openings to the same weights, of several commitments, or of
who made a commitment. The same weights can have many commitments: the honest committer computes the
commitment from the weights and its own randomness. No line bounds the length of a proof, or the
hash queries that `verify` itself makes.

Basis: proved (the theorems named) · by reading (the statements and definitions named; what no
theorem says; what a verifier learns from the bits: an argument from the definitions, which no
theorem states).

## 11. What the lemmas on the honest provers leave open

These entries tell what statements say and what no statement says. Paths in this part are from
`lean/`, but for those that begin with `docs/`, which are from the repository's top.

### Lemmas on the honest prover hold "wherever the invariant holds"

**L94.** Most lemmas on the honest prover are implications from an invariant of its run at a given
point of the protocol; no statement says, on its own, that an honest run reaches a named point with
the invariant.

**What the library has.** The online protocol is written as three lists of sub-protocols (`first`,
`shared`, and the third list, `second`). The argument for completeness goes by an invariant: for
each list a predicate on the verifier's state, the prover's state and the messages at hand, indexed
by the number j of sub-protocols played so far.

`atEveryTiedRunAtItsThreads` (`AtFullSide/Honest/TheOneObject.lean`) says, from a value of the
structure `TheOneObject`, that at every request in the relation `TiedRequest` (a served request
together with the committed table's randomness and its out-of-domain sample) and at all of the
prover's coins there is a value of the structure `ThreadsCJ`
(`Johnson/Desc/ProofFile/Honest/Law/ThreadStratCJ.lean`) whose three invariants are these
predicates. `theOneObjectValue` (`AtFullSide/Honest/TheOneObjectValue.lean`) is such a value, at
public files that pass the policy's test and at which the prover's maker returns. It is stated at
the prover as the maker returns it; `AtFullSide/Honest/TheCrossing.lean` has the form at the online
prover. The fields of `ThreadsCJ` say that the invariants hold at the start of the first two lists
(`a₁`, `a₂`); that each sub-protocol, where its own check accepts, carries them from j to j + 1
(`h₁`, `h₂`, `h₃`); that outside a listed set of exceptional challenges the check accepts (`y₁`,
`y₂`, `y₃`); and that from the ends of the first two lists the third list starts (`d₃`) with its
invariant (`b₃`).

`every_served_request_is_tied` says, at public files in scope, that every served request gives a
member of `TiedRequest`, at every such randomness; `a_tied_request_exists` and `a_tied_run_exists`
(the same file) say that the relation and the set of runs are not empty. The step by induction on j
is a lemma of the library in general form: `thread_in_first`, `thread_in_shared`, `thread_in_second`
(`Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean`) say, for any invariants with these fields,
that where a run has called the prover's move at a point, the invariant held in front of that
sub-protocol.

`complete_in_scope` (`AtFullSide/Honest/CompleteAtTheFiles.lean`) has three premises, all on the
public files; its conclusion is completeness of the interactive oracle proof at served requests,
with an error of at most `completenessTarget`. `someRequestIsServed_in_scope` and
`aDueListWithNoStop_in_scope` (`AtFullSide/Honest/CompleteInScopeNotForNothing.lean`) say that in
scope some request is served, at an index in range, and that at every served input some list of
challenges of the declared form meets no stop of the honest prover. The request is at made-up
weights and neither is computed.

**The limits.** Most lemmas under `Johnson/Desc/ProofFile/Honest/K12`, `K13`, `K14` and
`AtFullSide/K12`, `K13`, `K14` are stated in the form "wherever the invariant holds at point j, …".
Where it does not hold, such a lemma says nothing. No statement applies the three general lemmas to
the three invariants above, and none says that a run gets as far as a named point, for example in
front of sub-protocol number 355 of the first list or at point 2 of the third. A reader who takes
one of these lemmas by itself has to make that step: no single statement makes it.
`complete_in_scope` does not depend on it being stated.

Basis: by reading (the statements, definitions and opening comments named; that no statement says
more: a search of the files' text, which can miss what Lean fills in by itself).

### No state is shown at which the test `shapeAt` accepts

**L95.** Lemmas lead from and to an acceptance of the executable test `shapeAt` on the verifier's
state in the third list of sub-protocols; no statement exhibits a state at which it accepts.

**What the library has.** `VerifiableInference.Desc.Last.shapeAt` (`Johnson/Desc/Last/ShapeAt.lean`;
below `shapeAt`; other definitions of the library bear the same short name) is an executable test on
the verifier's state at a point k of the third list (`second`) and on what the last states of the
first two lists hand over. Lemmas draw consequences from its acceptance and carry it from one point
to the next behind an accepting step (`Johnson/Desc/Last/ShapeGives.lean`; from point 2 to point 3
under four further premises: `step_two`). `shapeAt_zero_iff` (`Johnson/Desc/Last/ShapeDoor.lean`)
says that at point 0 it accepts if and only if the third list's start returns that state and two
tests on the last states of the first two lists accept (`firstDoorB`, `sharedDoorB`);
`first_door_at_end` (`AtFullSide/K14/FirstDoorAtEnd.lean`) and `AtFullSide/K14/SharedDoorAtEnd.lean`
have these two from the first two lists' invariants at their ends. `shape_of_form`
(`AtFullSide/Frames/LastChain.lean`) says that wherever the invariant's clause on the form of the
state holds at a point b, `shapeAt` accepts there. `Johnson/Desc/Last/ShapeAtTable.lean` shows that
the test can reject. `last_run_at_border358` (`ShapeLines/LastChain/LastRunAtBorder358.lean`)
evaluates in Lean's kernel a run of tests on shapes over the four sub-protocols of the third list,
from written values; it is on shapes alone and does not name `shapeAt`.

**The limits.** No statement exhibits a state at which `shapeAt` accepts, by evaluation or
otherwise. A lemma with the premise that it accepts, such as `samples_of_shape`
(`Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointSamplesAtShape.lean`, which has two premises
more), is shown to speak of something only through the invariant of L94. `complete_in_scope` has no
premise on `shapeAt`.

Basis: by reading (the statements, definitions and opening comments named; that no statement says
more: a search of the files' text, which can miss what Lean fills in by itself).

### `RowDataIsReady` is stated, not proved

**L96.** That the honest prover's data for a message pass their own readiness test at the states of
a served run, once enough challenges have been received, is written as a definition; no statement
proves it.

**What the library has.** For the message W, `w_ready_at_fold` (`AtFullSide/K12/LettersReadyW.lean`)
says, under the hypothesis `P5J.AtMgA` on the public files at the full size, which
`headAtReturn_baseMaker` (`AtFullSide/K1/HeadAtBaseMaker.lean`) shows to hold at public files in
scope that pass the policy's test, at what the base maker returns (that it returns there:
`baseMaker_returns`, the same file), that the test `readyAt` of W's data (`wDataAt`) accepts, from
four premises on a run: enough challenges have been received (the Lean field is `heard`); the last
2 + kCol of them have one element each; the verifier's run through the first 355 sub-protocols
(`foldBlocks`) has returned, with no failure mark and with the reply that was asked; and the front
of the list of challenges is that of these rounds. `hone_at_head`
(`AtFullSide/K12/LettersHone.lean`) gives the second premise from challenges of the declared form.
Where `readyAt` accepts, a default value in W's data is not taken (`wData_ready_own`,
`wDataAt_ready_heard`, `Johnson/Desc/ProofFile/Honest/K13/DefaultsIdle.lean`): x and eps, which are
0 where fewer challenges are found than are read (`wG`). The count of challenges (`wHeard`) falls
back on 0 where the public data have no such round; under `P5J.AtMgA` it is a written number
(`k13_wHeard_at_head`, `AtFullSide/K13/WFillAtHead.lean`), so that default is not taken at the full
size.

**The limits.** The proposition `RowDataIsReady` (`E2E/TheHonestProverNotTaken.lean`) says: at every
state in front of a move of the prover in the first or third list that a run at a served request
returns (`midAtW`), once enough challenges have been received for a message's data, `readyAt`
accepts. It is a definition, one of eleven propositions that this file writes as definitions; the
file itself proves none. Two of the eleven are theorems of the library: `Q0IsIdle` and
`LayersPlansAreThere` (`q0_is_idle`, `layers_plans_are_there`,
`AtFullSide/K13/NotTakenAtTheReturn.lean`; the second under the hypothesis `P5J.AtMgA` on the public
files, and of what the online maker returns). So is `K14RowIsWholeAtServedRuns`, a further
proposition of the same kind, stated in another file (`k14_row_at_return`,
`AtFullSide/K14/RowIsWholeAtServedRuns.lean`; L97). The opening comment of
`E2E/TheHonestProverNotTaken.lean` names three more as stated in other files (`K5RowWhole`,
`LookupRowIsWholeAtServedRuns`, `KeyPointsAreTheLookupsOwnAtServedRuns`): no file of this library
declares them. Each of the other eight of the eleven is proved nowhere in this library, and is used
by none of the theorems of L90 to L93. No statement of the library proves `RowDataIsReady`; none
applies `w_ready_at_fold` at a run; and none says that W's data there are the data that
`RowDataIsReady` names. Where `readyAt` rejects, the data still return a value, with no error, and
nothing says that it is W's entry.

**What it touches.** The statements on completeness and on zero knowledge speak of the prover as it
is defined, default values included. So this limit does not touch the truth of these statements. It
touches whether the prover that Lean defines is, at every served run, the prover that the paper
describes.

Basis: by reading (the statements, definitions and opening comments named; that no statement says
more: a search of the files' text, which can miss what Lean fills in by itself).

### Cases that two of the honest prover's senders handle with a default value and no error

**L97.** The definitions of the honest senders "send o_u" and "send o_omega" return a message at all
public parameters and at every run; for parameters that one executable test accepts, statements
exclude most of the cases in which a random field element would be misplaced; a few cases rest on a
reading, and none of this is a statement on distributions.

**What the library has.** The two senders of the batch's shared rounds are defined in
`Johnson/Desc/ProofFile/Honest/K14/Sendings.lean`, whose opening comment lists the cases below;
`Johnson/Desc/ProofFile/Honest/K14/DefaultsIdle.lean` lists them with what excludes each. A shape is
the public parameters of the messages. One executable test, `sendingsFit`
(`Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean`; for one sender `sendShapeFits`, for one
message `msgShapeFits`), is meant to accept only shapes at which the senders place a random field
element (a "coin") wherever one is due. `sendings_at_head`
(`Johnson/Desc/ProofFile/Honest/K14/SendingsAtHead.lean`) says that it accepts under the hypothesis
`P5J.AtMgA` on the public files at the full size, which `headAtReturn_baseMaker`
(`AtFullSide/K1/HeadAtBaseMaker.lean`) shows to hold at public files in scope that pass the policy's
test, at what the base maker returns (that it returns there: `baseMaker_returns`, the same file);
`publicIdle_at_head` (`Johnson/Desc/ProofFile/Honest/K14/DefaultsIdleAtHead.lean`) says that under
the same hypothesis all sentences of the structure `PublicIdle` hold for both senders. Where the
test accepts:

- where the coins stand (`Johnson/Desc/ProofFile/Honest/K14/SendingsReach.lean`): `spotCoins` lists
  the coins of which a position is made; `spot_reads` and `spot_sum` say that a position of the
  senders' rows (`laid`) reads these coins alone and is their sum. Of these lists: none has a coin
  twice (`spot_once`); two real positions of one message share no coin, but for one case, the same
  position's number in two rows of a fold's fresh table (`spot_share`, `spot_apart`); a mask row's
  coin reaches no tail and no second position of its row (`mask_no_tail`, `mask_one_place`); every
  coin below a message's count stands at a real position (`spot_all`); two messages of one sender
  share no coin (`messages_apart`, at every shape). `one_coin_turns` says it of the rows themselves:
  change one coin, at one state, and the real positions that change lie in one message and are one
  position, or the same position's number in two rows of a fresh table;
- the subtractions in `laid` that stop at 0: the inequalities hold at which none does
  (`SendIdle.plain`, `SendIdle.fresh`); each message's coins lie within the sender's count
  (`SendIdle.count`);
- a coin beyond the sender's count: the tables and the answers are the same whatever stands in for
  it (`sent_within_coins`, `Johnson/Desc/ProofFile/Honest/K14/SendingsWithin.lean`);
- a message that lies in no tree: the trees can be laid, and there is a tree for each message
  (`SendIdle.trees`; at the full size also `trees_at_head`, `width_all_head`,
  `Johnson/Desc/ProofFile/Honest/K14/WidthAllTrees.lean`);
- a code's number beyond its list: it lies within the list at every message that has rows of that
  sort (`SendIdle.base`, `SendIdle.mask`);
- a seed beyond the list: the list has a seed for each answer (`SendIdle.seeds`);
- a mask code shorter than a fresh table's row of coefficients: the coefficients fit the code's
  message length (`SendIdle.fresh`).

For the cases that depend on a run: `k14_row_at_return`
(`AtFullSide/K14/RowIsWholeAtServedRuns.lean`) says, under `P5J.AtMgA` and with no invariant, that
at the states of a run in front of the two senders and of "SPLIT" (a sub-protocol's name in the
description), and behind each sender's first round, the shared point and the challenge of "LIN zeta"
(another such name) are received whole, the seeds are whole and no factor is 0.

**The limits.**

- A position, in these statements, is a position of the rows that the encoder is handed, not of a
  column that is sent: a coin of a row may reach every symbol of that row's codeword. Each statement
  is an equation or a congruence at each value of the coins. No distribution occurs in them, and
  what follows from them for what a verifier sees is not stated there.
- Any two rows of a fold's fresh table share coins: the constant's coin and the coins of every
  variable above h stand in every row (`plan_rows_high`,
  `Johnson/Desc/ProofFile/Honest/K14/SendingsPlan.lean`), and all rows together have 2 k + 1 coins
  (`plan_below`, `plan_last_all`).
- These statements say nothing of a shape that the test rejects.
- A message's number beyond the sender's list, and the default code at a message without rows of
  that sort: no sentence; by the definitions' text the first does not occur and the second is
  multiplied by 0 rows or read by nothing.
- A vector that does not fit its rows is cut; and if the matrix's positions reached into the
  positions kept for random pads, an entry of the matrix would be laid where a pad is due.
  `linOk_at_head` (`Johnson/Desc/ProofFile/Honest/K14/SendingsAtFilling.lean`) says that the
  library's test on the linear part's shape and codes (`OnBytes.linOk`) accepts under `P5J.AtMgA`;
  `sendingsFit` does not ask it. That this test excludes both cases is a reading of its text, not a
  theorem.
- Of `k14_row_at_return`: that such a state of a run exists is not said there; that a run passes
  through the states behind a sender's first round is a reading of the definition `walk`.
- Some positions hold 0 by definition and are sent or committed so: positions of a fold's fresh
  table to which no coin is assigned (`spot_zero`; no statement says which positions these are), the
  free positions of a main row, rows beyond the real ones where the number of rows is no power of
  two, and three zones of a committed row. No statement compares these zeros with the specification
  of the byte format (`docs/format/`).
- That the list of cases is complete is a reading of the definitions, not a theorem.

**What it touches:** as at L96.

Basis: by reading (the statements, definitions and opening comments named; that no statement says
more: a search of the files' text, which can miss what Lean fills in by itself).

### A test on the shape that no definition of the honest provers asks

**L98.** The honest provers take the offline prover's senders as an argument (`Parts`); the six
lines stand at one value, `thePartsAt`. The committed rows that the shared chain's two sendings and
three of the four proximity tests read (`rowsOf`) hold an entry of the weights' matrix where a pad
is due at a shape whose matrix's places run into the pads. `LinShape.ok` refuses such a shape, and
no definition of the provers asks that test. That `thePartsAt`'s shape passes it at public files in
use is read off three theorems that no one theorem joins (`sourced_of_ok`, `third_public`,
`linOk_ok`). Of other values of `Parts` the six lines say nothing.

**What it touches:** zero knowledge first, and completeness too (L91 to L93). The like case at the
two senders of the batch's shared rounds: L97.

Basis: by reading (the definitions `Parts` (`E2E/TheHonestProver.lean`), `thePartsAt`
(`E2E/KeyArgumentsAt.lean`), `rowsOf` (`Johnson/Desc/ProofFile/Honest/K14/Parts.lean`) and
`LinShape.ok` (`OnBytes/Iop/Lin.lean`); the statements of `sourced_of_ok`
(`E2E/KeyThePartsFacts.lean`), `third_public` (`E2E/KeyPublic.lean`) and `linOk_ok`
(`OnBytes/Params/Fit/TreesSized.lean`); that no one theorem joins them: a search of the files' text,
which can miss what Lean fills in by itself).