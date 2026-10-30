# The proof of the soundness theorem on `verify`, step by step

Terms: [TERMS.md](TERMS.md).

This page follows the proof of `VerifierAndGoals.AtTheName.sound_of_verify_at` from the top down,
for a cryptographer who knows none of this library's names. Of the six theorems, `sound` rests on it
([LIMITS.md](LIMITS.md), "What is proved, and of which object"). This page serves to follow the
argument, not to learn what is claimed: that, with every limit, stands on [THEOREM.md](THEOREM.md)
("What it does not say", "What to read").

## The argument in one paragraph

`verify` is compiled, by Merkle trees and the Fiat–Shamir transformation, from three interactive
oracle proofs (IOPs), which together make up the IOP that THEOREM.md states: one on the committed
table that encodes the weights (key file), one that ties a further encoding of the same weights to
it (copy's file), one on a request (proof file). The extractor reads the table off the committer's
hash queries and decodes it. If every round of the IOPs has a round-by-round soundness error of at
most 2^-128, proof of work counted where a round has it, each hash query costs a small multiple of
that, and a union bound gives the theorem's error. The rest shows that the rounds are that good,
down to a bound on Reed–Solomon codes, and that the IOPs' relation says that the output is the
integer model's. A second proof of the same statement goes through soundness as an IOP of the one
protocol: what it adds, and what not: [LIMITS.md](LIMITS.md), L89.

## How much there is to read, and what is taken on trust

The argument turns at few statements. Under each step stand its chief Lean texts, in bold, with file
and line under `lean/` and length (of a theorem: the statement, without the proof). They are for
following the proof. Lean's kernel checks the proofs, so nobody needs to read them: a person reads
what is proved: [STATEMENTS.html](STATEMENTS.html). The 28 bold texts are 236 lines in all.

These texts are the statements at which the argument turns, and few of the proofs; the theorem uses
many more files ([README.md](README.md)), and definitions that stand outside the files named here.
That each statement follows from what lies beneath it is taken from Lean's kernel. The theorem's
statement has three hypotheses (the public files are in scope; they are read; their policy is exact
match) and no further one: no lemma about a sub-protocol and no conjecture on codes is assumed. It
rests (THEOREM.md, "What it rests on") on Lean's kernel and three standard axioms, on the format's
hash function as a random oracle, sampled after the public files are fixed, and on a second, fixed
hash function, built on BLAKE2b's compression function, assumed not to interact with the random
oracle; the bounds on codes are proved, from files adapted from ArkLib and Mathlib (step 16). What
stands in the theorem's statement, inside `verify`, is the text of the three IOPs and the tests on
the public files. The notions by which part B orders the proof (conditions and claims between
sub-protocols, the bound on a round's error) do not stand in it: had this page misdescribed those,
the theorem would still say what THEOREM.md says. Of their kind two things do stand there: the
planner, which `verify` runs on the public files, computes a figure for every round's error by
formulas of its own and refuses a plan in which a round misses the parameter file's target; and one
test weighs the attention rounds' counts of bad challenges. Lean checks the proof, not this page.

On names: `P5J`, `Cms`, `Ride` and their like in names and paths are working labels of parts of the
library; they say little or nothing of the content ([GLOSSARY.md](GLOSSARY.md)). `Hole` and `hole_`
mark a named hypothesis of the general theorem, filled at this protocol, not a hole in the proof.
The words that the Lean files' comments use are at the end of this page.

## The objects

- **Public files** (`Z`): a parameter file, which holds the acceptance policy, a layout file and a
  scale file. They fix the protocol's sizes and the integer model's scales. **In scope**
  (`InScope`): the layout and the parameter file of the full-size example, but for eight free
  numbers; the scale file is free within what the reader of the files accepts.
- **Policy**: three numbers that say how far an output may fall short of the model's first choices.
  **Exact match** allows nothing: each token is the model's next token.
- **Index**: the weights. The committer encodes them as a table of Reed–Solomon codewords under a
  Merkle root. The **commitment** is 256 bits (step 5).
- **Key file**: the root, the table's OOD sample (step 3) and a one-time proof that the table is
  well formed. **Copy's file**: the format encodes one index more than once; this file holds the
  root and the OOD sample of a further encoding of the same weights, with a proof that links it to
  the first. **Proof file**: the proof for one request, a prompt and a claimed output; it is made
  against the copy. In the theorem all three come from the adversary.
- **One request, or a batch.** `verify` gets one prompt, one output and one proof, and the theorem
  speaks of one. A prover may serve up to 64 requests against one copy at once and run a part of the
  protocol, step 8's shared chain, once for all: the hash chain of each request's first chain ends
  in a leaf of a Merkle tree of depth 6; the shared chain's challenges are hashed from that tree's
  root; the request's last chain goes on from the shared chain's last value and the request's own;
  and a proof holds the root, its leaf's number and the path. So one hash answer is a shared round's
  challenge for up to 64 requests of the adversary's choice, and the proof file's condition in step
  3 bounds the bad challenges jointly, for every vector of up to 64 requests.
- **Two hash functions.** The format's main one is the random oracle; the eight digests of the
  public files (steps 5 and 18) come from it. A second (`OnBytes.secondHashFunction`;
  `atSecondHashFunction D` is the protocol `D` with it put in; in some names (`extractor_atOlder`,
  `bindsWith_atOlder`) the word Older means this function; no age is meant) digests the public
  tables and parts of the statement, the prompt and the output among them. It is one fixed function
  throughout. No further property of it is assumed, collision resistance included; what is assumed
  is that it may be treated as separate from the sampled one (THEOREM.md, "What it rests on"). How
  the request is bound without it: step 4.

## The proof as a tree

The numbers are the steps below.

```
(outside the proof: the executable form, 19)
sound_of_verify_at (1)
└─ sound_at (1)
   ├─ exact match, from the form under a policy (2)
   └─ seven facts and a general theorem (2)
      ├─ the general theorem: three conditions (3), the compiler (4), four wrappers (5),
      │     side conditions (6)
      ├─ the three conditions, needed only where the tests on the public files pass (7):
      │     ├─ the proof file's (8)
      │     │     ├─ first chain: a lemma for each kind (9), joined (10), its two ends (11)
      │     │     ├─ shared and last chain (12)
      │     │     └─ standing hypotheses, from the verifier's own tests (13)
      │     ├─ the key file's (14)
      │     ├─ the copy's file's (15)
      │     └─ beneath 6, 9, 12, 14 and 15: the bounds on codes (16)
      ├─ what the relation means; the extractor (17)
      └─ the error (18)
```

## The chief Lean texts

| step | Lean text | file and line | lines |
|---|---|---|---|
| 1 | `VerifierAndGoals.AtTheName.sound_of_verify_at` | `Johnson/Goal/Skeleton/SoundOfVerifyAt.lean:69` | 5 |
| 2 | `VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_of_two` | `Johnson/Goal/Skeleton/TopAtZ.lean:194` | 3 |
| 3 | `VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.keySound` | `Johnson/Top/InnerCompiledVerifier.lean:157` | 3 |
| 3 | `VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound` | `Johnson/Top/InnerCompiledVerifier.lean:163` | 4 |
| 3 | `VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound` | `Johnson/Top/InnerCompiledVerifier.lean:170` | 4 |
| 4 | `TypedOracleCompiler.Compile.Batch.Cms.BcsAtA` | `Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean:206` | 21 |
| 4 | `TypedOracleCompiler.Compile.Batch.Cms.cmsRA_binding_at` | `Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean:75` | 14 |
| 4 | `Iop.BatchInteractiveOracleProof.SndBL` | `Iop/Batch.lean:392` | 12 |
| 5 | `VerifiableInference.OnPublicFiles.verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor` | `Johnson/Top/InnerCompiledVerifierByPublicReading.lean:640` | 32 |
| 6 | `FlashProve.compilerSoundnessConditions_layoutsByPublicReading` | `Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean:115` | 12 |
| 7 | `FlashProve.keySound_theLay` | `Johnson/Goal/Conditions/NumbersAtThe.lean:118` | 4 |
| 8 | `VerifierAndGoals.AtTheName.RowsOfProofFile` | `Johnson/Goal/Skeleton/ProofFile.lean:82` | 26 |
| 9 | `VerifierAndGoals.AtTheName.kindsLaws_at_head` | `Johnson/Goal/Skeleton/KindsLawsAtHead.lean:68` | 5 |
| 9 | `TypedOracleCompiler.Run.PQ.roundS` | `OnBytes/TypedOracleCompiler/Run/PlanQS.lean:38` | 11 |
| 10 | `VerifiableInference.Desc.Plain.fold_chain` | `Johnson/Desc/Plain/FoldChain.lean:61` | 6 |
| 11 | `VerifiableInference.OnPublicFiles.tie_of_some` | `Johnson/Goal/Meaning/TieAtSome.lean:91` | 16 |
| 12 | `P5J.five_at_free2_laid2` | `Johnson/P5J/FiveAtFree2Laid2.lean:54` | 3 |
| 12 | `Desc.K14.Law.ownPt_below` | `Johnson/Goal/Numbers/K14OwnAllAt.lean:111` | 4 |
| 13 | `P5J.headA_at_name` | `Johnson/P5J/AtNameA.lean:42` | 4 |
| 14 | `VerifierAndGoals.AtTheName.keySound_at_live_holds` | `Johnson/Goal/Conditions/KeyOpenHolds.lean:95` | 3 |
| 15 | `FlashProve.hole_entrySound` | `Johnson/Goal/Conditions/EntrySits.lean:47` | 2 |
| 16 | `Cb.BCHKS46At` | `Cb/Gen/CodeListRSAt.lean:88` | 5 |
| 16 | `Cb.Bridge.foldErr_ix` | `Johnson/Bridge/FoldErrIx.lean:51` | 9 |
| 17 | `OnBytes.Road.L5.sound_ledger` | `Johnson/Road/Lane5SoundLedger.lean:65` | 7 |
| 18 | `VerifierAndGoals.frame_le_bits` | `Ladder/BitsOfStep.lean:64` | 5 |
| 19 | `PV.Ride.verdictThe_is_theDescription` | `Johnson/PVR/RideThe.lean:133` | 5 |
| 19 | `PV.Ride.verdictThe_eq` | `Johnson/PVR/RideEveryHash.lean:116` | 5 |
| 19 | `PV.Ride.sound_of_the_form_events` | `Johnson/PVR/SoundOfTheFormEvents.lean:252` | 6 |

## A. From the statement to three IOPs

**1. Unfold the statement.** `Sound` and `verify` are short definitions. The theorem's proof and
five theorems beneath it only fill in hypotheses, from steps 8 to 14; the argument starts at
`VerifierAndGoals.AtTheName.sound_at` (`Johnson/Goal/Skeleton/TopAtZ.lean:225`).

- **`VerifierAndGoals.AtTheName.sound_of_verify_at`**: the theorem.
  `Johnson/Goal/Skeleton/SoundOfVerifyAt.lean:69`, statement, 5 lines

**2. The plan; exact match comes last.** All below is proved for the claim "the output meets the
public files' policy", at a named extractor (that form is a theorem of its own: THEOREM.md, "The
theorem under a policy: other acceptance policies"). One theorem gathers seven facts at the given
public files: soundness of the three IOPs (steps 7 to 16), three facts on their relation's meaning
and on the extractor (17), the bound on the error (18). A theorem that is general in the protocol
(`VerifierAndGoals.Fit.soundForWith_system_of_toldO` (`Johnson/PV/FitO.lean:83`)) turns such facts
into soundness of `verify` (3 to 6). At exact match the claim says: the output is not empty, and
each token is the model's next (`Policy.meetsPolicy_exact_iff`
(`Policy/Front/MeetsPolicyGuards.lean:449`)); so the policy's form gives `Sound`
(`VerifierAndGoals.AtTheName.sound_of_atZ` (`Johnson/Goal/Skeleton/TopAtZ.lean:205`)).

- **`VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_of_two`**: gathers the seven.
  `Johnson/Goal/Skeleton/TopAtZ.lean:194`, statement, 3 lines

**3. Three IOPs, and what each must show.** After each committed table the verifier draws a seed and
the prover answers: the table's out-of-domain (OOD) sample. The decoder gives the nearest table of
codewords with these answers, if it lies within the radius and holds an index. At a collision, a
seed at which two tables within the radius answer alike, it gives nothing. Each IOP must be
round-by-round sound for a condition, a disjunction: where the disjunction fails, the prover has
lost from the start. For the key file and the copy's file, and all through part B, that is stated
without a state function: the prover is *doomed* towards an event on full transcripts, with errors
e₁, …, e_k, if, with no round left, the event holds, and else, whatever it sends next, at most e₁ of
the round's challenges lead to a position from which it is not doomed towards the event with e₂, …,
e_k. Soundness is "doomed towards: the verifier rejects". The proof file's condition is stated with
a state function, in a form for batches (step 4); step 8's rule gets it from chains that are
"doomed". Errors are counts of challenges; as a share of its round's challenges each must be at most
εs (2^-128: step 18), and a round that a batch shares is counted for all its requests together. Read
the three conditions first; step 4 says why these three.

- **`VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.keySound`**: key file:
  the table has a collision, or decodes. `Johnson/Top/InnerCompiledVerifier.lean:157`, definition, 3
  lines
- **`VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound`**: copy's
  file: the first table does not decode, or the copy has a collision, or both decode to one index.
  `Johnson/Top/InnerCompiledVerifier.lean:163`, definition, 4 lines
- **`VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound`**: proof
  file, in a form with a witness, for a batch (`SndBKT`, `Ior/KnowWide.lean`): the copy does not
  decode, or the request's relaxed relation (step 17) holds at its index.
  `Johnson/Top/InnerCompiledVerifier.lean:170`, definition, 4 lines

**4. The compiler's theorem.** *Index binding* is this game: the committer puts out a key; the
extractor, a fixed rule that may depend on the public files, names an index, or none, from the key
and the committer's hash queries alone; then the prover, with the committer's state, puts out an
instance and a proof. The error bounds the probability that the verifier accepts while no index was
named or the instance is not in the relation at the named index ([TERMS.md](TERMS.md): index-binding
knowledge soundness, in its witness-free case). If step 3's three conditions hold, with step 6's
side conditions, the compiled argument has index binding over typed random oracles (one for each
kind of query), at the error n·εs + 2(n+1)²/2^256, n = 5(q + v + 1): q the sum of a bound on the
committer's hash queries and a bound on the prover's, v a bound on the verifier's, the 1 a query of
the analysis that announces the root.

The proof fixes one event, Bad, on traces of queries. It is rare: an algorithm with t queries meets
it with probability at most t·εs + 2(t+1)²/2^256. (A new query's answer moves the state of one of
the three IOPs out of "doomed", or gives a seed with a collision: at most εs a query, and no query
is exempt. A new hash answer equals an earlier value: the square term.) Outside Bad all is
deterministic: the word under a root no longer changes once the root is announced; a seed that the
verifier has checked is no collision; an accepting run of each of the three compiled verifiers gives
its IOP's condition at the word under its root. So the three conditions fall like dominoes: the
first table decodes, the copy decodes to the same index, the relation holds there. The 5 is 1 + 4:
the three clauses on the verifiers are proved on traces in which the queries that give the OOD seeds
of a proof's roots stand before that proof's first Fiat–Shamir query; the analysis inserts them, up
to four before any query of committer, prover or verifier, which changes no output
(`OnBytes.Slice.between_law`, `OnBytes/Slice/WrapBetween.lean:236`).

**How the statement enters the hash.** In the theorem's game the prover picks the prompt and the
output with the random oracle in hand, so, in the random-oracle model, a weakness in how the request
is hashed would contradict the theorem. The IOP's instance is a window of 1,024 tokens (the prompt,
the output, padding that the proof brings, then zeros; step 17's fact 1 holds at every padding), the
two positions that bound the output, and one further token: 0, unless prompt and output have 1,025
tokens together, and then the last output token. The first query of the proof file's first chain
holds that instance with the further token set to 0, behind the copy's root and its OOD answers.
Typed queries are coded one to one into the hashed strings (a law in the coding's type): where the
query has the format's shape, the string of its chaining block spells the window and the two
positions byte for byte; elsewhere an escape code writes the whole typed query. The second hash
function's digest of the request stands in the same string; the verifier computes it itself, and no
step of the proof reads it (other words of that item are compared, public values against public
values): that the coding is one to one is proved from the request's own bytes, whatever the digests
are (`PV.MFull.apartI`, `Johnson/Top/Fire/Code/Dec/MOneD.lean:59`, for the queries of the format's
shape, those with the further token 0; every other query has the escape code), so a collision of the
second hash merges no two queries.

The further token enters the chain as a message of the prover, in a round of its own, and the last
test compares it with the announced one; so step 3's condition on the proof file is asked in a
"late" form, in which the state function sees the instance without that token, and "doomed" at the
end must rule out every accepted instance with that early part at which the relation fails (steps 10
and 11 meet it). The commitment is not in that query; the copy's root is, and the way from the
commitment to the copy is step 5's (the commitment is the hash of the key) and this step's dominoes
(the key's table, then the copy). In a batch each request has such a first query of its own, and its
chain's value is a leaf of the Merkle tree whose root stands in the shared chain's first query.

The public files are no part of what the prover picks: they are fixed before the oracle is sampled.
The IOPs and the tests on the public files are written out in Lean with a 32-byte constant in the
place of the files' digest; the hashed strings hold the digests that the verifier gets from the
oracle (step 5), which is meant to guard against public files tuned to the hash function, a case
outside the theorem.

- **`TypedOracleCompiler.Compile.Batch.Cms.BcsAtA`**: the invariant: Bad is rare, and what holds
  outside it, clause by clause. `Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean:206`,
  definition, 21 lines
- **`TypedOracleCompiler.Compile.Batch.Cms.cmsRA_binding_at`**: the theorem, for a strict and a
  relaxed relation (here both are the relaxed one).
  `Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean:75`, statement, 14 lines
- **`Iop.BatchInteractiveOracleProof.SndBL`**: the late form of round-by-round soundness.
  `Iop/Batch.lean:392`, definition, 12 lines

**5. From typed oracles to `verify`: four wrappers.** (1) The typed oracles become one hash
function, by a coding that is one to one and onto. (2) Digests of the public files, which the
verifier gets from that same function, may stand inside the strings that it hashes. (3) The
compiler's key (Merkle root and OOD sample), with a digest of the public files, shrinks to the hash
of its code, the 256-bit commitment: the committer now publishes the commitment alone, and the key
comes with the proof. The extractor takes the first key that the committer hashed to that
commitment, and none if there is none. No two keys have one code (a side condition of step 6), so
another key under the commitment needs a hash answer that repeats an earlier value; that costs
(q+2)²/2^256. Here, too, index binding turns into soundness for a claim on prompt and output (step
17's fact 1 is used here, facts 2 and 3 in step 2's general theorem). (4) The parser's queries and
those that hash the public files are added to q.

- **`VerifiableInference.OnPublicFiles.verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor`**:
  (4); the form that step 2's general theorem calls.
  `Johnson/Top/InnerCompiledVerifierByPublicReading.lean:640`, statement, 32 lines

**The compiler as an object, for every input.** Steps 3 to 5 are stated of any input, not of this
protocol alone. An input (`VerifiableInference.OnPublicFiles.InnerCompilerInput`
(`Johnson/Top/InnerCompiledVerifier.lean:59`), twenty fields) holds any object of the library's type
of a protocol with records (`protocol : HolographicProtocol Index Instance`: three IOPs with the
encoder and the decoder of an index) and, written by hand beside it, which rounds are shared, how
rounds and openings are laid into hash queries, the seeds' queries, three codings, how an instance
is built, the model and an honest side. `innerSystem` (`:124`) makes an argument system from an
input, and `innerCompiledVerifier` (`:128`) is that system's verifier. `CompilerSoundnessConditions`
(`:239`) is step 6's list of the compiler, step 3's three and the twelve, as one structure of
fifteen named hypotheses. With a sixteenth, on what the relation means (at this protocol: step 17's
fact 1), `innerCompiledVerifier_sound` (`:299`) states soundness of `innerCompiledVerifier` at every
input that is fixed before the hash function is drawn. The proof of step 1's theorem does not call
that theorem: the strings that `verify` hashes hold digests that the hash function itself gives
(wrapper 2), so it goes by `verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor`, which asks
`CompilerSoundnessConditions` at every value of the digests; both rest on step 4's theorem, through
`CompilerSoundnessConditions.binds` (`:264`). At every input whose type of witnesses has one
element, soundness as an IOP of the object is four of the fifteen together with a count of the seeds
at which a table has a collision (`indexKnowledgeSoundIOP_iff_premises`
(`Johnson/Top/SoundAsIOPIsThePremise.lean:68`)). `InnerCompiledVerifier.lean` gives no object and
shows none to meet the sixteen: that is steps 6 to 17.

**6. The side conditions hold at this protocol.** Beside step 3's three, the compiler's list has
twelve conditions (two of them: uniform hash answers give uniform challenges; a seed with a
collision has probability at most εs), and the wrappers ask nine (one: domain separation between the
public files' strings and the protocol's queries). All twenty-one are theorems at this protocol, at
all public files and every value of the digests; the wrappers' nine are given one by one in
`FlashProve.publicReadingFitAtDescriptionOfFields`
(`Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFieldsO.lean:43`).

- **`FlashProve.compilerSoundnessConditions_layoutsByPublicReading`**: the compiler's whole list,
  step 3's three and the twelve, from step 3's three, under nine conditions on numbers.
  `Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean:115`, statement, 12 lines

## B. The three IOPs are sound, round by round

**7. Only where the tests on the public files pass.** `protocolDataWellFormed` is a list of tests
that `verify` itself runs on the public files. Where one fails, the three verifiers reject
everything, and step 3's conditions hold for that reason. So steps 8 to 14 assume that they pass.

- **`FlashProve.keySound_theLay`**: for the key file; the two others stand beneath it.
  `Johnson/Goal/Conditions/NumbersAtThe.lean:118`, statement, 4 lines

**8. The proof file is three chains.** A chain is a list of places, each a sub-protocol or a
book-keeping row of the verifier's own, each handing the verifier's state to the next; a border is
the point between two places. Read what the decoder gives for the copy as a matrix A with 3,076,096
rows and 2^18 columns: the table's 2^11 rows are the high 11 bits of A's column number, so a point
for A's columns is a pair (ψ_lo, γ) of 7 and 11 coordinates, and γ alone weighs the table's rows.

*The first chain* (358 places; the request's own challenges) walks through the model and reduces a
statement M on the request (step 11) to **the first claim**, one linear equation on the weights: ⟨g
⊗ eq(ψ, ·), A⟩ + ℓ(masks) = t. Here g (weights on A's rows), ψ (a point for its columns), the linear
form ℓ and the value t stand in the verifier's state, and "masks" is a committed message. The
segments' claims on the weights have been batched into this one, and the prover has committed to a
vector W, said to be gᵀA.

*The shared chain* (twelve places; one run for a batch) does the part of testing such an equation
that does not depend on g. The verifier draws one point ψ* = (ψ_lo, γ). The prover commits to u,
said to be the combination of the table's rows with weights eq(γ, ·); the verifier holds u against
the table's OOD answers and against the table's columns at random positions. The prover then commits
to Ω, said to be A·eq(ψ*, ·), and a further random point ties Ω to u. Two proximity tests with
linear constraints, one on u's group of committed words and one on Ω's, close this. What is left is
**the second claim**, two equations on committed vectors: ⟨eq(ψ, ·), W⟩ + ℓ(masks) = t, and ⟨eq(ψ*,
·), W⟩ = ⟨g, Ω⟩. With W = gᵀA the first is the first claim; if Ω is as said and W is not gᵀA, the
second fails at all but a share 18/|E| of the points ψ* (E: the challenges' field).

*The last chain* (four places; the request's own challenges again) takes Ω into W's group of
committed words and adds the second equation to it as a constraint (the first lies there since the
first chain's batching); one proximity test closes both. Behind it no claim is open.

In a claim, A, W, Ω and the masks mean what the committed word decodes to with its OOD sample: the
claim says that such values exist and meet the equations. Each chain also hands on a condition on
the state and the oracles, under the same errors. The copy's table has no proximity test in the
proof file: where it does not decode, step 3's condition holds for that reason, and that it decodes
is what the two other files give (step 4's dominoes).

- **`VerifierAndGoals.AtTheName.RowsOfProofFile`**: seven fields, each with a sentence: the three
  chains; the part of the shared chain's start on which its common bad challenges depend is a
  function of the committed table and its OOD sample alone; an accepting run of the IOP is a run of
  the three chains; step 11's tie; every round's error is at most εs; with four equations they give
  the proof file's condition (`VerifierAndGoals.AtTheName.proofSound_of_rows`
  (`Johnson/Goal/Skeleton/ProofFile.lean:110`)). `Johnson/Goal/Skeleton/ProofFile.lean:82`,
  definition, 26 lines

**9. One lemma for each kind of sub-protocol.** The first chain has 358 places: book-keeping rows,
and thirteen kinds of sub-protocol ([GLOSSARY.md](GLOSSARY.md), `K1` to `K13`): sending with an OOD
sample, code switching, lookup, a group of layers' rounds, attention, output head, next token, the
random matrix of the approximate range proof, batching, closing a segment, merging, proximity test,
batching the claims on the weights. A table of joints ([GLOSSARY.md](GLOSSARY.md), "table of
joints") gives, for each border, a condition on the verifier's state and the claims that are open
there. A kind's lemma says: at each of its places, at every state that the chain can reach, the
sub-protocol is round-by-round knowledge sound between the table's entries for its two borders. Its
errors are set to εs, so the lemma holds the comparison with 2^-128.

*Knowledge.* There is one type of witness for the whole proof file: the table's content, the token
received, and the content of each committed message. Each sub-protocol comes with a map on
witnesses: set the components that this sub-protocol answers for to what the committed words decode
to with their OOD samples (the token: to what the state holds), and leave the rest. A lemma says:
whatever witness meets the claims behind, its image meets the claims before. Nothing has to start
the maps: behind the last chain's last place no claim is open, so any witness will do. Along the
first chain one witness is followed, for its token's sake; at the first border it is read as step
11's trace. M keeps only that there is one, and the witness in step 3's condition is empty at this
protocol.

*Proof of work.* In the rounds in which the verifier draws query positions, the IOP itself holds a
proof of work of w = 20, 28 or 32 bits (which rounds: the second table below). The prover's message
ends in a nonce, which the IOP's verifier never reads; the verifier's message is a pair (c, z), the
challenge proper and w more uniform bits; each of the three verifiers, and each sub-protocol,
rejects unless z = 0 in every round. So a challenge with z ≠ 0 leaves the prover doomed for good,
and over each c exactly one (c, z) passes: if s of the S values of c are bad, s of the S·2^w values
of (c, z) lead out of "doomed". That is all that the proof of work counts for. Steps 3 and 4 know
nothing of work: they count bad challenges among all challenges of a round as it is written. After
compilation the nonce stands in the round's Fiat–Shamir query and z is read off the answer, so a new
nonce is a new query: step 4's union bound charges it εs like any other, and it counts in q. In the
random-oracle model this asks nothing on what a try costs; what counting it assumes of the real hash
function: [GAPS.md](GAPS.md), "36 · What the level means: three quantities".

- **`VerifierAndGoals.AtTheName.kindsLaws_at_head`**: names each kind's lemma, and the book-keeping
  rows' (`frame`); `k14` and `k15` have no place on this chain; the proximity test's stands behind a
  condition on the public files, which follows from the scope and step 7's tests
  (`H2K12.lastTypedAt_of_live` (`Johnson/Loose/H2K12/LastTypedOfLaid.lean:90`)).
  `Johnson/Goal/Skeleton/KindsLawsAtHead.lean:68`, statement, 5 lines
- **`TypedOracleCompiler.Run.PQ.roundS`**: a round of the three IOPs: a nonce in the message, w bits
  in the challenge. `OnBytes/TypedOracleCompiler/Run/PlanQS.lean:38`, definition, 11 lines

**10. Joining the lemmas.** In the table, what stands behind one place stands before the next, so
the lemmas compose to the first chain's field of step 8. One more fact is needed: only the
sub-protocol that receives the next token alters it, so the IOP's last test compares the claimed
output with the token that the output head's claims were about. A guard inside `verify` gives it:
after every place of the first chain but that one, `verify` checks that its stored value of the
token is unchanged, and rejects if it is not (THEOREM.md, "What it does not say").

- **`VerifiableInference.Desc.Plain.fold_chain`**: composes the places' lemmas into the chain's
  statement. `Johnson/Desc/Plain/FoldChain.lean:61`, statement, 6 lines

**11. The two ends of the first chain.** At the first border the table lists the claims that are
open, among them four for each of 25 segments (twelve groups of layers, twelve of attention, the
output head). Together they say that some trace of intermediate values meets the model's conditions
segment by segment, at what step 3's decoder gives for the copy, with the token that the chain
received: that is M. A theorem on the 24 segments before the head turns these conditions into a run
of the integer program through all 48 layers, and so M into the proof file's relation at the decoded
index. At the far end, the last test's yes says that the token received is the request's.

- **`VerifiableInference.OnPublicFiles.tie_of_some`**: M and two facts (the first border's condition
  holds; the last test gives the token) give the relation. `Johnson/Goal/Meaning/TieAtSome.lean:91`,
  statement, 16 lines

**12. The shared chain, the last chain, and where the chains meet.** Step 8 says what these chains
do. The lemmas have step 9's form, each at its own count, which is within 2^-128, and so at most εs.

*Shared chain*: six places of a kind of its own (`K14`), two sendings, two proximity tests, two
book-keeping rows. At the place that draws ψ* the lemma has two events. One depends on the table and
its OOD sample alone: γ is none of the weights at which some u can be close to the combination of
the table's rows and answer the OOD seeds rightly without being the combination of the decoded rows;
step 16's two bounds count these. The other may depend on the request: W = gᵀA, or ψ* is no zero of
the multilinear polynomial with coefficients W − gᵀA. The first count and 64 times the second are
within 2^-128: here alone a batch costs its factor. At the ten places behind it the lemmas hold for
any number of requests.

*Last chain*: its first place takes Ω over and adds the second equation; its proximity test's lemma
closes both equations, together with "W, the masks and Ω are what their words decode to".

*Where the chains meet*: what is open at one chain's end is, claim for claim, what is open at the
next one's start (one claim, on the state, passes into the condition), and the condition at the end
gives the condition at the start. The theorem that gathers these three also carries step 10's fact
on the token and step 11's on the output head.

- **`P5J.five_at_free2_laid2`**: the five facts: the two chains, where the chains meet, the token,
  the output head; from the standing hypotheses, step 7's tests and one premise, what is left of the
  last chain's lemma (`LastLeftAt`), which `P5J.AtMgA.lastLeft_at_head_alone`
  (`Johnson/P2LawR/LastLeftAlone.lean:69`) gives from the standing hypotheses alone.
  `Johnson/P5J/FiveAtFree2Laid2.lean:54`, statement, 3 lines
- **`Desc.K14.Law.ownPt_below`**: at a list of rounds that passes two written comparisons
  (`K14Rounds`, `pointNB`), the first count and N times the second are within 2^-128, for every N ≤
  64; the list written in Lean passes both, by evaluations in Lean's kernel
  (`Desc.K14.Law.k14_rounds_real` (`Johnson/Goal/Numbers/K14RoundsAt.lean:201`),
  `Desc.K14.Law.real_test64` (`Johnson/Goal/Numbers/K14JointAt.lean:112`)).
  `Johnson/Goal/Numbers/K14OwnAllAt.lean:111`, statement, 4 lines

**13. The standing hypotheses are the verifier's own tests.** Steps 9 to 12 share one bundle of
hypotheses. It follows from the scope, from `readFiles` and from step 7's tests: what these steps
need of the public files, `verify` tests. Some of the tests compare the list of rounds that is
computed from the public files with values written into the Lean text, so that most other conditions
become facts on constants.

- **`P5J.headA_at_name`**: the bundle from the tests and one named condition (`At.Conds`), which
  `P5J.conds_of_laid` (`Johnson/Goal/Skeleton/CondsOfLaid.lean:134`) has from the same three, with
  `P5J.owed_of_live` (`Johnson/Goal/Skeleton/OwedOfLive.lean:38`). `Johnson/P5J/AtNameA.lean:42`,
  statement, 4 lines

**14. The key file.** It too is three chains, of 35 places. Fourteen are book-keeping. Each of the
other 21 has a lemma, four of them on proximity tests; they are joined as in steps 8 to 10, at the
same bound εs, under hypotheses that follow from the scope and step 7's tests. At the first border
the open claims say that the committed table decodes and that its entries lie in range: step 3's
condition.

- **`VerifierAndGoals.AtTheName.keySound_at_live_holds`**: the key file's condition.
  `Johnson/Goal/Conditions/KeyOpenHolds.lean:95`, statement, 3 lines

**15. The copy's file.** The link is one chain of eight places: four of a kind of its own (`K15`), a
sending, a proximity test, two for book-keeping. It is treated whole, at explicit counts of bad
challenges, written out in Lean, which are then compared with 2^-128. Its condition holds at all
public files.

- **`FlashProve.hole_entrySound`**: the copy's file's condition at this protocol.
  `Johnson/Goal/Conditions/EntrySits.lean:47`, statement, 2 lines

**16. The bounds on codes.** The lemmas on folding and on proximity tests (steps 12, 14 and 15; in
step 9, closing a segment and the proximity test) rest on theorems on Reed–Solomon codes, above all
mutual correlated agreement below the Johnson radius. As typed in Lean, they are proved in this
library, not assumed, from files adapted from ArkLib and Mathlib (`lean/LIMITS.md`, L15). That says
nothing on whether the published theorem (Theorem 4.6 of ePrint 2025/2055, the full version of a
paper published at STOC 2026) is formally verified. Their match to the published statements has not
been independently compared. Two bounds carry everything.

*Agreement.* Take the Reed–Solomon code of the polynomials of degree at most k on n distinct points
of the base field, with words over the challenges' field E; put ρ = k/n. Take a radius of e ≥ 1
positions below the Johnson radius: δ = e/n < 1 − √ρ. For two words u₀, u₁ call z exceptional if
u₀ + z·u₁ agrees with a codeword on some set of at least n − e positions on which u₀ and u₁ do not
both agree with codewords. Then at most B(n, k, e) = (2(m + ½)⁵ + 3(m + ½)δρ)/(3ρ^(3/2))·n + (m +
½)/√ρ values z in E are exceptional, with m = max(⌈√ρ/(1 − √ρ − δ)⌉, 3). At fixed ρ and δ the bound
is linear in n, and it does not depend on the field. By reading, not machine-checked, it follows
from the two-word case of Theorem 4.6 of ePrint 2025/2055. The paper's own form is not proved in
this library's files that prove the statement above (LIMITS.md, L15).

*Lists.* With n positions, distance d and a radius e with n(n − d) < (n − e)², at most L(n, d, e) =
⌊n(d − e)/((n − e)² − n(n − d))⌋ codewords lie within e of any word: the Johnson bound. It holds for
tables of any number of rows, a position being a column.

*From two words to a table.* A table costs what two words cost: for two tables of any number of
rows, with agreement on a common set of columns, the exceptional z are exceptional for one fixed
linear combination of the rows, so B bounds them too. And 2^r rows, folded with the multilinear
weights eq(γ, ·) at γ in E^r, cost r lines: one variable at a time, each step is a line through two
half tables. So at most r·B·|E|^(r−1) points γ are exceptional. Outside these, whatever is close to
the folded word is the fold of one of at most L tables. For a table without a collision at its seed,
a listed table with the OOD answers that were sent is the decoded one, and one with other answers
survives at no more than r·|E|^(r−1) points.

*One round, worked.* In the first round of the shared chain the verifier draws 18 elements of E, 11
of them to fold the table's 2^11 rows into one word; |E| = p³, about 2^192; the round has no proof
of work. Here n = 2^32, k = 446,693,374, e = 2,852,142,980: ρ = 0.1040, √ρ = 0.3225, δ = 0.6641, so
1 − √ρ − δ = 0.01344 and m = 24; then B is about 2^59.4, and L = 26. The lemma's count of bad
challenges, as a share, is (11·(⌊B⌋ + 26) + 18·N)/|E| for a batch of N ≤ 64 requests: about
2^-129.15. Lean does not compute B. It proves ⌊B⌋·2^132 ≤ |E| and then compares natural numbers in
its kernel: a written ceiling of the count, times 2^128, against the number of challenges, with a
factor (1 + 2^-128) for each hash block from which the elements are drawn. Three rounds later the
verifier draws 64 positions of the table: if u's codeword is not within e of the folded table, all
64 positions agree with a share of at most (1 − δ)^64, about 2^-100.7, and the round's 28 bits of
work make it 2^-128.7; Lean proves that its comparison passes at 28 bits
(`Desc.K14.Law.k14_rounds_real`), and, in a theorem beside the proof, that it fails at 27
(`Desc.K14.Law.teeth`; both in `Johnson/Goal/Numbers/K14RoundsAt.lean`). The logarithms in this
paragraph are arithmetic on Lean's numerals, no Lean theorem. The margins are small: the radii are
taken about as far towards the Johnson radius as the rounds allow.

- **`Cb.BCHKS46At`**: agreement, for two words; proved: `Cb.Bridge.bchks46At`
  (`Cb/Bridge/CodeListRSProved.lean:94`). `Cb/Gen/CodeListRSAt.lean:88`, definition, 5 lines
- **`Cb.Bridge.foldErr_ix`**: together, for a table without a collision at its seed: at most r(⌊B⌋ +
  L)·|E|^(r−1) bad fold points. `Johnson/Bridge/FoldErrIx.lean:51`, statement, 9 lines

## C. What the relation means, and the error

**17. From the relation to the model.** The compiler tells a strict relation, for the honest side,
from a relaxed one, for soundness; soundness reads the relaxed one alone. It is arithmetic: cells
that are small integers, the model's identities modulo a prime, lookup keys that stand in their
tables. Step 2's three facts: (1) a witness of it at an index gives "the output meets the policy"
for the integer model at the index's weights; (2) where that claim holds, the map from a decoded
matrix to weights is defined and gives step 2's claim at these weights, at the settings that
`readFiles` returns; (3) the extractor that the protocol names is that of steps 4 and 5 (the word
under the root, off the committer's queries, decoded), followed by this map.

- **`OnBytes.Road.L5.sound_ledger`**: from a witness of it to the integer model.
  `Johnson/Road/Lane5SoundLedger.lean:65`, statement, 7 lines

**18. The error.** εs is 2^-128. The compiled verifier asks at most 2^20 typed queries (step 4's v),
the hashing of the public files eight, the parser one (the 1 in `soundnessErrorInQueries q 1`). The
2^23 in T = q + 1 + 2^23 is an allowance for v, the eight and the query that announces the root, so
n ≤ 5T. Steps 4 and 5 then give at most `soundnessErrorInQueries q 1` = 16·T/2^128 + (T+2)²/2^256
wherever that is below 1; elsewhere there is nothing to prove. The square term that is left pays
step 5's. The compiler's own, 2(n+1)²/2^256, is paid out of the linear term, since below 1 we have
16T < 2^128: the four bits between 128 and the theorem's 124 for each hash query (THEOREM.md) cover
the factor 5 and that term. At q = 0 the bound is about 16·2^23/2^128 = 2^-101. Every hash query of
the committer and the prover counts in q, a try at a proof of work among them (THEOREM.md, "The
error").

- **`VerifierAndGoals.frame_le_bits`**: the arithmetic. `Ladder/BitsOfStep.lean:64`, statement, 5
  lines

**19. Outside the proof: the executable form.** Lean marks `verify` noncomputable, so as typed it
cannot be executed (THEOREM.md, "The executable form, and how to run it"). A second Lean term, its
executable form (in the Lean files' comments: the step-by-step form), can, and whatever verdict that
form gives is the value of `verify` at the same hash function, by a theorem: a theorem on the term;
a run also trusts Lean's evaluator and compiler, and the program that calls it.

At every function from byte strings to 32 bytes the form gives a verdict, so there its verdict is
`verify`'s value; and every hash function of the model is given by such a function. These are
equations between two values. A soundness statement of its own, `SoundOfDecision`, is also proved of
the form's decision, under the theorem's three hypotheses and at its bound. `Sound` itself asks for
a verifier that queries the hash function, as a step of the experiment, and the form is a plain
function that is handed the hash function whole; so that statement has a form of words of its own,
`SoundOfDecision`, which at the system's own decision is `Sound`, in both directions. It is
`Sound`'s text line by line, except that the experiment stops after the prover's step and hands on
the commitment and the proof, and the decision, taken at the drawn hash function, is part of the
event. No theorem has `Sound` of a system built from the form. For each drawn hash function the form
is handed a function on bytes from which that hash function is read back. Where these functions
answer with 32 bytes, "the form is sound" and "`verify` is sound" are one statement. The library's
own functions (`Run.oOf`) do; they are defined with the axiom of choice, have no code, and are not
the real hash function. For others the statement bounds a lower integral, since measurability is not
shown. All this is said of the term's value, not of a run.

- **`PV.Ride.verdictThe_is_theDescription`**: the tie: whatever verdict the form gives at a function
  O on bytes is `VerifierAndGoals.verify …` evaluated at `hashOf O`, the hash function that is read
  back from O. `Johnson/PVR/RideThe.lean:133`, statement, 5 lines
- **`PV.Ride.verdictThe_eq`**: at every O with 32-byte answers the verdict is `verify`'s value at
  `hashOf O`; its left side is a term with code. `Johnson/PVR/RideEveryHash.lean:116`, statement, 5
  lines
- **`PV.Ride.sound_of_the_form_events`**: the form's decision meets `SoundOfDecision` at the
  theorem's bound, under its three hypotheses, whichever functions on bytes it is handed, if the
  hash function is read back from each; "no verdict" counts as no accept.
  `Johnson/PVR/SoundOfTheFormEvents.lean:252`, statement, 6 lines

## Two tables of numbers

| what | value | Lean text |
|---|---|---|
| the codes' field | p = 2^64 − 2^32 + 1 | `Code.pGold`, `Code/Field.lean:400` |
| the challenges' field E | its cubic extension, x³ = 2 | `Cb.Gl.E`, `Cb/Gl/GlField.lean:108` |
| a row of the committed table | a codeword of length 2^32 for 402,653,184 message entries and 44,040,191 random ones (rate about 0.104) | `OnBytes.Slice.recT`, `OnBytes/Slice/RecordFull.lean:56` |
| its rows | 2^11 | `OnBytes.Slice.recV`, `OnBytes/Slice/RecordFull.lean:59` |
| OOD answers for each row | 1 | `OnBytes.Slice.recS`, `OnBytes/Slice/RecordFull.lean:63` |
| the decoder's radius | 2,852,142,980 of the 2^32 positions (about 0.664) | `OnBytes.Slice.frS`, `OnBytes/Slice/FullRecLink.lean:78` |
| that it is the decoder's | by definition | `OnBytes.Slice.fr_dec`, `OnBytes/Flat/EntryRecord.lean:155` |
| that radius | below the Johnson radius (about 0.678) | `OnBytes.Params.record_radius_inJohnson`, `OnBytes/Params/RecordRound.lean:163` |
| a collision at a seed | probability at most 2^-128 | `OnBytes.Flat.entryFull_seedLawK`, `OnBytes/Flat/RecordSeed.lean:50` |
| a batch | at most 64 requests | `FlashProve.slots_the`, `Johnson/Goal/Numbers/DepthAtThe.lean:78` |
| the model | 48 layers, 1,024 positions, a vocabulary of 202,048, width 5,120 | `Inst.Model.ppref`, `Inst/Model/Program.lean:122` |
| εs, the bound on each round | 2^-128, by definition (that the rounds meet it: steps 8 to 15) | `VerifierAndGoals.AtTheName.eps_the`, `Johnson/Goal/Conditions/RowsAtTheRecord.lean:179` |
| v, the verifier's typed queries | at most 2^20 | `VerifierAndGoals.AtTheName.count_the`, `Johnson/Goal/Conditions/RowsAtTheRecord.lean:136` |
| the allowance in T | 2^23 | `VerifierAndGoals.verifierQueryAllowance`, `Ladder/Bits.lean:91` |
| the factor in the error | 16 | `VerifierAndGoals.errorFactorPerQuery`, `Ladder/Bits.lean:85` |

Each value is a Lean definition or a theorem at the address; the figures in brackets (about …) are
arithmetic.

| rounds with proof of work | how many | bits |
|---|---|---|
| proof file, a request's own chains: closing a segment (25), two proximity tests (6 and 5) | 36 | 20 |
| proof file, the batch's shared chain: the read of the committed table (1), two proximity tests (9) | 10 | 28 |
| key file: the read of the committed table (1), four proximity tests (18) | 19 | 32 |
| copy's file: the read of both tables (1), a proximity test (5) | 6 | 32 |

The three numbers are the parameter file's line "work positions 20 28 32": for a request, for a
batch, once for a commitment; the scope fixes the line (`Ladder/Stored.lean`), and one of step 13's
tests holds the proof file's whole list of rounds, these numbers among them, against the list
written in Lean. No other round has work, the OOD rounds included. The counts in this second table
are taken off the lists of rounds written in Lean; no Lean theorem states them. Without the
work these rounds' errors are about 2^-96 to 2^-110; the folding rounds, none with work, lie between
2^-128.001 and 2^-129.16, but for fourteen later rounds of folds, seven in the shared chain and
seven in the key file, at 2^-148 to 2^-152: arithmetic on Lean's numerals, no Lean
theorem. These are single rounds' bits, not the chance of a forgery. That each round's count is at
most 2^-128 of its challenges, work counted, is what steps 8 to 15 prove. The rounds of the other
sub-protocols (sum-checks, lookups, the random matrix) use no bound on codes; their counts stand
inside the kinds' lemmas (those of the attention rounds also in the test named at the top).

## Words in the Lean files

The comments use these words: "entry file" for the copy's file, "record" for an OOD sample (under
`Johnson/Desc/` mostly the verifier's state), "live test" for the tests on the public files and
"entry tests" for fourteen of them, "law" for a lemma, "head" for the standing hypotheses, "link"
for a segment (the stretch of the first chain for one part of the model; `HolographicProtocol.link`
is another thing), "description" for the IOP ([GLOSSARY.md](GLOSSARY.md), [TERMS.md](TERMS.md)).
Where a comment and Lean's printed statement differ, the statement counts (THEOREM.md).
