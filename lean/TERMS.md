# Terms: the definition's names, Lean's names, and the words in use

FlashProve is meant to let a provider show that a list of output tokens is what one fixed language
model returns on a prompt, without showing the model. Each of its proofs is about one *instance*
(here: a prompt with its output tokens) and claims that this instance lies in the language of an
*index* (here: the model's weights). The verifier is handed no index, only a short key that was made
public for it once. The party that made that key, the index committer, is not trusted. Technically
one of its two hash functions is modelled as a random oracle (table 1, the row on the second hash
function), and FlashProve is a *commit-and-prove argument* whose relation has an index.

The names of its properties on this page (index-binding knowledge soundness, correctness of
extraction, index privacy) are those of the definition that this library follows, and so are the
names of the roles in table 1. From here on an index committer is called a committer, and an index
extractor an extractor. The commitment is the 256-bit value that has the role of the definition's
index verification key; it is narrower than that key (table 1). This page gives each term, the Lean
name that states it, the word that the pages and comments of this library use for it, and, for the
properties of table 2, how each stands at the Lean verifier's system. The tables' third columns give
the other words in use for a term. The definition stands in Lean, in general form, in
`lean/ZKCP/Defs.lean` and `lean/ZKCP/Optional.lean`. These two files follow further work of the
researchers that this protocol builds on (`lean/CREDITS.md`, "Further work that this protocol builds
on"). That work is not public, so a reader cannot hold the files against it; table 5 lists the
paper's own definitions of these notions. That the two files render that work faithfully rests on a
comparison by reading, not on a theorem. For index privacy the first of them has two forms, and the
one whose Lean name is `HasIndexPrivacy` asks less than the definition (note 9). Paths on this page
are from the repository's top. An L with a number (L93) is a labelled entry of
[LIMITS.md](LIMITS.md), not a line; a number behind `lean/GAPS.md` is the number of a gap there.
Lean does not check this page. The paper is the one in the repository's paper folder.

Short names on this page: `verify` is `VerifierAndGoals.verify`.

P5J, LPFD, H2K12, Loose, Face, AtFullSide, T1 and their like in names and paths are working labels
of parts of the library; they say little or nothing of the content ([GLOSSARY.md](GLOSSARY.md)).

Programs, not Lean names: `cp_verify`, `cp_commit`, `lean-verify`. No Lean name either:
`verify-on-bytes`, the name of a Lean text (below).

## What is proved, in these terms

- Six theorems about one argument system, `compile (flashProve setup)`, for every public setup:
  `VerifiableInference.sound`, `VerifiableInference.soundAndBinding`,
  `VerifiableInference.completeOnCanServe`, `VerifiableInference.zeroKnowledgeOnCanServe`,
  `VerifiableInference.refusedHandsOutNoProof` and `VerifiableInference.repliesFit`
  (`lean/AtFullSide/Face/TheSixLines.lean`): soundness; soundness with binding; completeness and
  zero knowledge, at the requests that can be served; the reply at a refused request; the replies
  fit. Their terms: table 6, the row on the six lines; what each says, with all that goes with it:
  [LIMITS.md](LIMITS.md), L93; each beside its Lean text: [STATEMENTS.html](STATEMENTS.html).
- The soundness theorem on `verify`, on which `sound` rests, what it assumes and what it does not
  say: [THEOREM.md](THEOREM.md).
- What is not proved: [LIMITS.md](LIMITS.md).
- Soundness, completeness and zero knowledge of the protocol and its honest provers written in Lean,
  before hashing, each statement with its bounds: [LIMITS.md](LIMITS.md), L88 to L92; their terms:
  table 6.
- The illustrative committers and Lean's results on index privacy, each with all that goes with it:
  [LIMITS.md](LIMITS.md), L61 to L66; single limits on the statements and the public files: L67 to
  L75.
- Each property and how it stands at the Lean verifier's system: table 2 and its notes.
- The statements that an auditor reads: [STATEMENTS.html](STATEMENTS.html); as plain text:
  [AUDIT.md](AUDIT.md).

## Which system

A term is one notion. It can be proved of one system and not of another. The pages speak of the
final system and of the Lean verifier's system above all, then of two IOPs and of one verifier, and
each has one name on all pages, but for the final system, which some pages call the compiled system.
The last column of table 2 is about the second of them.

| The term | Lean name, with file | The word that our pages use | What it is |
|---|---|---|---|
| **the final system** | `VerifiableInference.Compilation.finalSystem` (`lean/Johnson/Face/FinalStatement.lean`): the compiler `VerifiableInference.Compilation.compile` (`lean/Johnson/Face/Compiler.lean`) applied to `VerifiableInference.Compilation.flashProveAtFiles` (`lean/Johnson/Face/FinalStatement.lean`) at an honest part (table 6) | "compile flashProveAtFiles" · "compile (flashProve setup)" · "the compiled system" | The same IOP and the same verifier as the Lean verifier's system, with an honest committer and an honest prover that the compiler makes from the honest provers written in Lean. One system for each set of public files and settings. Its verifier reads no honest part: `VerifiableInference.Compilation.compile_flashProve_verify_eq` (`lean/Johnson/Face/FinalStatement.lean`) states that it is the verifier of the soundness theorem on `verify`. Its committer and prover are definitions, not programs. The statements on it: table 6. |
| **the Lean verifier's system** | `VerifierAndGoals.systemOfRecord` (`lean/Ladder.lean`) at `VerifierAndGoals.theDescription` (`lean/Johnson/Goal/Description/Description.lean`), taken at the second hash function (table 1's row on it): one system for each set of public files; its verifier: `VerifierAndGoals.verify` (`lean/Ladder.lean`) | "verify()'s system" · "the system of the theorem" | The argument that Lean compiles from the interactive oracle proof (IOP) as written in Lean: the protocol that the programs are written to run, as Lean describes it, following the default setting. The soundness theorem on `verify` is about it. Its honest side is a constant one: a committer that returns one constant and a prover that hands over empty files, whatever the weights; the final system has the same verifier, and honest ones written in Lean. That its IOP is the protocol that the programs run is not proved. |
| **the two IOPs** of `lean/Johnson/Flat/TwoSizes.lean` | the two sizes of `lean/Johnson/Flat/TwoSizes.lean`, at which the theorem on `innerCompiledVerifier` is told: `VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound` (`lean/Johnson/Top/InnerCompiledVerifier.lean`) | "the theorem on innerCompiledVerifier" | Two IOPs. The theorem on `innerCompiledVerifier` leads from 16 named hypotheses to soundness, and at these two IOPs, which are families and not closed inputs, four of the 16 are left in general, `VerifiableInference.OnPublicFiles.RemainingSoundnessConditionsFromDryRunAtFullSize` (`lean/Johnson/Flat/TwoSizes.lean`). At members where more is fixed, fewer are left, three and, at the full size, two: `VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtFullSize_withId`, `VerifiableInference.OnPublicFiles.soundThreeFull_ref_withId` (`lean/Johnson/Flat/CommitCodeSound.lean`). (These 16 are not the sixteen conditions of table 3.) It is not the soundness theorem on `verify`, which this page follows, and has no column in table 2. |
| **the compiled verifier** | `VerifiableInference.OnPublicFiles.innerCompiledVerifier` (`lean/Johnson/Top/InnerCompiledVerifier.lean`); with the test of scope, the parser and the two public readings around it: `VerifiableInference.Compilation.compiledVerifier` (`lean/Johnson/Face/Compiler.lean`) | "verify()" (under lean/OnBytes/ and lean/Ask/; elsewhere that word is the Lean verifier) | No system: the verifier that the library's compiler makes from an IOP written in Lean, whichever it is given. `verify` ends in it. |

One thing under lean/ is run as a command: the executable form of verify, run inside Lean by
tools/lean-verify (table 4). verify-on-bytes, the Lean text below OnBytes.Main, is a hand
translation of cp_verify into Lean, from which this repository builds no stand-alone program; one
test (tools/accepts/) compiles it and has Lean load the compiled code while it evaluates files of
lean/Ask/; it has conditional theorems only. Beside the Lean verifier's system there are
illustrative systems, of which three are named here: systems that keep the Lean verifier's verifier
and extractor and have an illustrative committer, which is tied to no program in this repository by
a theorem: `FlashProve.theWideDigits` (`lean/Johnson/Goal/Conditions/WideDigits.lean`),
`FlashProve.plainSystemAt` (`lean/Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean`) and
`Bind.Cpp.theCpp` (`lean/Johnson/Bind/Cpp/Defs.lean`) (the first two are compared with no program).
The third's committer stands on byte strings: it models one part of `cp_commit`. None has an honest
prover (table 3). The library has more: the made-up schemes of notes 9 and 10.

## Table 1: roles and objects

| The term | Lean name, with file | The word that our pages use | The same, or how it differs |
|---|---|---|---|
| **commit-and-prove argument**: an index committer, a prover and a verifier, all with access to the oracle | `ZKCP.Arg` (`lean/ZKCP/Defs.lean`); `VerifiableInference.ArgumentSystem` (`lean/VerifiableInference/Statements.lean`); from the second to the first: `VerifiableInference.ArgumentSystem.uploadArgument` (`lean/VerifiableInference/Agreement.lean`) | "argument system" · "proof system" · "scheme" | `ArgumentSystem` is narrower: oracle answers and keys have 256 bits, the committer samples its randomness first and then commits without further coins, and the verifier has no coins. |
| **indexed relation**: a set of triples of an index, an instance and a witness | `ZKCP.IndexedRelation` (`lean/ZKCP/Defs.lean`); `VerifiableInference.ArgumentSystem.uploadRelation` (`lean/VerifiableInference/Agreement.lean`) | "claim" | The same, with a witness type of one element. |
| **index** | `VerifiableInference.ArgumentSystem.Weights` (`lean/VerifiableInference/Statements.lean`); at the Lean verifier's system `VerifiableInference.ModelWeights` (`lean/VerifiableInference/ModelWeights.lean`) | "weights" · "model weights" | The same. The index set is every family of integer arrays that passes tests of size and range. All-zero matrices pass. The type takes the settings that are read off the public files, but by reading it holds the same arrays at all files that are read (no theorem says so). What moves with the files is the model, and so the language. |
| **instance** | the prompt and the output tokens among the arguments of `VerifiableInference.ArgumentSystem.verify` (`lean/VerifiableInference/Statements.lean`) | "request" · "prompt and output" · "prompt" · "output tokens" · "output" | The same. |
| **witness** | none | "witness" (the values of the model's run) · "trace" | `ArgumentSystem` has no witness. |
| **language of an index** | `ZKCP.IndexedRelation.L` (`lean/ZKCP/Defs.lean`); `VerifiableInference.ArgumentSystem.IsModelOutput` (`lean/VerifiableInference/Statements.lean`) | "true claim" · "the model's output" | Each output token is the integer model's greedy next token after the prompt and the earlier output tokens. The empty output and every prefix of the model's output are members. |
| **index verification key** | `VerifiableInference.Commitment` (`lean/VerifiableInference/Statements.lean`) | "commitment" · "commitment ID" · "key" · "verifier's key" | The same role, but narrower: in the definition the key is all that the committer publishes, and in the theorem it is these 256 bits alone. The key file is not part of it, although the programs keep it in a folder named ivk: see the row on the proof. The public files are not part of it either, and no theorem ties a commitment to one set of public files ([THEOREM.md](THEOREM.md)). The general step from a key to its digest: `ZKCP.Arg.digestKey` (`lean/ZKCP/DigestKey.lean`). |
| **index secret key** | the weights with the committer's randomness (`uploadArgument`) | "the prover's key" | The same. |
| **proof** (of one session) | `VerifiableInference.ArgumentSystem.Proof` (`lean/VerifiableInference/Statements.lean`); at `verify`: `FlashProve.FormBytes` (`lean/Johnson/Goal/Tie/DescriptionOnBytes.lean`), which the parser inside `verify` turns into a `VerifierAndGoals.TypedProof` (`lean/Ladder.lean`), made of further tokens and of `TypedOracleCompiler.Compile.Batch.Cms.KeyRoot`, `TypedOracleCompiler.Compile.Batch.Cms.OfflineLinkOnlineProof` (`lean/Johnson/TypedOracleCompiler/RecCompile/FrontRoot.lean`) | "key file" · "proof file" · "form" | Wider than the word suggests: what the key file, the copy's file with its link proof and the proof file hold are all parts of the proof. By its file's comment it is not the programs' three files as they ship but an outside parser's form of them: five parsed byte files with further tokens. The verifier rejects unless the oracle's answer at the code of the key that the proof brings is the 256-bit key that it holds: `ZKCP.verifyDigestKey` (`lean/ZKCP/DigestKey.lean`). |
| **public parameters of the index**: what the key and the proofs are allowed to give away about the index (its size, for example) | `ZKCP.IndexedRelation.pp` (`lean/ZKCP/Defs.lean`); `VerifiableInference.ArgumentSystem.publicParameters` (`lean/VerifiableInference/Statements.lean`); `VerifierAndGoals.Description.shown` (`lean/Ladder.lean`) | "what a proof may reveal" · "public parameters" (of the weights) | The same role. No statement bounds what it returns. At the Lean verifier's system it is a one-element type. The field is not the whole: the public files are fixed first, a simulator may depend on them, and part of them is fitted to the weights. What they tell of the weights no statement covers. |
| **random oracle** | `VerifiableInference.Hash`, `VerifiableInference.uniformHash` (`lean/VerifiableInference/RandomOracleModel.lean`); `ZKCP.U` (`lean/ZKCP/Defs.lean`) | "hash function" · "the format's hash function" | The same, with answers of 256 bits. |
| **trace** of an algorithm: its queries with their answers, in order | `VerifiableInference.QueryLog` (`lean/VerifiableInference/RandomOracleModel.lean`); `ZKCP.Trace` (`lean/ZKCP/Defs.lean`) | "query log" · "the committer's queries" | The same. |
| **index committer**, **prover**, **verifier** | `VerifiableInference.ArgumentSystem.sampleCommitmentRandomness`, `VerifiableInference.ArgumentSystem.commit`, `VerifiableInference.ArgumentSystem.prove`, `VerifiableInference.ArgumentSystem.verify` (`lean/VerifiableInference/Statements.lean`) | "committer" · "provider" · "key maker" (a committer that may cheat) · "honest side" (the honest committer and prover together) · "the Lean verifier" · "verify()" | The same. The prover keeps no state from one session to the next. In index binding the committer and the prover are any algorithms; the honest ones are read only by the properties that name them. |
| **index extractor** | in `Sound` a bound variable; the IOP's own: `VerifierAndGoals.Description.extractor` (`lean/Ladder.lean`), `FlashProve.theExtractor` (`lean/Johnson/Goal/Description/Extractor.lean`) | "extractor" | A function of the key and the committer's trace that returns an index or nothing. It sees no proof, so its answer is the same for every session. Here it also depends on the public files. It is a fixed rule defined with choice, not a program, and its running time is not bounded. There is no witness extractor. The statement of `sound_of_verify_at` says that there is an extractor and does not name it; the theorem for the second relation names the IOP's own (note 2). |
| **extracted index** | the value of that function | "the committed weights" (where the extractor's are meant) · "the weights under the commitment" | It need not be the weights that a committer used: that would be correctness of extraction (table 2). |
| **offline phase**, **online phase**, **session** | the three protocols of `VerifierAndGoals.Description.F` (`lean/Ladder.lean`): key file and copy's file offline, proof file online | "weight phase" | The same split. Because the key is 256 bits, `verify` is handed what the offline phase made, with the committer's one-time proof, inside every proof. |
| **number of sessions**; **environment**; **adversarial verifier**; **simulator**; **view** | the arguments proofCount and chooser of `VerifiableInference.realExperiment` (`lean/VerifiableInference/Statements.lean`); `VerifiableInference.MaliciousVerifier`, `VerifiableInference.Simulator`, `VerifiableInference.View` (`lean/VerifiableInference/Statements.lean`) | "number of proofs" · "chooser" · "malicious verifier" | The same, but for two things in `ZeroKnowledge`: the chooser, which sees the verifier's whole view as the definition's environment does, may also decline, which ends the run, and it has no coins of its own (note 9). |
| **interactive oracle proof (IOP)**, as written in Lean | `VerifierAndGoals.Description` (`lean/Ladder.lean`); `VerifierAndGoals.theDescription` (`lean/Johnson/Goal/Description/Description.lean`) | "description" · "the interactive level" | The protocol before it is compiled by Merkle trees and the Fiat–Shamir transformation. It has three IOPs, offline, link and online (table 6, the row on the protocol); on these pages "the IOP" is the three together. |
| **further encoding of the index**, kept in the secret key | the fields copy and link of `OfflineLinkOnlineProof` | "copy" · "the copy's file" · "link proof" · "further table" · "leaf table" · "entry file" · "leaf file" · "link" | One index under one key, encoded more than once, each further encoding with a link proof whose relation is: the further one decodes to the same index, or the first does not decode, or there is a collision (`lean/GAPS.md`, 34). It is not a relation with several indices. The verifier checks the link proof inside every proof, so the index binding of the soundness theorem on `verify` is stated of the whole proof, link included; it says nothing more of the link by itself. |
| **out-of-domain (OOD) sample** on a committed table: its OOD seed and its OOD answers | `Iop.HolographicProtocol.Rec` (`lean/Hiop/RecInterface.lean`); the field rcd of `KeyRoot` | "record" (the committer's answers to out-of-domain sampling) · "seed record" · "the record's seed" (the OOD seed alone) | In the programs' files the first of these words is the OOD answers alone. Lean's type is the pair of seed and answers. In many comments the same word is something else, most often the verifier's state: `lean/GLOSSARY.md`. |
| no term of the definition: **public files** | `VerifierAndGoals.PublicFiles` (`lean/Ladder/Stored.lean`); `VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles` (`lean/Ladder.lean`) | "parameter file" · "layout file" · "scale file" · "settings" | Parameters of the argument and of the relation. They are fixed before the oracle is sampled, although whoever commits writes the scale file. **In scope**: one proof format and one model size; only the scale file and eight numbers of the parameter file may vary. The library holds, as Lean terms, written copies of two sets of them, a full-size set that states exact match and the same set with a tolerant policy: `VerifierAndGoals.storedPublicFiles`, `VerifierAndGoals.zGap` (`lean/Ladder/Stored.lean`). These two sets are "the two stored sets of public files" of these pages, the first also "the stored full-size files", and the two Lean terms "the library's written copies" of them. No theorem ties the copies to files on disk. |
| no term of the definition: **default setting** | at full size `VerifierAndGoals.storedPublicFiles` (`lean/Ladder/Stored.lean`) | "the default configuration" (the paper's word, at full size) | The setting that the parameter file policy.txt has in the example configurations, at full size and at the small size: proof of work counts toward the target, and the policy is exact match. Two example configurations have a clipped-gap policy in its place. |
| no term of the definition: **exact match** | `Inst.Model.AcceptancePolicy.exact` (`lean/Inst/Model/ProgramR.lean`) | none | The policy in the parameter file that asks that every output token be the model's own: the three numbers 256, 256 and 0. It is a premise on the parameter file, not a test in the text of `verify`: files with other policies are in scope, and at one of them an honest proof was accepted (evaluated). So a user has to check the policy in the parameter file. |
| no term of the definition: **second hash function** | `OnBytes.secondHashFunction` (`lean/OnBytes/Hash/SecondHashFunction.lean`); `VerifierAndGoals.atSecondHashFunction` (`lean/Ladder.lean`) | "the format's second hash function" | The format has two hash functions, both built on BLAKE2b's compression function. Only one of them is modelled as random: it is the oracle of the statement. This is the other: a second, fixed hash function that is part of the argument. That it may be treated as separate from the sampled one is an assumption of the model, not a hypothesis of the theorem. In some names (`extractor_atOlder`, `bindsWith_atOlder`) the word Older means this function; no age is meant. |

**Words that differ between the pages under lean/ and the other pages.** The pages under docs/ and
the guides have words of their own for some things of table 1. Each row is one thing, but for the
row on sessions.

| Under lean/ | Outside lean/ | What it is |
|---|---|---|
| **first table** | "anchor" | The first committed table of the weights. The key file holds its root. |
| **copy** | "leaf table" | A further committed table of the same weights, with masks of its own, against which requests are proved. |
| **the copy's file** | "leaf file" | A file of the programs with a stored copy's root and the link proof that ties the copy to the first table. |
| **session** | "batch" | Not one thing. A session in Lean is one request. A batch of the programs holds up to 64 requests. No theorem ties a count of the one to a count of the other. |
| **OOD answers** | the same words; in the programs, their files and what they print: "record" | The published masked sums of the weights (table 1, the row on the OOD sample). |
| **the executable form** of `verify` | the same words | See table 3. |
| **the final system** | "the compiled system" (on some pages under lean/ too) | `VerifiableInference.Compilation.finalSystem`: the same verifier, `verify`, with the honest committer and prover that the compiler yields. |
| **the label of a reply** | "label" | What a reply shows beside its proof where a service chooses to say "failed": served, failed or other tokens (table 6). |

## Table 2: properties, at a glance

The last column is about the Lean verifier's system, whose honest side is constant, not about the
system of the six theorems, `compile (flashProve setup)`: of that one completeness and zero
knowledge are proved, at the requests that can be served (table 6; [LIMITS.md](LIMITS.md), L93). The
notes under the table tell each row: the definition, how Lean's statement differs, the theorems by
name and their limits. A cell of the last column is never quoted without its note. "**nothing** of
this system" means that no statement of the row is proved of the Lean verifier's system. Where this
page says that no theorem states something, or that no file names something, that rests on searches
of the files' text. A statement can be typed at the constant honest side too. It then speaks of a
committer that returns one constant and of a prover that hands over empty files. "No content" means
that.

| The term | Lean name, with file | The word that our pages use | The same, or how it differs | Of the Lean verifier's system |
|---|---|---|---|---|
| **index-binding knowledge soundness**; short: index binding; after the first use on a page: soundness (note 1) | `ZKCP.HasIndexBinding` (`lean/ZKCP/Defs.lean`); `VerifiableInference.Sound` (`lean/VerifiableInference/Statements.lean`) | "soundness" · "binding for the language" · "binding" (of index binding itself, as in binding at the key) | the same, by a theorem, without a witness and at a summed budget | **proved**, at exact match, in a restricted form |
| **index binding for a second relation** (note 2) | `VerifiableInference.SoundForWith`, `VerifiableInference.SoundFor` (`lean/VerifiableInference/MoreStatements.lean`); `Policy.MeetsPolicy` (`lean/Policy/Front/MeetsPolicy.lean`) | "the theorem under a policy" · "soundness under the policy" | the text of `Sound` with another claim (the output meets the files' policy); a theorem leads each way between it and the definition's form with the extractor named, and none states the two as one equivalence | **proved**; by itself it bars nothing against some committers |
| **session-augmented index binding** (note 3) | `ZKCP.HasSessionAugmentedBinding` (`lean/ZKCP/Optional.lean`); `VerifiableInference.SoundManyProofs` (`lean/VerifiableInference/MoreStatements.lean`) | "soundness for several proofs" | the same idea | **proved**, at exact match, by a union bound: N times the error, at the whole list's queries; without the factor N: open |
| **no two answers** (note 3) | `ZKCP.NoTwoAnswers` (`lean/ZKCP/TwoIndices.lean`) | none | this library's own notion, no part of the definition; it follows from session-augmented index binding | **proved**, at exact match, for one list: N times the error, at the whole list's queries |
| **correctness of extraction** (note 4) | `ZKCP.HasExtractionError` (`lean/ZKCP/Optional.lean`); `VerifiableInference.ExtractsCommittedWeights` (`lean/VerifiableInference/MoreStatements.lean`) | "binding" (that the extracted weights are the honest committer's own) · "extraction error" · "the extractor returns these weights" | an optional addition; the experiment is this library's | **no content**; at two illustrative systems a form at each fixed choice of coins; at a third the statement itself, on average over sampled coins |
| **soundness after an honest commitment** (note 4) | `VerifiableInference.SoundAfterHonestCommitment`, `VerifiableInference.SoundAfterHonestCommitmentFor` (`lean/VerifiableInference/MoreStatements.lean`) | none | outside the definitions, which have no name for it: what index binding and correctness of extraction at one extractor give together; no extractor is in it | **no content**; proved of one illustrative system (vacuously where a test on the public files fails) |
| **extractability of the commitment**; on our pages **binding of the commitment**, in the opening form, and after the first use on a page **opening-form binding** (note 5) | `VerifiableInference.BindsWith` (`lean/VerifiableInference/MoreStatements.lean`); the second clause of `VerifiableInference.SoundAndBinding` (`lean/VerifiableInference/Statements.lean`); `VerifierAndGoals.G9bits` (`lean/Ladder/Bits.lean`), and the coarser `VerifierAndGoals.G9` (`lean/Ladder.lean`: an error of at most one quarter for up to 2^64 queries, no security level) | "binding" (that nobody opens a commitment to other weights than the extracted ones) · "the commitment binds to the weights" | outside the definitions; it gives correctness of extraction (note 5) | **no content**; proved of three illustrative systems |
| **no two openings** (note 6) | `VerifiableInference.NoTwoOpenings` (`lean/VerifiableInference/MoreStatements.lean`) | "binding" (of the committer, taken as a commitment scheme) | outside the definitions; the classical binding property | **no content**; proved of two illustrative systems, `plainSystemAt` and `theCpp` (note 5) |
| **soundness for an opened commitment** (note 7) | `VerifiableInference.SoundOpened` (`lean/VerifiableInference/Statements.lean`) | "binding" (where the two statements that read openings are named together) | outside the definitions; it names no extractor | **no content**; proved of one illustrative system |
| **completeness** (note 8) | `ZKCP.HasCompletenessError` (`lean/ZKCP/Defs.lean`); `VerifiableInference.Complete` (`lean/VerifiableInference/Statements.lean`); on a set of requests: `VerifiableInference.CompleteOn` (`lean/VerifiableInference/Steps.lean`); at well-formed requests whose result is their claimed output: `VerifiableInference.AtEveryRequest.ProofAcceptedWhere` (`lean/VerifiableInference/AtEveryRequest.lean`) | "acceptance" (that honest proofs are accepted; the acceptance policy is another thing) | the same, by a theorem; the gap lies in the relation | **no content**: its honest prover is a constant one, the same at all weights; of the final system: note 8 |
| **index privacy against an environment that sees only the earlier instances and proofs** (note 9) | `ZKCP.HasIndexPrivacy` (`lean/ZKCP/Defs.lean`) | "the literal form" · "the first form" | weaker than the definition, in spite of its Lean name, by a comparison by reading: its environment sees the earlier instances and proofs and nothing else of the verifier's view | **nothing** of this system; beside it: note 9 |
| **index privacy**; plain gloss: weight hiding (note 9) | `ZKCP.HasStrongIndexPrivacyWith` (`lean/ZKCP/Defs.lean`); on a range of indices `ZKCP.StrongPrivacyOn` (`lean/ZKCP/OnRange.lean`) | "hiding" · "weight hiding" · "zero knowledge" · "index privacy with a stronger environment" · "the stronger form" | the definition's form at a named simulator, by a comparison by reading, but for two things: its environment may also decline, and has no coins of its own; "stronger" is said against the row above, and the converse fails | **nothing** of this system; beside it: note 9 |
| **a form of index privacy with a narrower key** (note 9) | `VerifiableInference.ZeroKnowledge` (`lean/VerifiableInference/Statements.lean`) | "zero knowledge" (where Lean's statement of that name is meant) · "a form of index privacy with a stronger environment and a narrower key" · "a stronger form of index privacy" | the row above at fixed types, where the key is the 256-bit commitment | **nothing** of this system; beside it: note 9 |
| **the same form for a smaller relation** (note 9) | `VerifiableInference.ZeroKnowledgeOn` (`lean/VerifiableInference/MoreStatements.lean`) | "only for requests that can get a proof" | a choice of relation; whether a request is in it is not hidden | **nothing** of this system; of the final system: note 9 |
| **index privacy for batches** (note 9) | `ZKCP.Gen.HasIndexPrivacyWith` (`lean/ZKCP/Gen.lean`); on a range of indices `ZKCP.Gen.PrivacyOn` (`lean/ZKCP/OnRange.lean`) | "hiding for batches" | the environment of the row "index privacy", with batches; not the first row's form, in spite of its Lean name; the definition that this library follows has no batches | **nothing** of this system; beside it: note 9 |
| **doubly zero-knowledge commit-and-prove argument**: the three together (note 10) | `ZKCP.IsZKCPArg` (`lean/ZKCP/Defs.lean`); `VerifiableInference.CompleteSoundZeroKnowledge` (`lean/VerifiableInference/Statements.lean`) | "the three together" · "the top statements" | the same three, but for the third: in `IsZKCPArg` it is the form of the first row on index privacy, which is weaker than the definition; in `CompleteSoundZeroKnowledge` it is `ZeroKnowledge` | **one of the three**, in a restricted form |
| **the same statements without the empty output** | `VerifiableInference.SoundNonEmpty`, `VerifiableInference.CompleteNonEmpty`, `VerifiableInference.ZeroKnowledgeNonEmpty` (`lean/VerifiableInference/StatementsNonEmpty.lean`), and their kin in that file | none | the same notions for the relation without the empty output; those on soundness ask more, those on the honest side ask less, and neither bundle of all of them gives the other | soundness in this form follows at exact match by a general theorem (note 2), not stated by name; the others are proved of no named system |
| **well-formedness of the extracted index**: an optional addition, a single proof, made once for a key, that the index behind it is of an admissible kind | none | none | **not defined in this library**, by the opening comment of `lean/ZKCP/Defs.lean`. Without it index binding does not say which indices of the set are reasonable ones | not stated at all |

### Notes to table 2

**Note 1: index-binding knowledge soundness.**

*The definition.* One fixed rule, the index extractor, reads nothing but the index verification key
and the hash queries of whoever made that key, with their answers, and names an index or none: so
the index is settled before any proof is made. Whatever a committer with at most t_C queries and a
prover with at most t_P queries do, the verifier accepts an instance that lies outside the named
index's language with probability at most an error that may depend on t_C and on t_P; where no index
is named, every accepted instance counts. Where a relation has witnesses, a second rule, which also
reads the instance, the proof and the prover's queries, must name a witness that fits the instance
at the named index, and a failure of either kind counts toward the same error. The experiment has
one session.

*How Lean's statement differs.* `Sound` is the same, by a theorem for every argument system, at an
error that reads the sum of the two query budgets; it has no witness part, since the relation has no
witness: `VerifiableInference.sound_iff` (`lean/VerifiableInference/Agreement.lean`). Where the
extractor may be any function, the definition's clause on the witness adds nothing, whatever the
relation: `ZKCP.indexBinding_iff_sound` (`lean/ZKCP/Basic.lean`). So a form in which the witness is
read off the proof and the prover's queries would ask more than the definition does.

*Of the Lean verifier's system.* `Sound` is proved, `sound_of_verify_at`, and index-binding
knowledge soundness is stated of `verify` too, by `sound_iff`:
`VerifierAndGoals.AtTheName.indexBinding_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`); with the extractor named, the IOP's own:
`VerifierAndGoals.AtTheName.indexBindingWith_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`). There is one system, and so one extractor,
for each set of public files. The word "knowledge" belongs to the name: nothing is extracted from a
prover, and the name does not mean that a prover knew the weights or ran the model. The restricted
form, in six points (no witness; one budget for both parties, 124 bits a query; public files fixed
in advance; exact match; files in scope; the second hash function): [THEOREM.md](THEOREM.md);
`lean/GAPS.md`, 28. For every proof parser, at an error that grows with the parser's queries:
`VerifierAndGoals.AtTheName.sound_of_verify_parsers_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyMore.lean`).

**Note 2: index binding for a second relation.** `SoundForWith` is the text of `Sound` with the
claim as a parameter and the extractor as an argument; `Sound` is its case at the claim that the
output is the model's: `VerifiableInference.sound_iff_soundFor`
(`lean/VerifiableInference/MoreStatements.lean`), by unfolding the two definitions. It says as much
as the claim says.

*Of the Lean verifier's system.* `SoundForWith` of the same verifier, over the same set of possible
weights, for another relation: the output meets the policy that the public files state. It is proved
at all files in scope, with the extractor named, for every proof parser, at an error that grows with
the parser's queries: `VerifierAndGoals.AtTheName.soundUnderPolicy_of_verify_at`,
`VerifierAndGoals.AtTheName.soundUnderPolicyAt_of_verify`,
`VerifierAndGoals.AtTheName.g8bits_of_verify`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean`). It is index binding for that relation, with
the extractor named, the IOP's own:
`VerifierAndGoals.AtTheName.indexBindingUnderPolicy_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`), which states `ZKCP.HasIndexBindingWith`
(`lean/ZKCP/Defs.lean`). It is not `HasIndexBinding` of the model's own relation. At the policies in
scope the relation is the larger of the two but for the empty output, which is the model's on every
prompt and meets no policy: so at exact match this theorem bars an accepted empty output, and
`Sound` does not: `VerifierAndGoals.soundNonEmpty_of_soundUnderPolicyAt`
(`lean/Ladder/NonEmptyTies.lean`). By itself the theorem bars nothing against a committer who
commits to weights under which every output meets the policy, and it speaks of the weights that its
extractor reads off the commitment and the committer's hash queries, at the given public files,
whoever made it. So it means something only together with correctness of extraction at the same
extractor, which has no content at the Lean verifier's system, and with knowing who made the
commitment, which no theorem says. The theorem does not show that `verify` accepts what the policy
allows: that is the goal `VerifierAndGoals.G3'pol` (`lean/Ladder.lean`), a statement typed there for
any IOP, which is not proved. The policy is not the test of the public paper on Token-DiFR.

**Note 3: many sessions.**

*The definition.* Here the error covers many sessions under one key at once. The cheating prover,
held to t_P hash queries in total, hands in a list of at most N instances with proofs, and it wins
if any accepted entry is outside the language of the single index that is extracted for that key.

*How Lean's statement differs.* `SoundManyProofs` has that shape: one extractor, one index for the
whole list, one budget for the list, which is sent at once. It checks the first N entries of a list
of any length, where `HasSessionAugmentedBinding` counts only lists of at most N. One theorem leads
from the first to the second, `VerifiableInference.sessionAugmented_of_soundManyProofs`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`); none leads back.

*Of the Lean verifier's system.* Proved at exact match, in both forms, by a union bound: N times the
error of one proof, taken at the queries for the whole list, for a list of proofs that is sent at
once: `VerifierAndGoals.AtTheName.soundManyProofs_union_of_verify_at`,
`VerifierAndGoals.AtTheName.sessionAugmented_union_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`). The prover sees no decision of the verifier
before it hands the list in, and it sees no honest proof. A form without the factor N is open: the
lemmas that would give it, `VerifiableInference.Sound.manyProofs`
(`lean/VerifiableInference/ManyProofs.lean`) and the like lemma in `lean/ZKCP/ManyOfOne.lean`, need
a bound on the verifier's own hash queries, which no theorem gives of `verify`.

*No two answers.* Under one commitment and one set of public files that state exact match, no prover
gets two different outputs of the same length accepted for one prompt, except with probability at
most N times the error of the soundness theorem on `verify`, for a list of N proofs handed in at
once, the error taken at the query budget of the whole list. It follows from index-binding knowledge
soundness: `VerifierAndGoals.AtTheName.noTwoAnswers_of_verify_at`
(`lean/Johnson/Goal/Skeleton/NoTwoAnswersOfVerify.lean`), `ZKCP.noTwoAnswers_of`
(`lean/ZKCP/TwoIndices.lean`). It does not say that an accepted output is the output of the weights
that an honest committer put in, and it says nothing under a tolerant policy, on two proofs under
two commitments or at two sets of public files, or on outputs of different lengths. It is not "no
two openings" (note 6).

**Note 4: correctness of extraction.**

*The definition.* When the committer is the honest one, the index that the extractor names is the
very index that was committed. It is an optional addition to the primitive and no part of index
binding.

*How Lean's statement differs.* `ExtractsCommittedWeights` follows from the library's general form,
`HasExtractionError`: `VerifiableInference.extracts_of_extractionError`
(`lean/VerifiableInference/AgreementWith.lean`). The experiment and the error are this library's
own. It means something only at an extractor for which soundness is proved by name (notes 1 and 2).
What the two give together has no extractor in it: after an honest commitment no false output is
accepted at the committed weights, up to the sum of the two errors and on average over honest
commitments, `VerifiableInference.SoundAfterHonestCommitment`
(`lean/VerifiableInference/MoreStatements.lean`), by
`VerifiableInference.SoundForWith.soundAfterHonestCommitmentFor`
(`lean/VerifiableInference/AgreementWith.lean`). The definition has no name for that.

*Of the Lean verifier's system.* It has no content there: the committer is one constant, and the
statement is false of it at every error below 1 (by reading, not machine-checked).

At two illustrative committers a form at each fixed choice of the committer's coins is proved, for
the extractor of `verify` itself: `FlashProve.extracts_atOlder`, `FlashProve.extractor_atOlder`
(`lean/Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean`), `FlashProve.extracts_own_digits`,
`FlashProve.extractor_theWide` (`lean/Johnson/Goal/Conditions/BindsOwn.lean`),
`VerifierAndGoals.AtTheName.same_extractor_wide` (`lean/Johnson/Goal/SameExtractorWide.lean`). Coins
fixed before the hash function is sampled have, as the first 256 bits of a leaf's salt, the public
files' digest that the format asks there (itself an answer of the hash function) with probability at
most 2^-256, so but for that chance these two theorems speak of trees whose leaves are hashed as
strings outside the format, not of a commitment that the programs could write (by reading, no
theorem; `lean/GAPS.md`, 64). Where the tests on the public files fail, both speak of a committer
over empty data.

At the third such system, `ExtractsCommittedWeights` itself, on average over sampled coins, is
proved, at files in scope where the tests on the public files pass, or at files that are read and
whose plan has salts of 40 bytes: `Bind.Cpp.extractsCommitted`, `Bind.Cpp.extractsCommitted_salt`
(`lean/Johnson/Bind/Cpp/TheTie.lean`). There soundness after an honest commitment is proved too, at
all files in scope, for the claim that the output meets the files' policy, and at exact match for
the claim that the output is not empty and is the model's: `Bind.Cpp.soundAtCommitted`,
`Bind.Cpp.soundAtCommitted_own` (`lean/Johnson/Bind/Cpp/SoundAtCommitted.lean`),
`Bind.Cpp.soundAtCommitted_exact_nonempty` (`lean/Johnson/Bind/Cpp/SoundAtCommittedExact.lean`) (all
that goes with these theorems: `lean/LIMITS.md`, L61).

No theorem says that `verify` accepts anything under an illustrative committer's commitment. Of
`cp_commit` nothing is proved.

**Note 5: extractability of the commitment; on our pages binding of the commitment, in the opening
form.**

*What it says.* Whoever opens a commitment, by naming weights and coins from which the honest
committer computes it again, names the extracted weights. The commitment may be a cheating
committer's.

*How it stands to the definition.* It is no term of the definition, and not index binding of the
argument whose verifier is `verify`. For a system made from a scheme it follows from index binding
of a second argument with the same committer and the same extractor:
`ZKCP.opensToExtracted_of_binding` (`lean/ZKCP/WithOpenings.lean`),
`VerifiableInference.bindsWith_ofArgument` (`lean/VerifiableInference/OfArgumentBinds.lean`). It
gives correctness of extraction: at each fixed choice of coins,
`VerifiableInference.BindsWith.atRandomness` (`lean/VerifiableInference/BindsAtRandomness.lean`),
and on average over sampled coins, at the error read at a bound on the honest committer's hash
queries, where the system's sampler draws one number and asks the hash function nothing,
`VerifiableInference.BindsWith.extractsDrawn` (`lean/Johnson/Bind/ExtractsDrawn.lean`).
`SoundAndBinding` is index binding and this property at one extractor:
`VerifiableInference.soundAndBinding_iff` (`lean/VerifiableInference/Binds.lean`). Nothing in
`SoundAndBinding` ties the committer to the verifier, so its second clause means something only
beside completeness (an argument on paper). This is what Binding means in that name and Binds in
`BindsWith`. In `HasIndexBinding` the same word means index binding.

*Of the Lean verifier's system.* This property, no two openings (note 6) and soundness for an opened
commitment (note 7) all read the honest committer, so none has content there; of its constant
committer the first two are false at every error below 1 (by reading, not machine-checked, from
`VerifiableInference.BindsWith.one_le_of_blind`, `VerifiableInference.NoTwoOpenings.one_le_of_blind`
(`lean/Johnson/Top/FrontBinds.lean`)). They are proved of illustrative systems, which have the same
verifier and extractor.

At `theWideDigits`: `SoundAndBinding` and `SoundOpened` at exact match,
`VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_verify_at`,
`VerifierAndGoals.AtTheName.soundOpened_level_digits_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyMore.lean`), and the two goals, `FlashProve.G9_digits`,
`FlashProve.G9bits_digits` (`lean/Johnson/Goal/Conditions/WideDigits.lean`). Where the tests on the
public files fail, the first two hold because `verify` rejects everything, and the two goals speak
of a committer over empty data. Of a kin of that illustrative system, whose randomness is the
committer's coins themselves, so that an opener may pick any coins, this property and no two
openings are proved at files in scope (`lean/Johnson/Goal/Conditions/BindsAtCoins.lean`).

At `plainSystemAt`: this property and no two openings, from the one premise that the public files
are read, `FlashProve.bindsWith_atOlder`, `FlashProve.noTwoOpenings_atOlder`
(`lean/Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean`); where the tests on the public files
fail, these two speak of a committer over empty data.

At `theCpp`: this property, `Bind.Cpp.bindsAt` (`lean/Johnson/Bind/Cpp/TheTie.lean`), at files in
scope where the tests on the public files pass; this property and no two openings,
`Bind.Cpp.bindsAt_salt`, `Bind.Cpp.noTwoOpenings_salt` (`lean/Johnson/Bind/Cpp/TheTie.lean`), at
files that are read and whose plan has salts of 40 bytes; no two openings also at files in scope
where the tests on the public files pass, `Bind.Cpp.noTwoOpenings_live`
(`lean/Johnson/Bind/Cpp/NoTwoOpeningsAtLive.lean`), at twice the error of `bindsAt`; not the goal
`G9bits`: it does not reach all files in scope that are read.

Of the final system `SoundAndBinding` is one of the six theorems (table 6). Of `cp_commit` nothing
is proved.

**Note 6: no two openings.** Nobody opens one commitment to two different sets of weights. No
extractor and no verifier occur: it is the binding of the committer taken as a commitment scheme by
itself. It is no term of the definition, in which the commitment is part of the scheme. It follows
from opening-form binding at twice the error: `VerifiableInference.BindsWith.noTwoOpenings`
(`lean/VerifiableInference/NoTwoOpenings.lean`). Of what it is proved: note 5.

**Note 7: soundness for an opened commitment.** Soundness at weights that the adversary opens
itself; no extractor occurs. It is no term of the definition. It follows from `SoundAndBinding` at
twice the error and is strictly weaker: `VerifiableInference.soundOpened_of_soundAndBinding`
(`lean/VerifiableInference/Checks.lean`). Of what it is proved: note 5.

**Note 8: completeness.**

*The definition.* The completeness error bounds how often an honest run fails: the probability, over
the oracle and both parties' coins, that the verifier rejects a proof which the honest prover made
under a key from the honest committer, taken at the worst triple of index, instance and witness in
the relation. `Complete` is that definition, without a witness: `VerifiableInference.complete_iff`
(`lean/VerifiableInference/Agreement.lean`).

*Where the gap lies.* In the relation, not in the name. The statement speaks of every request in the
relation, and for some no proof is to be had: the empty output, which meets no policy, is one, and
no theorem says whether it is the only one. The goal on soundness under the policy,
`VerifierAndGoals.G8` (`lean/Ladder.lean`), counts an accepted empty output as a forgery, so of a
system that meets it `Complete` holds at no small error (by reading, not machine-checked;
`lean/GAPS.md`, 39). `CompleteOn` restricts the statement to a set of requests, here those that can
be served, `VerifiableInference.CanServe` (`lean/VerifiableInference/CanServe.lean`), and that set
depends on the weights: at some valid weights it is empty, and all weights that a theorem shows by
name to meet it are made up (`lean/LIMITS.md`, L27). `CompleteOn` at an empty set of requests is
true of every system: what counts is the set at which it is proved.
`VerifiableInference.completeOn_of_completenessError`
(`lean/VerifiableInference/AgreementWith.lean`) leads to it from the general form.

*Of the Lean verifier's system.* It has no content: the honest prover of that system is a constant
one, the same at all weights. The honest provers written in Lean stand in the final system, and
completeness is stated of them in two forms: as an IOP, on the served requests, and of the final
system, at the requests that can be served and whose output is the model's (`completeOnCanServe`;
the same requests as the well-formed ones whose model result is their claimed output) (table 6).
Further statements cover no request that the second of these does not already cover: they are about
weights that pass the first worst-case check, or the least-bound check with numbers that hold (the
library's own checks; neither is `cp_commit`'s worst-case check), at which the model has a result on
every well-formed request (table 6). What is proved of these statements, and within which bounds:
`lean/LIMITS.md`, L88 to L93. Runs of `verify` on proof files are evaluations:
[THEOREM.md](THEOREM.md). As for any notion of soundness, a verifier that rejects everything is
sound too: `VerifiableInference.rejectAll_sound` (`lean/VerifiableInference/Checks.lean`).

**Note 9: index privacy, in five rows.**

*The definition.* Index privacy compares two runs that a cheating verifier, limited to t_V hash
queries, should not be able to tell apart. In the real run the honest committer makes the key and
the honest prover serves up to N requests. In the other run a single simulator, fixed in advance and
told nothing but the index's public parameters and N, makes the key, answers every hash query of the
verifier itself (the same answer each time a query repeats), and makes each proof from the request's
instance, never from a witness or the index. The error bounds the statistical distance between the
verifier's views of the two runs, and it may grow with t_V and with N. It must hold for every index,
every such verifier, and every rule, the environment, that picks each request, with a witness that
fits at the index; the rule may toss coins. At each request the environment is handed the index and
all that the verifier has seen up to then: the key, the earlier requests with their proofs, the
verifier's hash queries with the answers, and the verifier's own random choices. One key serves
every request, and that is why N appears in the error.

- **Against an environment that sees only the earlier instances and proofs**, `HasIndexPrivacy`. It
  is weaker than the definition, in spite of its Lean name. Whoever picks the instances is given the
  index and the earlier instances with their proofs, and nothing else of the verifier's view: none
  of its hash queries. How little that can be, a made-up scheme shows: its prover puts the secret
  index into the proof when the instance equals one hash value, which anybody can compute with one
  query. An environment of this kind cannot query, so it hits that instance with probability at most
  N/2^λ, and the scheme meets this form: `ZKCP.Separation.leaky_isZKCPArg`
  (`lean/ZKCP/Separation.lean`).
- **Index privacy**, `HasStrongIndexPrivacyWith`: whoever picks the instances is handed the
  adversarial verifier's whole view so far, as in the definition. By a comparison by reading it is
  the definition's form, at a named simulator, but for two things. The environment may decline,
  which ends the run: that asks more. And the environment is a function without coins of its own,
  where the definition's may toss coins: by its type it covers fewer environments, and no theorem of
  the library carries this form over to the others. Where a page says "stronger", that is said
  against the first form. It implies the first form. The converse fails, by the same made-up scheme:
  `ZKCP.Separation.leaky_not_strong` (`lean/ZKCP/Separation.lean`).
- **`ZeroKnowledge`.** In the library's `ZeroKnowledge` whoever picks the instances sees all that
  the adversarial verifier has seen, as the definition's environment does. Beyond the definition
  that party may decline, which ends the run. It is a function with no coins of its own, where the
  definition's environment may toss coins. `ZeroKnowledge` implies `HasIndexPrivacy` (a theorem:
  `indexPrivacy_of_zeroKnowledge`), which is weaker than the definition in spite of its Lean name;
  for the general forms the converse fails (a made-up scheme: `lean/ZKCP/Separation.lean`).
  `ZeroKnowledge` is narrower than the definition in its key: that is the 256-bit commitment, so
  whatever else a committer publishes is covered only inside a proof. `ZeroKnowledge` is proved of
  no system; `ZeroKnowledgeOn` of the final system alone, on the requests that can be served, at
  public files in use (`lean/LIMITS.md`, L18). The ties: `VerifiableInference.zeroKnowledge_iff`,
  `VerifiableInference.indexPrivacy_of_zeroKnowledge`
  (`lean/VerifiableInference/AgreementZeroKnowledge.lean`).
- **For a smaller relation**, `ZeroKnowledgeOn`: the same form for the relation that a named
  condition holds and the output is the model's. That is a choice of relation, not a weaker notion;
  whether a request meets the condition is then not hidden, and the condition may depend on the
  weights.
- **For batches**, `ZKCP.Gen.HasIndexPrivacyWith`: the same environment, with batches of instances,
  typed oracles and two relations. It is stated in this library; the definition that this library
  follows has no batches.

*Further limits of the statements.* The computational form is not defined in this library. Without a
witness, the privacy is that of the index alone. What the public files tell of the weights no
statement covers. No theorem on hiding is about a program.

*Of the Lean verifier's system.* That system's honest side is a constant one: a committer that
returns one constant and a prover that hands over empty files, whatever the weights. Index privacy
can be stated of it in Lean, but the statement would be about these two, and not about the committer
and the provers of the six lines. One goal is typed for every IOP and proved of none, in the form of
`ZeroKnowledge`: `VerifierAndGoals.PackageZeroKnowledge` (`lean/Ladder/Package.lean`). Of the honest
provers written in Lean zero knowledge is stated in two forms: honest-verifier, as an IOP before
hashing, and of the final system: on the requests that can be served (`zeroKnowledgeOnCanServe`, one
of the six theorems); as its corollary at every request, with the simulator told one bit for each
request, served or refused; and, at every well-formed request, with each request's label shown and
told (table 6). What is proved of these statements, and within which bounds: `lean/LIMITS.md`, L88
to L93.

*What Lean states on hiding.* Each statement below is of its own object. The committed tables: table
3, the row on independence of the index. The link proof: table 3, the row on honest-verifier zero
knowledge.

A conditional theorem, `OnBytes.WholeKey.wholeKeyPrivacy` (`lean/Johnson/WholeKey/Main.lean`): if 20
conditions hold for an IOP's honest provers and their simulators, the hashed argument made from
them, with its whole key published once, has index privacy, over typed random oracles, one instance
a proof, on a stated range of indices, up to a written error. Its coins are uniform and independent,
so coins derived from a secret seed by a pseudo-random function are not covered. Provers that send
fixed messages and never stop can be simulated with error 0, `OnBytes.WholeKey.silent_good`
(`lean/Johnson/WholeKey/Foes.lean`), so of the provers' own messages the theorem says something only
beside completeness of the same provers. Fifteen of the 20 conditions (a count of conditions, not of
work), those that read no prover, coin or simulator, are proved at the input at which the Lean
verifier calls the compiled verifier: `AtPublicFiles.Premises.noProverSide_description`
(`lean/E2E/PremisesAtFiles.lean`). The other five speak of the three honest provers, their
simulators and coins: there hiding itself must be proved.

At full size, where the tests on the public files pass, all 20 are proved for provers that send
fixed messages, and with the link proof's honest prover beside two of them at one constant in the
place of the public files' digest, at which `verify` is not proved ever to be called:
`AtPublicFiles.ZetaAt.privacyWithNumber_description` (`lean/E2E/ZetaAtCaps.lean`),
`AtPublicFiles.LinkLaid.linkLaidAtOnce` (`lean/E2E/LinkLaidPrivacy.lean`). The error is then at most
2^-135 for one copy, one request and 2^64 hash queries; for more the bound is a formula, which no
theorem evaluates there. In both cases the key file's and the request's provers send fixed messages:
nothing that these two would compute from the weights is covered. That is proved for one request per
proof, not for batches, and of the paper's whole-key argument, not of the Lean verifier's own system
(`lean/LIMITS.md`, L64).

The 20 conditions are conditions on any IOP's provers. The statements on the honest provers written
in Lean are those of table 6, and what is proved of them stands at `lean/LIMITS.md`, L88 to L93 and
L62 to L66. No Lean theorem covers the OOD answers as the programs make them (`lean/LIMITS.md`,
L14).

Where a comment in `lean/ZKCP/Defs.lean`, or in the files that follow it, calls `HasIndexPrivacy`
the definition's form or `HasStrongIndexPrivacyWith` stronger than the definition, this page counts.

**Note 10: the three together.** From `CompleteSoundZeroKnowledge` to `IsZKCPArg`, one direction,
and no converse is stated: `VerifiableInference.CompleteSoundZeroKnowledge.toIsZKCPArg`
(`lean/VerifiableInference/AgreementZeroKnowledge.lean`). Of the Lean verifier's system one of the
three is proved, in a restricted form ([THEOREM.md](THEOREM.md)). No scheme of this protocol is
shown to meet all three clauses of `IsZKCPArg`. To meet `IsZKCPArg` says little by itself. A scheme
with empty proofs meets it (`lean/LIMITS.md`, L35). The clause of `IsZKCPArg` on privacy is the
weaker first form, which the made-up scheme of note 9 meets. The library's bundle with the second
form is `ZKCP.IsZKCPArgWith` (`lean/ZKCP/Defs.lean`), which names its extractor and its simulator
and implies `IsZKCPArg`. The scheme with empty proofs meets that bundle too. The three at one
protocol and one triple of honest provers are stated in another form, at the IOP level: table 6.
`CompleteSoundZeroKnowledge` is a bare conjunction: nothing bounds the verifier's or the honest
side's work, so, by an argument on paper that is not machine-checked, a useless system meets all
three together. It is proved of no system, and of the six top statements as written `lean/GAPS.md`,
39, tells what is expected.

## Table 3: things of this library for which the definitions have no word

| The term | Lean name, with file | The word that our pages use | What it is | What is proved |
|---|---|---|---|---|
| **the guard** in `verify` | `VerifiableInference.Desc.Chain.guarded` (`lean/Johnson/Desc/SeatGuard.lean`), laid by `VerifiableInference.Desc.First.firstChain` (`lean/Johnson/Desc/First/Driver/Chain.lean`) | none | After every step of the proof file's first chain except the one that receives the next token, the verifier checks that its own stored value of that token is unchanged, and rejects the proof if it has changed. It is a test on the verifier's own bookkeeping, not on anything that the prover sends. | The soundness theorem on `verify` is proved of the verifier with this guard, and its proof relies on it: `VerifiableInference.Desc.Chain.guarded_flat` (`lean/Johnson/Desc/Sound/SeatGuardLaws.lean`). That an honest proof passes it is a matter of completeness (table 6; `lean/GAPS.md`, 68; `lean/LIMITS.md`, L74). |
| **the tests on the public files** inside `verify` | `FlashProve.protocolDataWellFormed` (`lean/Johnson/Goal/Description/Live.lean`) | "the gate" · "the live test" · "the verifier's first test" · "entry tests" (fourteen of them, a part of these tests) · "the sixteen conditions" (those that the proof needs) | Tests that `verify` makes on the public files alone, whatever the proof, beyond the test of the scope, `InScope`. Conditions that the soundness proof needs and that are not proved for all files in scope were made such tests. They are not all the places at which `verify` rejects everything on account of the public files alone, and no theorem says which places are all of them. | Where one fails, `verify` rejects everything, and the theorem holds for that reason: it is then vacuous at these files. That is a theorem, at every proof parser and every hash function: `FlashProve.theDescription_dead_all` (`lean/Johnson/Goal/Description/DeadParser.lean`). That they pass is proved at the library's written copies of the two stored sets of public files, and at the first copy under every other policy in scope (with only the policy's three numbers changed, within the four bounds that `theLive_zAt` asks of them), not at the files in this repository, in a side library: `AtFullSide.Top.theLive_zFull` (`lean/AtFullSide/Top/LiveAtFull.lean`), `AtFullSide.Top.theLive_zGap`, `AtFullSide.Top.theLive_zAt` (`lean/AtFullSide/Top/LiveAtPolicies.lean`). At all other files in scope it is not proved. `protocolDataWellFormed` reads no proof: a yes is no sign that `verify` accepts any proof. It is one of the conditions on the public files under which most statements of table 6 are stated (table 6, the row on public files in use). |
| **the executable form** of `verify` | `PV.Ride.rideOf` (`lean/Johnson/PVR/RideAll.lean`); `PV.Ride.verdictThe`, `PV.Ride.verdictThe_is_theDescription` (`lean/Johnson/PVR/RideThe.lean`); `PV.Ride.verdictThe_some`, `PV.Ride.verdictThe_eq` (`lean/Johnson/PVR/RideEveryHash.lean`); `PV.Ride.theForm_eq_verify` (`lean/Johnson/PVR/SoundOfTheForm.lean`); `PV.Ride.sound_of_the_form_events` (`lean/Johnson/PVR/SoundOfTheFormEvents.lean`); at BLAKE2b: `VerifiableInference.executableVerifier` (`lean/AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean`) | "the step-by-step form" · "driver" · "the executable verifier" | `verify` as typed cannot be executed. This is a second term, which Lean's evaluator can run. One command, `lean-verify`, runs the executable form, inside Lean, on the C++ prover's proof files, which a small parser cuts for it. There is no stand-alone binary. | The executable form of `verify` computes `verify`'s own decision at every hash function with 32-byte answers, and is proved sound in the same sense, at the same bound. These are statements about the term's value, not about whether or when an evaluation ends. A run of it is an evaluation, not a proof, and what ran was in part natively compiled code, which is trusted. Whole: [THEOREM.md](THEOREM.md). |
| **an illustrative committer**: a committer written in Lean beside the IOP, not the final system's, that computes its commitment from the weights and its coins, so that the statements that read the honest committer have some content; the system that has it in the constant committer's place is an **illustrative system** | `FlashProve.committerAt` (`lean/Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean`), in `plainSystemAt`; the committer of `theWideDigits`; `Bind.Cpp.cppCommit` (`lean/Johnson/Bind/Cpp/Defs.lean`), in `theCpp` at `Bind.Cpp.theTwin g` (`lean/Johnson/Bind/Cpp/Defs.lean`), where g is a free generator: from a seed it asks two hash queries, makes its coins by g, lays the table from the weights' digits, `Bind.Cpp.entryOf` (`lean/Johnson/Bind/Cpp/Defs.lean`), and these coins, and then calls `Bind.Twin.twinID` (`lean/Johnson/Bind/TwinAlgorithm.lean`) at the full size: that is the text `Bind.Twin.commitW` (`lean/Johnson/Bind/Twin.lean`), taken as an algorithm that gives the commitment ID | none | What distinguishes it from the constant committer: that one returns one constant whatever the weights, and an illustrative committer computes its commitment from the weights and its coins. It is tied to no program in this repository by a theorem. The final system's honest committer is none of these. | The extractor is the IOP's own: `FlashProve.extractor_atOlder` (`lean/Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean`), `VerifierAndGoals.AtTheName.same_extractor_wide` (`lean/Johnson/Goal/SameExtractorWide.lean`), `Bind.Cpp.cpp_is_of_verify` (`lean/Johnson/Bind/Cpp/OfTie.lean`). What is proved of these systems: notes 4 to 7. Nothing on completeness or hiding. |
| **the statement on codes** | `Cb.BCHKS46At` (`lean/Cb/Gen/CodeListRSAt.lean`); at this library's two fields `Cb.Gl.bchks46At` (`lean/Cb/Bridge/GlCodesProved.lean`) | "the theorem on codes" (in some comments) | Mutual correlated agreement of Reed–Solomon codes, for two words, below the Johnson radius. | The library proves it at its two fields, from files that AI systems adapted from third-party Lean. |
| **Johnson radius**, **Johnson list bound** | the condition on the radius in `Cb.BCHKS46At` (`lean/Cb/Gen/CodeListRSAt.lean`); `Cb.InJohnson`, `Cb.listMax` (`lean/Cb/Gen/JohnsonList.lean`) | "the Johnson bound" (of either) | Two things with one name. The radius is where the statement on codes ends. The list bound counts the code words close to a word. | The proximity rounds rest on the statement on codes together with the list bound; the batching and out-of-domain rounds on the list bound alone. |
| **round-by-round knowledge soundness** of a sub-protocol | `Iop.Reduction.Know` (`lean/Ior/Know.lean`) | "knowledge soundness" (of sub-protocols and reductions) | A property of interactive parts, with witnesses of their own. It is not a property of the whole argument. | `Iop.Reduction.Know` is stated of parts alone; the protocol as a whole has a statement of its own (table 6, soundness as an IOP). On a page the two words never stand alone for what `Sound` says. |
| **honest-verifier zero knowledge** of the interactive protocol | at the protocol `VerifiableInference.Compilation.HonestVerifierZeroKnowledge` (table 6); in general form `Hiop.HVZKWholeR` (`lean/Hiop/RecWhole.lean`); for the link proof `OnBytes.LinkSim.AtHome.homeExactAt` (`lean/Johnson/LinkSim/AtHome/HomeExactAll.lean`) | "hiding from an honest verifier" | Another kind of property: of an IOP, against an honest verifier, before any hashing, with a bound on the positions that are read of each encoded index. It keeps its name. It is not index privacy, which is a property of the argument, with the number of sessions in its error. | Of the honest provers written in Lean: `lean/LIMITS.md`, L88 to L93. In general form: conditional theorems, for every object that meets their premises. Their premises are shown, at the IOP of this page with its index type cut to the matrices in range, of the fixed-message provers (provers that send the same messages whatever the weights, and so show nothing of them; at public files in use the protocol's honest provers are others: only where a function that makes them refuses do they fall back on these) (`AtPublicFiles.AtFiles.tables_atFiles` (`lean/E2E/WholeViewAtFiles.lean`)). The next row's result goes by another theorem and needs no cut. The link proof has a theorem of its own. Before hashing, at full size, Lean proves perfect honest-verifier zero knowledge for it (`homeExactAt`): the simulated view has exactly the honest view's distribution. A written simulator is given the two tables' OOD seeds and answers, the verifier's challenges and the columns opened in the two tables. This is no statement that the weights are hidden: answers and columns are computed from them. |
| **independence of the index, for the committed tables alone**; after the first use on a page: the result on the committed tables | `AtPublicFiles.AtFiles.tables_own_named`, `AtPublicFiles.AtFiles.tables_own` (`lean/E2E/TablesAtOwnObject.lean`); for a single table `AtPublicFiles.Table.HidE` (`lean/E2E/TableHides.lean`), `AtPublicFiles.Reads.hidE_filesAt` (`lean/E2E/ReadsAtFiles.lean`) | none on a page; in the Lean files' comments "the result on the index's committed tables" · "the interface's clause on the encoder" · "query bound" (the budget of columns) | A fact on the encoder of an IOP and on how many columns its verifiers read, before any hashing: what is shown of the tables that encode the index (each table's OOD sample and every opened column, within a budget of columns for each table) has the same distribution at every index. It covers no message of a prover. A prover's messages are what the IOP's provers send in their rounds; the committed tables, their OOD samples and the columns of these tables that a proof opens are not among them. So it is not honest-verifier zero knowledge of the protocol, and it is not index privacy, which is a property of the argument. Lean's encoder is the function that turns the weights and given random values into the table that is then committed, before any hashing. | Proved at the IOP of this page with its fixed-message provers (not the protocol's at public files in use: table 6), at 44,040,191 columns a table, for uniform pads and encoding randomness that are fresh for each table, one OOD sample a table, one set of public files for a table's random values, and OOD seeds chosen from nothing hidden. Nothing in Lean keeps count of the budget. At one column more the statement for a single table fails: `AtPublicFiles.AtFiles.not_hidE_own` (`lean/E2E/ObjectGuardsSeeded.lean`). Nothing on a prover's messages, nothing after compilation, nothing on a program. The conditional theorem carries the single-table statement past hashing for fixed-message provers (note 9). |
| **a comment** in a Lean file | none | none | Text that Lean does not check. Lines in comments that name a reading: `lean/LIMITS.md`, L75. | Nothing hangs on a comment: where a comment and a statement disagree, the statement holds. |
| **vacuous**, of a statement | none | none | True because its hypothesis is never met, so that it says nothing. | none |
| **trivially**, of zero knowledge or index privacy | none | none | Met by a prover that shows nothing. | none |

## Table 4: the verifier programs

The first two are other texts than `verify`. No theorem ties either of them to `verify` at the IOP
of this page. One layer down, for the compiled verifier at a general input, a tie from the exit
status 0 of `verify-on-bytes` is stated, on the statements that its free parameter Served admits, at
Lean's BLAKE2b in the sampled function's place, under hypotheses that are proved at no input:
`OnBytes.K.exit_innerCompiledVerifier` (`lean/Johnson/Top/TieInnerCompiledVerifier.lean`). The third
row's command, `lean-verify`, evaluates the executable form of `verify`: what is proved of that form
stands in table 3, and what is not proved of the command in its own row.

| The term | Lean name, with file | The word that our pages use | What it is | What is proved |
|---|---|---|---|---|
| **the C++ verifier**, `cp_verify` | none | the same words | The verifier that users run. | Nothing under lean/ is proved of it. |
| `verify-on-bytes` | the Lean text below `lean/OnBytes/Main.lean` | "the Lean program" | A test tool, written in Lean by following the C++ verifier's source; not the verifier of the soundness theorem on `verify`. This folder's build file makes no stand-alone program from it. | A theorem ties its exit status to `innerCompiledVerifier`, another Lean verifier, only under hypotheses that are not proved. Even under them no theorem bounds the chance that it accepts a false file at its own fixed hash function. |
| **the command** `lean-verify` | none: a script, under tools/lean-verify/; what it evaluates: the executable form of `verify` (table 3) | none | A script that evaluates the executable form on a proof's files, inside Lean. It does not build the library: it stops unless the part that it needs is built already, and it compiles and links only the helper library of native code. It is not a binary. | What is proved of what it runs: the row on the executable form (table 3). Of the script itself nothing is proved. A run trusts Lean's evaluator and compiler, the natively compiled helper modules, and the short functions that turn a user's files into the claim, `PV.Program.claimOf` (`lean/Johnson/PVR/Program.lean`) with its two readers `PV.Front.idOf`, `PV.Front.userOf` (`lean/Johnson/Top/Fire/Code/PvFront.lean`): no theorem says that these cut the files as the format page means. The whole list of what a run trusts: tools/lean-verify/README.md. It says nothing about cp_verify. |
| **the line on codes** that `cp_verify` prints | none | "binding of the weights" (in that printed line) | The programs' own printed word. The line says on what the programs' own reckoning rests: the committed table's closeness tests are sized up to the Johnson radius, and the programs count their error by a theorem on codes that they take as given. It does not say that anything is missing. | It is not the Lean theorem's index-binding knowledge soundness, and nothing of it is proved in Lean of the programs. The Lean theorem takes no statement on codes as given: the library proves the one that it uses, from files that AI systems adapted from third-party Lean (table 3). |

## Table 5: the paper's terms

The paper defines its terms in statements of its own. This table lists them by title, with the terms
that each defines, their first Lean names (at most three) and the words of these pages where they
differ.

| The paper's terms | Lean name, with file | On these pages |
|---|---|---|
| Random oracle, query bound, trace | `VerifiableInference.Hash`, `VerifiableInference.uniformHash`, `VerifiableInference.RandomizedAlgorithm` (`lean/VerifiableInference/RandomOracleModel.lean`) | random oracle; trace, on some pages "query log" (table 1) |
| Mutual correlated agreement | none | the same; "the statement on codes" is a bound on it for Reed–Solomon codes |
| Interactive oracle proof, batch | `Iop.InteractiveOracleProof`, `Iop.InteractiveOracleProof.IsLocal` (`lean/Iop/InteractiveOracleProof.lean`); `Iop.BatchInteractiveOracleProof` (`lean/Iop/Batch.lean`) | interactive oracle proof (table 1) |
| Compilation (BCS transformation) | `VerifiableInference.Compilation.compile`, `VerifiableInference.Compilation.compiledSide`, `VerifiableInference.Compilation.compiledVerifier` (`lean/Johnson/Face/Compiler.lean`) | compiled by Merkle trees and the Fiat–Shamir transformation; "hashing", "after hashing"; the final system and the compiled verifier: "Which system"; the compiled committer and prover: table 6. The library has other compilers too, which no statement of table 6 is about (`lean/LIMITS.md`, L14, L21) |
| Proof of work (grinding) | `Iop.WorkBits` (`lean/Hiop/CompleteCore.lean`); `TypedOracleCompiler.Iop.GrW`, `TypedOracleCompiler.Iop.GrW.ok` (`lean/OnBytes/TypedOracleCompiler/Iop/BatchWire.lean`) | the same; before hashing: table 6, the row on the challenges that pass the proof-of-work tests |
| Indexed relation, commit-and-prove argument | `VerifiableInference.ArgumentSystem` (`lean/VerifiableInference/Statements.lean`); `VerifiableInference.ArgumentSystem.uploadRelation`, `VerifiableInference.ArgumentSystem.uploadArgument` (`lean/VerifiableInference/Agreement.lean`) | table 1. The pair of a prompt and an output is a request on these pages; the commitment has the role of the index verification key |
| Index-binding knowledge soundness | `VerifiableInference.Sound` (`lean/VerifiableInference/Statements.lean`); `ZKCP.HasIndexBinding`, `ZKCP.bindingExp` (`lean/ZKCP/Defs.lean`) | table 2; the extractor: table 1 |
| Correctness of extraction | `VerifiableInference.ExtractsCommittedWeights` (`lean/VerifiableInference/MoreStatements.lean`) | table 2 |
| Extractability of the commitment, no two openings | `VerifiableInference.BindsWith`, `VerifiableInference.NoTwoOpenings` (`lean/VerifiableInference/MoreStatements.lean`) | table 2; for the first also "binding of the commitment, in the opening form" |
| Completeness on a set of triples | `VerifiableInference.CompleteOn` (`lean/VerifiableInference/Steps.lean`); `VerifiableInference.Complete` (`lean/VerifiableInference/Statements.lean`) | table 2, note 8 |
| Real and ideal experiment | `ZKCP.Gen.Arg`, `ZKCP.Gen.realExp`, `ZKCP.Gen.idealExp` (`lean/ZKCP/Gen.lean`) | table 1: environment ("chooser"), adversarial verifier, simulator, view |
| Index privacy | `ZKCP.Gen.PrivacyOn` (`lean/ZKCP/OnRange.lean`); `ZKCP.Gen.PrivacyFor`, `ZKCP.Gen.HasIndexPrivacyWith` (`lean/ZKCP/Gen.lean`) | table 2, note 9; with batches and a set of instances: the row "index privacy for batches" |
| Integer model | `VerifiableInference.ModelWeights`, `VerifiableInference.settingsAreValid`, `VerifiableInference.modelNextToken` (`lean/VerifiableInference/ModelWeights.lean`) | the same |
| Greedy token, greedy output | `VerifiableInference.modelNextToken` (`lean/VerifiableInference/ModelWeights.lean`); `VerifiableInference.ArgumentSystem.IsModelOutput` (`lean/VerifiableInference/Statements.lean`); `Policy.modelNextToken_eq_firstArgmax` (`lean/Policy/Front/MeetsPolicyGuards.lean`) | language of an index (table 1); "the model's output"; the greedy token: the model's "top choice" |
| Logit gap, acceptance policy, exact match, clipped gap | `Policy.logitGap`, `Policy.tokenCost`, `Policy.outputCost` (`lean/Policy/Front/MeetsPolicy.lean`) | policy; exact match; a clipped-gap policy: a "tolerant policy"; the stored one: "the stored tolerant policy" |
| Model parameters | `IntegerTransformer.Settings` (`lean/IntegerModel/Model.lean`); `VerifiableInference.settingsInRange`, `VerifiableInference.settingsAreValid` (`lean/VerifiableInference/ModelWeights.lean`) | settings |
| Configuration, default configuration | `VerifierAndGoals.PublicFiles`, `VerifierAndGoals.storedPublicFiles`, `VerifierAndGoals.zGap` (`lean/Ladder/Stored.lean`) | public files; the default configuration: the first of the two stored sets of public files. "The default setting" is wider: the format's default, at full size and at the small size |
| Admissible configuration | `VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`, `VerifierAndGoals.settingsOfRead` (`lean/Ladder.lean`) | public files in scope (table 1, the row on public files). Not admissible: a reduced configuration, for a far smaller synthetic model; "the small size" is one |
| Masked encoding, committed table, opening budget | `OnBytes.Flat.codingCells`, `OnBytes.Flat.cellEntryAt` (`lean/Johnson/Flat/CodingCells.lean`); `OnBytes.Flat.codingHonest` (`lean/OnBytes/Flat/CodingHonest.lean`) | committed table; a budget of columns for each table |
| Out-of-domain seed, answers, sample | `Iop.HolographicProtocol.Rec` (`lean/Hiop/RecInterface.lean`); `Hiop.ConfigurationWithOutOfDomainSample.smp` (`lean/Hiop/RecConf.lean`); `OnBytes.Slice.recZ` (`lean/OnBytes/Slice/RecordRead.lean`) | OOD seed, OOD answers, OOD sample |
| First table, copy, link proof | `Iop.HolographicProtocol.link` (`lean/Hiop/RecInterface.lean`); `VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound` (`lean/Johnson/Top/InnerCompiledVerifier.lean`) | the same |
| Encoded request, offline and online proof, files | `IntegerModel.requestOf` (`lean/VerifiableInference/RequestOfTokens.lean`); `VerifiableInference.OnPublicFiles.Flat.buildReq`, `VerifiableInference.OnPublicFiles.Flat.Req` (`lean/Johnson/Flat/LedgerClaim.lean`) | not the request of these pages, which is the pair of the row on the commit-and-prove argument; the files: key file, the copy's file, proof file (table 1, the row on the proof) |
| Separate second hash | `VerifierAndGoals.atSecondHashFunction` (`lean/Ladder.lean`); `OnBytes.secondHashFunction` (`lean/OnBytes/Hash/SecondHashFunction.lean`) | table 1, the row on the second hash function |
| Parameter checks | `FlashProve.protocolDataWellFormed`, `FlashProve.protocolDataWellFormedAt`, `FlashProve.dataWellFormedAtFullSizeDepth` (`lean/Johnson/Goal/Description/Live.lean`) | the tests on the public files (table 3) |
| The argument | `VerifierAndGoals.systemOfRecord`, `VerifierAndGoals.atSecondHashFunction` (`lean/Ladder.lean`); `VerifierAndGoals.theDescription` (`lean/Johnson/Goal/Description/Description.lean`) | the Lean verifier's system ("Which system") |
| Executable form | `PV.Ride.theForm` (`lean/Johnson/PVR/SoundOfTheForm.lean`); `FlashProve.FormBytes` (`lean/Johnson/Goal/Tie/DescriptionOnBytes.lean`); `VerifiableInference.OnPublicFiles.hashOf` (`lean/Johnson/Top/Fire/Code/FastFamProbe.lean`) | the executable form (table 3) |
| Soundness under any policy | `VerifierAndGoals.AtTheName.soundUnderPolicy_of_verify_at` (`lean/Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean`); `VerifierAndGoals.AtTheName.indexBindingUnderPolicy_of_verify_at` (`lean/Johnson/Goal/Skeleton/SoundOfVerifyForms.lean`) | "the theorem under a policy", "soundness under the policy" (table 2, note 2) |
| Explicit committer | `Bind.Cpp.cppCommit`, `Bind.Cpp.theTwin`, `Bind.Cpp.theCpp` (`lean/Johnson/Bind/Cpp/Defs.lean`) | the third committer of table 3's row on illustrative committers |
| Constant-message prover | `OnBytes.WholeKey.silent` (`lean/Johnson/WholeKey/Foes.lean`); `OnBytes.Flat.Files.fixedMessageProvers` (`lean/OnBytes/Flat/Silent.lean`); `AtPublicFiles.Premises.silentAtC` (`lean/E2E/FiveLeftSilentCaps.lean`) | fixed-message provers: provers that send the same messages whatever the weights |
| Disclosed view, honest-verifier simulator | `Iop.Honest`, `Iop.DView`, `Iop.InteractiveOracleProof.dview` (`lean/Iop/InteractiveOracleProof.lean`) | |
| Table experiment | `Hiop.Seeded.EnvS`, `Hiop.Seeded.HostS.view`, `Hiop.Seeded.realHostS` (`lean/Hiop/Seeded/Whole.lean`) | |
| Within the opening budget | `Hiop.BoundsR.Fits` (`lean/Hiop/RecWhole.lean`); `Hiop.Seeded.EnvS.Adm` (`lean/Hiop/Seeded/Whole.lean`) | |
| Compiled run of a prover | `OnBytes.WholeKey.shown`, `OnBytes.WholeKey.HonestSide` (`lean/Johnson/WholeKey/Defs.lean`); `TypedOracleCompiler.Compile.Batch.Cms.proveTA` (`lean/Johnson/Prover/YesOfProve.lean`) | |
| Coins of a compiled run | `OnBytes.WholeKey.dress` (`lean/Johnson/WholeKey/Defs.lean`); `OnBytes.WholeKey.RunLaw`, `OnBytes.WholeKey.SaltsLaw` (`lean/Johnson/WholeKey/CoinLaws.lean`) | |
| Whole-key argument | `OnBytes.WholeKey.wholeKeySchemeOverTypedOracles` (`lean/Johnson/WholeKey/AtInput.lean`); `OnBytes.WholeKey.argW`, `OnBytes.WholeKey.commitAt` (`lean/Johnson/WholeKey/Defs.lean`) | the argument with its whole key published |
| Five conditions on the provers | `AtPublicFiles.Premises.FiveLeft` (`lean/E2E/PrivacyAtDescription.lean`); `OnBytes.WholeKey.ExtEnc`, `OnBytes.WholeKey.Sims.Good` (`lean/Johnson/WholeKey/Premises.lean`) | |
| Hashing error | `Rom.costTotal` (`lean/Rom/SpecHopCost.lean`); `OnBytes.WholeKey.mW`, `OnBytes.WholeKey.eW` (`lean/Johnson/WholeKey/Zeta.lean`) | |
| Instances that can be served | `VerifiableInference.CanServe` (`lean/VerifiableInference/CanServe.lean`); `IntegerModel.zeroFilledWindow` (`lean/IntegerModel/Window.lean`) | the requests that can be served |
| The rounds of the three IOPs | `VerifiableInference.Desc.Key.descriptionFromSource` (`lean/Johnson/Desc/Key/Desc.lean`); `Desc.K15.linkDescriptionAt` (`lean/Johnson/Desc/Link/LinkDesc.lean`); `ProofFile.onlineDescription` (`lean/Johnson/Desc/ProofFile/OnlineDescription.lean`) | |
| Oracles, seeds, and the compiled verifier of one IOP | `TypedOracleCompiler.Compile.Batch.typedOracleFamily` (`lean/OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean`); `Rom.OracleCoding` (`lean/Rom/Family.lean`); `TypedOracleCompiler.Compile.Batch.OneProtocolProof` (`lean/OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean`) | |

## Table 6: the honest provers written in Lean, and the statements on them

This table says what each thing is. It does not say whether a statement is proved: what is proved,
at which bound, stands at [LIMITS.md](LIMITS.md), L88 to L93, and [THEOREM.md](THEOREM.md). Every
term here is about the Lean provers exactly as written, default values included (the row on the
honest provers); none is about a program. A last name can stand in two files (`CompleteAtFiles`,
`theProvers`): a name is meant at the file named beside it.

| The term | Lean name, with file | The word that our pages use | What it is |
|---|---|---|---|
| **the protocol**, at given public files | `AtPublicFiles.AtFiles.protocolAtFiles` (`lean/E2E/BridgeJoinAtFiles.lean`), of the type `Iop.HolographicProtocol` (`lean/Hiop/RecInterface.lean`) | "the three proofs" · "offline, link and online" | Three IOPs: offline (the proof in the key file, on the first table), link (from a copy to the first table) and online (the proof for one request, on a copy). Every table has an OOD sample, in both phases, and the proximity tests are sized up to (just inside) the Johnson radius (table 3). This is the object inside the Lean verifier: `AtPublicFiles.AtFiles.object_description` (`lean/E2E/DescriptionTie.lean`). The three provers inside this term are fixed-message provers, which no verifier reads; the honest provers stand beside them. |
| **the honest provers**: offline, link, online | the type `VerifiableInference.Compilation.HonestProvers` (`lean/Johnson/Face/Protocol.lean`); the value `AtPublicFiles.AtFiles.HonestTerm.honestProvers` (`lean/E2E/TheHonestProver.lean`) at `AtPublicFiles.AtFiles.HonestTerm.thePartsAt` (`lean/E2E/KeyArgumentsAt.lean`), in the library's type `OnBytes.Prover.ThreeProvers` (`lean/Johnson/Prover/All/OfHonest.lean`); with the online prover made to refuse a request that is not served, as the theorems of `lean/LIMITS.md`, L90 to L93, have it: `VerifiableInference.Compilation.theProvers` (`lean/Johnson/Face/HonestProversWithCompiledPart.lean`) | "the Lean prover" · "the prover written in Lean" | One prover for each IOP, written in Lean as a definition, at the full size. It is no program: among other things it reads the model's trace by a non-constructive choice. Where a function that it calls refuses, it sends a fixed value, a **default value**; the listed places stand in `lean/E2E/TheHonestProverStatements.lean` and in the head of `lean/E2E/KeyArgumentsAt.lean`. The committer is no fourth prover: at this level it is the encoder, the OOD sample and their randomness. |
| **the honest provers, made to refuse** | `VerifiableInference.Compilation.HonestProvers.refuseUnserved` (`lean/Johnson/Face/Protocol.lean`); `VerifiableInference.Compilation.theProvers` (`lean/Johnson/Face/HonestProversWithCompiledPart.lean`) | "made to refuse" | The same provers, but that the online prover shows nothing at a request that is not served: its private stops (the row on stops) widen to every message there. Whether a request is served depends on the weights, which the prover holds. |
| **served request** | `AtPublicFiles.AtFiles.ServedRequest` (`lean/E2E/CompleteAsIOPAtFiles.lean`) | "the requests that are served" | At the index of some weights: a well-formed request whose model result is its claimed output, with the instance that the verifier's builder makes of it. Where the model has no result, nothing is served. The set depends on the weights. How it stands to `CanServe` (table 2): `VerifiableInference.AtEveryRequest.wellFormed_and_result_iff` (`lean/VerifiableInference/WellFormedRequests.lean`). |
| **well-formed request**; **the label of a reply** | `VerifiableInference.AtEveryRequest.WellFormedRequest` (`lean/VerifiableInference/WellFormedRequests.lean`); `VerifiableInference.AtEveryRequest.requestLabel`, `VerifiableInference.AtEveryRequest.Label` (`lean/VerifiableInference/RequestLabel.lean`); `VerifiableInference.reply` (`lean/VerifiableInference/Labelled.lean`) | "served" · "failed" · "other tokens" | A well-formed request: its tokens are in the vocabulary, neither list is empty, and together they have at most 1,025 tokens. The label says what became of a request: served, failed (the model has no value on the request's window) or other tokens. It is a function of the weights and the request. In the corollary it goes out beside the proof, and no verifier checks it. An ill-formed request gets "other tokens". |
| **the bit of a request** | `VerifiableInference.AtEveryRequest.requestOutcome` (`lean/VerifiableInference/RequestOutcome.lean`), `VerifiableInference.AtEveryRequest.Outcome` (`lean/VerifiableInference/AtEveryRequest.lean`); from the label: `VerifiableInference.AtEveryRequest.bitOf_requestLabel` (`lean/VerifiableInference/RequestLabel.lean`) | "served" · "refused" | The bit says whether a request is served: it is well formed, and the model's result on it is its claimed output. Every other request is refused: the model has no result, its result is other tokens, or the request is ill-formed. The bit is a function of the weights and the request, and the label's coarser form: the label is served exactly if the bit is. At a refused request every reply that the prover can return is the empty proof (`noProofForm`: a form all of whose parts are empty). That a request is refused is unchecked, as the label is: an empty proof proves nothing, and a prover can return it at a request that it could serve. |
| **the premise on the weights of the completeness theorem at weights that pass a worst-case check** (`theHonestPart_complete_where_some_worst_case_check_passes`); **weights at which the model never fails** | `VerifiableInference.PassesSomeWorstCaseCheck` (`lean/VerifiableInference/Bounds/SomeWorstCaseCheck.lean`): the first worst-case check, or the least-bound check with numbers that hold; its two checks: `VerifiableInference.PassesWorstCaseCheck` (`lean/VerifiableInference/Bounds/NeverFails.lean`), `VerifiableInference.PassesLeastBoundWorstCaseCheck` (`lean/VerifiableInference/Bounds/LeastBoundNeverFails.lean`); `VerifiableInference.ModelNeverFails` (`lean/VerifiableInference/ModelNeverFails.lean`) | "the first check" · "the least-bound check" · "numbers that hold" · "the model never fails" | The premise says of given weights that they pass the first worst-case check, or the least-bound check with numbers that hold: its first arm is this library's own decidable test on settings, tables and weights; its second is a statement that numbers exist that hold together ("numbers that hold": each stretch bound that the least-bound check reads is at least 0, and no vector of whole numbers gets longer by more than that factor when it is multiplied with its matrix; which matrices, and what they are made from: `LeastBoundNumbers.Hold`, `IntegerModel/Bounds/LeastBoundCheck.lean`), and that with them a second test, the least-bound check, passes: a statement, not a test. Neither check is `cp_commit`'s worst-case check (`lean/LIMITS.md`, L7): no theorem relates either to a check that any program makes. `ModelNeverFails` says of given weights that the model has a result on every well-formed request, whatever output it claims. Both are conditions on the weights, not theorems about all weights. No theorem says whether a real model's weights meet the premise, and nothing in a commitment, in a proof or in what a verifier does shows that the committed weights do. |
| **the challenges that pass the proof-of-work tests** | `Iop.WorkBits`, `Iop.chanceAtPassing` (`lean/Hiop/CompleteCore.lean`) | "the challenges that pass" | A verifier rejects unless all the proof-of-work bits of its challenges are 0, so nearly all uniform challenges are rejected. A chance among the challenges that pass is taken over uniform challenges with these bits set to 0. The search for a nonce belongs to the compiled prover, not to the IOP. |
| **public stop**, **private stop** | `Iop.Honest.Bad`, `Iop.Honest.Hid`, `Iop.Honest.withheld` (`lean/Iop/InteractiveOracleProof.lean`) | "stop" · "abort" | The verifier's messages at which a prover shows nothing. A public stop depends on these messages alone. A private stop may depend on the prover's private input and the instance as well, never on its coins. |
| **soundness as an IOP** | `Iop.HolographicProtocol.IndexKnowledgeSoundIOP` (`lean/Hiop/SoundAsIOP.lean`); at the protocol `AtPublicFiles.AtFiles.SoundAsIOPAtFiles` (`lean/E2E/SoundAsIOPAtFiles.lean`) | "round-by-round knowledge soundness" | Round-by-round soundness of the protocol's three verifiers, with the index extracted. It reads no honest prover. Its relation is wider than the served requests. Each round's bound is a share of all that round's challenges, the proof-of-work bits among them. Nothing but the index is extracted, by a function of which no running time is claimed; no witness (the model's trace) is. The form is this library's, and no equivalence with the published notion of round-by-round knowledge soundness is claimed. |
| **completeness as an IOP** | `VerifiableInference.Compilation.CompleteIOP`, `VerifiableInference.Compilation.CompleteInParts` (`lean/Johnson/Face/CompleteAsIOP.lean`); at the protocol `AtPublicFiles.AtFiles.CompleteOnServedRequests` (`lean/E2E/CompleteAsIOPAtFiles.lean`), `AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles` (`lean/E2E/CompleteAsIOPAtNamed.lean`) | "complete as an IOP" | On every index and request of a relation each of the three runs fails rarely, over the prover's coins and the challenges that pass. A run fails if the prover stops or the verifier rejects it. The three errors add up to at most the statement's error: at the served requests `AtPublicFiles.AtFiles.completenessTarget` (`lean/E2E/CompleteAsIOPAtFiles.lean`), 2^-41. Before hashing, one request per proof. |
| **honest-verifier zero knowledge before hashing** | `VerifiableInference.Compilation.HonestVerifierZeroKnowledge` (`lean/VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean`); at the protocol `VerifiableInference.Compilation.ZeroKnowledgeOnServedRequests` (`lean/VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean`); the simulators `VerifiableInference.Compilation.RunSimulators` (`lean/Johnson/Face/Protocol.lean`) | "honest-verifier zero knowledge" | Table 3's property, at the honest provers made to refuse. The simulators are fixed first, and may depend on the public files. A run's simulator is given the verifier's messages, the OOD samples, the symbols of the tables that the verifier reads and, online, the request with its claimed output and the copy's number. Run by run these samples and symbols are the real tables', which are made from the index; in the whole view they are those of tables of another fixed index, and there the simulated side is also given one bit for each request (served or not). They never get the index, a table's randomness or a prover's coins. Nothing bounds their running time. The honest verifier's messages are uniform among the challenges that pass. The distance between the two sides is statistical. Not covered: batches, coins derived from a short key, a second commitment to the same index, a verifier that deviates, what the public files tell of the index, time. |
| **the run-by-run form** | `VerifiableInference.Compilation.RunByRun`, `VerifiableInference.Compilation.ExactOutsideStops`, `VerifiableInference.Compilation.PrivateStopsAtMost` (`lean/VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean`) | "run by run" | Of each run: at every message outside the prover's private stops, the honest output and the simulator's output have one distribution; and the private stops have at most a stated measure, one number for each of the three proofs. |
| **the whole view**; **the whole life of a commitment** | `VerifiableInference.Compilation.WholeView`, `VerifiableInference.Compilation.WholeLife`, `VerifiableInference.Compilation.commitmentLife` (`lean/VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean`) | "the whole life" | The whole view: what an unbounded observer within a budget sees of the honest provers on one index is within a stated distance of what it sees of the simulators on tables of another fixed index. The whole life is that budget for one commitment: one offline run, one link to each copy, a stated number of requests on each copy and none on the first table, asked in any order and adaptively. Nothing in the statement ties a committer or a prover to that budget. The statement at the protocol goes up to 710,324 copies with 688,127 requests each (each one run of the online IOP; after compiling, one reply: the row "reply"). Its error adds up the stops of all these runs, so a number for one run is not the error of a life. |
| **the compiled committer**, **the compiled prover** | `VerifiableInference.Compilation.compile`, `VerifiableInference.Compilation.compiledScheme`, `VerifiableInference.Compilation.compiledSide` (`lean/Johnson/Face/Compiler.lean`) | "compile" | What this library's commit-and-prove variant of the BCS transformation makes of a protocol. Each oracle string goes under a salted hash tree, challenges run along a Fiat–Shamir chain, and a nonce stands where a round has proof of work. The committer makes the first table with its offline proof and each copy with its link proof; the commitment has 256 bits. The prover keeps no state: it runs the committer again, draws one copy at random and proves one request on it. |
| **the honest part** | `VerifiableInference.Compilation.HonestProversAndSettingsAtFiles` (`lean/Johnson/Face/FinalStatement.lean`), `VerifiableInference.Compilation.honestProversAndSettingsAtFiles` (`lean/Johnson/Face/HonestProversWithCompiledPart.lean`); the value `VerifiableInference.Compilation.honestProversAndSettings` (`lean/AtFullSide/Face/HonestProversAndSettingsValue.lean`) | "the honest part" | The honest provers made to refuse, with what compilation adds: search limits, salts, the range of the committer's coins, the sessions that one copy bears, and the instance at which the prover runs where a request builds none. At the value `honestProversAndSettings` there is one copy of the table. |
| **public files in use** | `VerifiableInference.Compilation.FilesTaken`, `VerifiableInference.Compilation.FilesInUse` (`lean/Johnson/Face/FinalStatement.lean`) | "public files in use" · "files in use" | Files taken: public files that are in scope, that are read, and whose policy is exact match. Files in use: these, and they pass the test `FlashProve.protocolDataWellFormed` (table 3). |
| **public setup** | `VerifiableInference.PublicSetup` (`lean/AtFullSide/Face/TheSixLines.lean`): its fields `files`, `readParameters`, `inUse` | "public setup" · "public files in use" · "public files that pass three tests", with exact match | Three public files that a user holds beside the commitment, fixed before the hash function is drawn: the parameter file, the layout file and the scale file; with what the reader returns at them. They are in the verifier's scope, are read without error, state the exact-match policy (the verifier does not test that they state it), and pass the test `FlashProve.protocolDataWellFormed`, which the verifier makes too (table 3). It is the one argument of each of the six lines. It is public files in use (the row on them) with what they read as. `VerifiableInference.storedSetup` is the only one that the library shows (which files it holds: [LIMITS.md](LIMITS.md), "What is proved, and of which object"). It is not the system's `PublicParameters`, which `compile` sets to `Unit`: what the files tell of the weights (a fitted model's scale file is made from its weights) is outside the lines on zero knowledge. |
| **`flashProve setup`** | `VerifiableInference.flashProve` (`lean/AtFullSide/Face/TheSixLines.lean`): `VerifiableInference.Compilation.flashProveAtFiles` at the setup's files, at the settings that they read as, and at the honest part `VerifiableInference.Compilation.honestProversAndSettings` there | "FlashProve at a public setup" | What `compile` takes: the protocol, with its layout into hash queries, its proof format, and the honest provers and settings, which are one closed term. It holds a second, fixed hash function, which is no random oracle. `compile (flashProve setup)` is the final system at that setup. |
| **the Lean verifier**, in two senses | `VerifierAndGoals.verify` (`lean/Ladder.lean`); `VerifiableInference.leanVerifier` (`lean/AtFullSide/Face/TheSixLines.lean`) | "the Lean verifier": on these pages `verify`; on [STATEMENTS.html](STATEMENTS.html) `leanVerifier` | `leanVerifier setup` is `(compile (flashProve setup)).accepts blake2bHash`: the compiled verifier with each of its hash queries answered by BLAKE2b. `verify` is the verifier of that same system, before any hash function is supplied (`VerifiableInference.Compilation.compile_flashProve_verify_eq`, with `VerifierAndGoals.theDescription_eq`). As in any proof in the random-oracle model, the six speak of the verifier under a hash function drawn at random, not of `leanVerifier`, where BLAKE2b stands in its place: the three that speak of acceptance (`sound`, `soundAndBinding`, `completeOnCanServe`) draw the hash function at random, so their verifier is `verify` under a random hash function, not at BLAKE2b; the other three do not call the verifier. As a definition `leanVerifier` cannot be run. `leanVerifier setup` equals `VerifiableInference.Compilation.finalVerifierProgram` at that setup's files (`VerifiableInference.leanVerifier_eq`). Wherever the user's files read as a claim, the verdict of `PV.Program.verdictOf`, the function whose parts `lean-verify` evaluates (`PV.Program.verdictOf_at`, `lean/Johnson/PVR/Program.lean`), is `finalVerifierProgram` at the user's public files (`VerifiableInference.Compilation.verdictOf_eq_finalVerifierProgram`, `lean/Johnson/Face/ExecutableVerifier.lean`), and it is `verify`'s value at BLAKE2b (`PV.Program.verdictOf_map`, `lean/Johnson/PVR/ProgramTotal.lean`). So, where the user's files read as a claim and the user's public files are a public setup's, and only there, that verdict is `leanVerifier`'s (`VerifiableInference.verdictOf_eq_leanVerifier`, `lean/AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean`); the command does not establish that the public files are a public setup's. Five of the files that this function takes come from a parser outside Lean, of which nothing is proved, and nothing is proved of a run ([LIMITS.md](LIMITS.md), L53, L9; table 4). A run counts for the six lines only as far as it is proved to give this term's value. |
| **reply** | the value of the compiled prover at one request; their number in the statements: `VerifiableInference.Compilation.finalReplyCount` (`lean/Johnson/Face/FinalStatement.lean`), 688,127 | "reply" · in single statements: "proof" (`ZeroKnowledgeOn`'s number of proofs), "request" (the IOP's whole life), "session" (`onlineRunsPerCopy`) | What the prover hands back to one request: a proof or the empty proof. The lines on zero knowledge hold up to 688,127 replies. The prover counts no replies. The programs' own 688,127 counts batches, another thing: no theorem ties the two ([LIMITS.md](LIMITS.md), L84). |
| **the six lines**: the six theorems on the compiled prover and verifier | `VerifiableInference.sound`, `VerifiableInference.soundAndBinding`, `VerifiableInference.completeOnCanServe`, `VerifiableInference.zeroKnowledgeOnCanServe`, `VerifiableInference.refusedHandsOutNoProof`, `VerifiableInference.repliesFit` (`lean/AtFullSide/Face/TheSixLines.lean`); the properties that five of them state: `VerifiableInference.Sound`, `VerifiableInference.SoundAndBinding` (`lean/VerifiableInference/Statements.lean`), `VerifiableInference.CompleteOn` (`lean/VerifiableInference/Steps.lean`), `VerifiableInference.ZeroKnowledgeOn` (`lean/VerifiableInference/MoreStatements.lean`), `VerifiableInference.AtEveryRequest.HandsOutNoProof` (`lean/VerifiableInference/AtEveryRequestGuards.lean`) | "the six theorems" · "the six lines" | Six theorems on the final system at public files in use: soundness; soundness with binding of the same committer; completeness at the requests that can be served and whose output is the model's; zero knowledge at those requests, up to a stated number of replies and hash queries; that at a refused request every reply that the prover can return is the empty proof; and that the replies fit the numbers that the proof of zero knowledge reads. One request per proof, one commitment, exact match. These six lines are the library's goals on the compiled prover and verifier; elsewhere on this page "goal" means a proposition that `lean/Ladder.lean`, `lean/Ladder/Bits.lean` or `lean/Ladder/Package.lean` types for any IOP (`VerifierAndGoals.Description`). They are not the six top statements of `lean/GAPS.md`, 39. The line on zero knowledge is not `ZeroKnowledge` of table 2: it is `ZeroKnowledgeOn` at the requests that can be served (the row on served requests), it says nothing of a refused request, and its error is bounded by one number, up to the stated counts. The line on completeness is not `Complete`: it is `CompleteOn` at the requests that can be served (the row on served requests). Beside the six lines stands the completeness theorem at weights that pass a worst-case check, which is no field of a structure: at weights that pass the first worst-case check, or the least-bound check with numbers that hold (the row on that premise) the model has a result on every well-formed request, and for every prompt that is not empty and whose tokens are in the vocabulary, and every output length of at least 1 that fits, there is exactly one output of that length that is the model's own, whose honest proof is accepted up to the completeness error; all at public files in use. It covers no request that the completeness line does not already cover. It is not `Complete` either: it takes a hypothesis on the weights. |
| **the final statement**, a structure of six fields | `VerifiableInference.Compilation.FinalStatementOneBit` (`lean/Johnson/Face/FinalStatementOneBit.lean`); with the label shown: `VerifiableInference.Compilation.FinalStatement` (`lean/Johnson/Face/FinalStatement.lean`); the forms that its fields use: `VerifiableInference.AtEveryRequest.ProofAcceptedWhere`, `VerifiableInference.AtEveryRequest.ZeroKnowledgeWhere`, `VerifiableInference.AtEveryRequest.ZeroKnowledgeBelowWhere` (`lean/VerifiableInference/AtEveryRequest.lean`), `VerifiableInference.AtEveryRequest.ZeroKnowledgeShownBelowWhere` (`lean/VerifiableInference/Labelled.lean`); its fields' statements `VerifiableInference.Compilation.FinalSound`, `VerifiableInference.Compilation.FinalComplete`, `VerifiableInference.Compilation.FinalZeroKnowledgeOneBit`, `VerifiableInference.Compilation.FinalSoundAndBinding`, `VerifiableInference.Compilation.FinalRefusedHandsOutNoProof`, `VerifiableInference.Compilation.RepliesFit` (`lean/Johnson/Face/FinalStatement.lean`, `lean/Johnson/Face/Checks.lean`, `lean/Johnson/Face/FinalStatementOneBit.lean`); with the label shown: `VerifiableInference.Compilation.FinalZeroKnowledge`, `VerifiableInference.Compilation.FinalHandsOutNoProof` (`lean/Johnson/Face/FinalStatement.lean`) | "the final statement" | Of the structure `FinalStatementOneBit` (`lean/Johnson/Face/FinalStatementOneBit.lean`) two fields, `binding` and `repliesFit`, are two of the six lines; two, `sound` and `handsOutNoProof`, say what two of the lines say at more public files (`FilesTaken`: that they pass the test is not asked); `complete` is equivalent to `completeOnCanServe` (`finalComplete_iff_completeOn`, `lean/Johnson/Face/Checks.lean`); and `zeroKnowledge` follows from two of the lines (`zeroKnowledgeAtEveryRequest_of_lines`) and is not proved to give `zeroKnowledgeOnCanServe` back. The field on zero knowledge is not `ZeroKnowledge` of table 2: its simulator is told one bit for each request, which depends on the weights; it speaks of every request, where `ZeroKnowledge` speaks of those with the model's own output; and its error is one number, up to the stated counts. As a corollary, for a service that chooses to say "failed", the same with the three-valued label shown: there the simulator is told each request's label, which depends on the weights, the field speaks of well-formed requests alone, and a reply whose label is not served holds no proof. The field on completeness speaks of well-formed requests whose result is their claimed output. |
| **the three statements at one protocol** | `AtPublicFiles.OneProtocol.ThreeAtOneProtocol`, `AtPublicFiles.OneProtocol.ThreeAtFiles` (`lean/E2E/ThreeAtOneProtocol.lean`) | "one protocol" | Soundness as an IOP, completeness as an IOP and honest-verifier zero knowledge as the fields of one structure, at one protocol, one triple of provers and one value of the proof-of-work bits. Soundness reads neither the provers nor the bits, and stands at a wider relation. The numbers in the fields stand over different distributions and are not to be compared. |
| **the theorems at the top of these statements** | `AtPublicFiles.AtFiles.soundAsIOPAtTheProtocol` (`lean/E2E/SoundAsIOPAtFilesProofs.lean`); `AtFullSide.Honest.complete_in_scope` (`lean/AtFullSide/Honest/CompleteAtTheFiles.lean`); `VerifiableInference.Compilation.zkOnServedRequests_inScope` (`lean/AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean`); `VerifiableInference.sound`, `VerifiableInference.soundAndBinding`, `VerifiableInference.completeOnCanServe`, `VerifiableInference.zeroKnowledgeOnCanServe`, `VerifiableInference.refusedHandsOutNoProof`, `VerifiableInference.repliesFit` (`lean/AtFullSide/Face/TheSixLines.lean`); `VerifiableInference.Compilation.finalZeroKnowledgeOneBit_value` (`lean/AtFullSide/CompletenessAndZeroKnowledge/OneBitAtHonestProversAndSettings.lean`); `VerifiableInference.Compilation.theFinalStatementOneBitHolds` (`lean/AtFullSide/Face/TheFinalStatementOneBitHolds.lean`); `VerifiableInference.Compilation.theFinalStatementHolds` (`lean/AtFullSide/Face/TheFinalStatementHolds.lean`); `VerifiableInference.Compilation.threeAtFiles_in_use` (`lean/AtFullSide/Face/TheThreeAtTheFiles.lean`); `VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes` (`lean/AtFullSide/E2E/CompleteWhereSomeWorstCaseCheckPasses.lean`; its premise: the first worst-case check, or the least-bound check with numbers that hold) | none | In this order: soundness as an IOP; completeness as an IOP; honest-verifier zero knowledge; the six theorems; the final statement's field on zero knowledge; all six fields; all six with the label shown; the three statements at one protocol; the completeness theorem at weights that pass a worst-case check. What each says, and within which bounds: [LIMITS.md](LIMITS.md), L88 to L93. |

## Four statements, as they stand in the files

The definition of soundness: `VerifiableInference.Sound`
(`lean/VerifiableInference/Statements.lean`).

```lean
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

That it is index binding, for every argument system: `VerifiableInference.sound_iff`
(`lean/VerifiableInference/Agreement.lean`).

```lean
variable (system : ArgumentSystem)

theorem sound_iff (ε : ℕ → ℝ≥0∞) :
    Sound system ε ↔ ZKCP.HasIndexBinding system.uploadRelation system.uploadArgument
        (fun tC tP => ε (tC + tP))
```

The theorem: `VerifierAndGoals.AtTheName.sound_of_verify_at`
(`lean/Johnson/Goal/Skeleton/SoundOfVerifyAt.lean`).

```lean
theorem sound_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1
```

The honest committer and prover of that system: `FlashProve.fixedCommitterAndProver`
(`lean/Johnson/Goal/Tie/DescriptionOfData.lean`).

```lean
def fixedCommitterAndProver : CommitterAndProver FormBytes where
  Shown := Unit
  shown := fun _ _ => ()
  Rand := Unit
  sample := .done ()
  commit := fun _ _ _ _ => .done fun _ => false
  prove := fun _ _ _ _ _ _ => .done ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty,
      ByteArray.empty, ByteArray.empty⟩
```
