-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/SoundAsIOP.lean: what it means that a protocol is sound as an interactive oracle proof (IOP),
round by round, with ONE NAMED STRAIGHT-LINE EXTRACTOR OF THE INDEX, before any hash. Definitions and
statements; the proofs are in Hiop/SoundAsIOPProofs.lean and, for the two bounds of line 10, in
Hiop/SoundAsIOPSum.lean.
Nothing is proved in this file.

If this holds: whatever a prover sends, if the verifiers of the protocol's three parts accept, then
the first table decodes to an index, the copy decodes to that same index, and the request is true at
that index; but for a chance that is bounded round by round.

 1. The protocol has three parts. Offline: on the first table, the committed encoding of the index.
    Link: from a copy, a further encoding, to the first table. Online: the proof for a request, on
    the copy.
 2. Each table has an out-of-domain sample: after the table is sent the verifier draws a point, and
    the prover answers. Beyond unique decoding a table may lie near several codewords; the sample is
    to single one out. A table HAS A COLLISION AT A POINT if the point fails to tell these apart
    (L.hasCollisionAt: here abstract, a property of (table, point); no answer occurs in it).
 3. THE EXTRACTOR is the index decoder at the first table and that table's sample (extractIndex). It
    reads nothing else, and runs the prover once. So its output is fixed after the second round of
    the whole run (line 6), before any round of the offline part. It is a function, not an algorithm:
    no running time is claimed.
 4. SoundInParts: THREE ROUND-BY-ROUND STATEMENTS, ONE FOR EACH PART, CONJOINED, with two clauses on
    collisions. Here a table's sample stands in the instance of each part. It is the library's
    HolographicProtocol.SoundAtR, the premise of the compiler's theorem, at the witness type Unit
    (Spec.soundInParts_iff_soundAtR).
 5. IndexKnowledgeSoundIOP: THE DEFINITION: SoundInParts for some lists of errors, each error at most
    bound as a probability. The library's own word for these clauses is "index binding, round by
    round".
 6. The three as one protocol, the whole run:
      the prover sends the first table  | the verifier draws the point of its sample
      the prover sends the answer       |
      the offline rounds
      the prover sends a copy           | the verifier draws the point of its sample
      the prover sends the answer       |
      the link's rounds
      the prover names a request (as much of it as is fixed first: L.early)
      the online rounds, for one request.
    BOTH TABLES ARE PROVER'S MESSAGES AND BOTH SAMPLES ARE ROUNDS.
 7. WholeRunSound: ONE STATEMENT: at the empty transcript of the whole run the prover has lost
    (Doomed, Iop/Rbr.lean), with one list of errors, one number for each round, none added up,
    towards THE CONCLUSION (WholeRun.Concludes): if all three verifiers accept, the extractor answers
    an index, the copy with its sample decodes to THAT index, and the relation holds of THAT index
    and the request.
 8. wholeRunState: THE ONE STATE FUNCTION, on partial transcripts of the whole run: "the prover has
    lost" (Lost, Iop/State.lean). Its four laws (Spec.wholeRunState_laws): lost at the start; no
    message of the prover leads out; at most that round's error many challenges lead out; lost at the
    end is the conclusion. A round's doomed set is the set of its partial transcripts in that state.
    It is the canonical state function; its sets are not given in closed form round by round. THE LAST
    THREE LAWS HOLD OF Lost BY ITS DEFINITION, at every protocol and every list of errors: all the
    content is the first, "lost at the start", which is WholeRunSound.
 9. The definition gives the one statement, every round of the whole run, the two in which a point is
    drawn among them, at most bound (Spec.wholeRunSound_of_indexKnowledgeSoundIOP), where nothing of a
    request comes late and a batch of each part has a place.
10. For EVERY prover of the whole run (a deterministic strategy; a randomised one is a mixture of
    these): the conclusion fails with probability at most the sum over the rounds of (the round's
    error / the number of its challenges), over uniform challenges; and over uniform challenges with
    the bits of proof of work set to 0, at most the sum in which a round's error is first multiplied
    by the number of challenges that are cleared to one (2^w at w bits of work)
    (Spec.probability_of_doomed, Spec.wholeRunSound_probability; Clearing). AT A PROTOCOL WITH PROOF OF
    WORK THE FIRST OF THE TWO SAYS NOTHING: see Limits.

WHAT KIND OF KNOWLEDGE SOUNDNESS THIS IS, AND IS NOT. What is extracted is the INDEX (for FlashProve:
the committed weights), by a function of which no running time is claimed. Read soberly: soundness,
round by round, together with binding to an index that is fixed after the second round. In that sense,
and in no other, WholeRunSound is round-by-round knowledge soundness with a straight-line extractor, in
this library's form: "for every statement the prover has
lost at the start towards: the verifier rejects, or the extracted value is valid" (as SndBP,
Ior/KnowWide.lean). No instance stands at the start of the whole run, so every run starts lost. In print
the notion reads otherwise: where more than a round's error many challenges lead out of state 0, the
extractor's output at that partial transcript is valid. No equivalence of the two forms is claimed;
this form gives the bound on "accepted, and the extracted value is not valid" for which the printed
form is used. NOTHING ELSE IS EXTRACTED: relation is a property of (index, request); where it hides a
witness under an existential quantifier (a model's trace), no map here returns that witness.

Limits.
- ONE WHOLE RUN: one first table, one copy, one request. A run with many copies, sessions and requests
  is a tree of whole runs that share their beginnings; the state of a whole run reads that run alone.
  No theorem here speaks of the tree. The joint error of a batch's shared rounds stands in
  SoundInParts.online (JointLaw, Iop/Batch.lean), not in WholeRunSound.
- THE ORDER IS FIXED: the copy is sent after the offline rounds, the request is named after the link's.
  A prover that sends the copy earlier is no strategy of this list of rounds.
- WholeRunSound does not give SoundInParts back (an offline verifier that accepts everything beside a
  link's verifier that rejects everything: the whole run is sound, the offline part is not). The
  compiler's theorem takes SoundInParts; and beside it a law of its own on how a point is made from
  hash answers, which no clause here gives.
- PROOF OF WORK IS COUNTED. An error is a count among ALL challenges of its round, the bits of proof
  of work among them: a verifier that rejects unless w such bits are 0 has its round's error, as a
  probability, smaller by the factor 2^w for that reason alone. What a round's law says there: of the
  challenges that pass, at most the round's error many lead out. OVER UNIFORM CHALLENGES EVERY PROVER,
  THE HONEST ONE TOO, IS ACCEPTED WITH PROBABILITY AT MOST 2^-(all bits of work together), so there a
  bound by the plain sum is true and says nothing. Completeness as an IOP is measured over the
  challenges that pass: uniform challenges with the bits of work set to 0. The second bound of line
  10 is in that measure. A round in which a point is drawn has no work.
- WHO DRAWS A POINT. In the whole run the point of a table's sample is a verifier's message, uniform
  among all points: by the type of the table's round, and counted among all points. In SoundInParts no
  point is drawn: a sample is any value of the instance, and the clause samplePoint counts.
- The verifier's randomness of the whole run is two points and the challenges of the three parts (the
  other rounds' challenges have one value): what a whole run of completeness as an IOP draws for the
  verifier (Hiop/SoundAsIOPChallenges.lean).
- The definition is general in L: which points there are, what a collision is and how far the decoder
  reaches are L's. Where a protocol's decoding radius lies is a fact about that protocol's decoder.
- Soundness alone: a verifier that rejects everything has it. Nothing on the honest prover, on
  completeness, on what a view shows. No field of L that belongs to the honest side is read (encodeIndex, honestOutOfDomainAnswer,
  honestOfflineProver, honestLinkProver, honestOnlineBatchProver).
- The whole run is a list of rounds with a condition on full transcripts. It is written as no value of
  the type InteractiveOracleProof, and no compiler takes it.

Names. L, of the library's type HolographicProtocol, holds the parts: L.offline offline, L.link, L.onlineBatch online; L.decodeIndex the
index decoder, L.hasCollisionAt "this table has a collision at this point"; L.OutOfDomainSeed the points, L.OutOfDomainAnswer the
answers; L.maxBatchSize the places of a batch.
-/
import Hiop.RecLine
import Iop.State

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Iop
open Prob Blocks

/-- The sum over the rounds of (the round's error / the number of the round's challenges). -/
def Err.sumOfProbabilities : {s : Shape} → Err s → ℝ≥0∞
  | [], _ => 0
  | r :: _, (e, ε) => (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) + Err.sumOfProbabilities ε

/-- Two lists of numbers, one for each round, multiplied round by round. -/
def Err.timesByRound : {s : Shape} → Err s → Err s → Err s
  | [], _, _ => ()
  | _ :: _, (m, M), (e, ε) => (m * e, Err.timesByRound M ε)

/-- For each round a map on its challenges. For proof of work: "set the bits of work to 0". -/
def Clearing : Shape → Type
  | [] => Unit
  | r :: s => (r.Chal → r.Chal) × Clearing s

/-- The verifier's randomness of a whole execution, cleared round by round. -/
def Clearing.cleared : {s : Shape} → Clearing s → Rho s → Rho s
  | [], _, _ => ()
  | _ :: _, (k, K), (c, ρ) => (k c, Clearing.cleared K ρ)

/-- In each round, no challenge is the cleared form of more than that round's number of challenges
(2^w at w bits of work; 1 where nothing is cleared). -/
def Clearing.AtMostToOne : {s : Shape} → Clearing s → Err s → Prop
  | [], _, _ => True
  | r :: _, (k, K), (m, M) =>
      (∀ c' : r.Chal, cnt (fun c : r.Chal => k c = c') ≤ m) ∧ Clearing.AtMostToOne K M

variable {Index Request : Type}

namespace HolographicProtocol

/-- A table: an oracle string that is meant to encode an index. -/
abbrev Table (L : HolographicProtocol Index Request) : Type := Fin L.wordLength → L.Symbol

/-- An out-of-domain sample on a table: the verifier's point and the prover's answer. -/
abbrev Sample (L : HolographicProtocol Index Request) : Type := L.OutOfDomainSeed × L.OutOfDomainAnswer

/-- **THE EXTRACTOR OF THE INDEX.** Straight-line: it reads the first table and that table's
out-of-domain sample, and nothing else. It is the index decoder at these two. -/
def extractIndex (L : HolographicProtocol Index Request) (firstTable : L.Table) (firstSample : L.Sample) :
    Option Index :=
  L.decodeIndex firstTable firstSample

/-! ## 1. The three parts -/

/-- The errors, by round: counts of challenges. One number for the round in which the point of a
table's out-of-domain sample is drawn (the same for the first table and for a copy), and one list
for each of the three parts. -/
structure RoundErrors (L : HolographicProtocol Index Request) where
  samplePoint : ℕ
  offline : Err L.offline.shape
  link : Err L.link.shape
  online : Err L.onlineBatch.loc.shape

/-- Every error, as a probability, is at most bound. In the offline and the link part the error of a
round that is marked as shared is counted once for each place of a batch: so the compiler's theorem
asks it. -/
structure RoundErrors.Within {L : HolographicProtocol Index Request} (errors : L.RoundErrors)
    (offlineMarks : RoundSplits L.offline.shape) (offlinePlaces : ℕ)
    (linkMarks : RoundSplits L.link.shape) (linkPlaces : ℕ) (bound : ℝ≥0∞) : Prop where
  samplePoint : (errors.samplePoint : ℝ≥0∞) ≤ bound * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞)
  offline : Err.Below (Err.timesShared offlinePlaces offlineMarks errors.offline) bound
  link : Err.Below (Err.timesShared linkPlaces linkMarks errors.link) bound
  online : Err.Below errors.online bound

/-- **Soundness, part by part, with each round's error named: three round-by-round statements,
conjoined**, with two clauses on collisions. A table's out-of-domain sample stands in the instance of
each part. relation: the pairs of an index and a request that count as true. -/
structure SoundInParts (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
    (errors : L.RoundErrors) : Prop where
  /-- Where a table has a collision at its sample's point, the decoder answers nothing. -/
  nothingAtCollision : ∀ (table : L.Table) (sample : L.Sample),
    L.hasCollisionAt table sample.1 → L.decodeIndex table sample = none
  /-- The round of a sample's point: whatever the table, few points give a collision. -/
  samplePoint : ∀ table : L.Table, cnt (fun point => L.hasCollisionAt table point) ≤ errors.samplePoint
  /-- Offline. No collision, and the extractor answers nothing: the prover has lost, at the start,
  towards "the offline verifier rejects". -/
  offline : ∀ (firstTable : L.Table) (firstSample : L.Sample),
    ¬ L.hasCollisionAt firstTable firstSample.1 → L.extractIndex firstTable firstSample = none →
    Doomed L.offline.shape errors.offline fun transcript =>
      L.offline.accept firstSample firstTable transcript = false
  /-- Link. The extractor answers an index; the copy has no collision and does not decode to THAT
  index: the prover has lost, at the start, towards "the link's verifier rejects". -/
  link : ∀ (firstTable copy : L.Table) (firstSample copySample : L.Sample) (index : Index),
    L.extractIndex firstTable firstSample = some index → ¬ L.hasCollisionAt copy copySample.1 →
    L.decodeIndex copy copySample ≠ some index →
    Doomed L.link.shape errors.link fun transcript =>
      L.link.accept (firstSample, copySample) (firstTable, copy) transcript = false
  /-- Online, for a batch. For every copy and every request the prover has lost, at the start,
  towards "the online verifier rejects, or the relation holds of the index to which the copy
  decodes": with a state function for each place of the batch and the joint law on the shared rounds
  (written out: Iop.sndBP_laws, Ior/KnowWide.lean). Where the copy decodes to nothing that goal is met
  for free: that it decodes, and to which index, is the link's clause. -/
  online : ∀ copySample : L.Sample,
    (L.batAt copySample).SndBP L.maxBatchSize L.early L.late
      (fun request copy _ => ∀ index, L.decodeIndex copy copySample = some index → relation index request)
      errors.online

/-- **THE DEFINITION: the protocol is sound as an IOP, round by round, the index being extracted by
extractIndex, every round's error at most bound.** -/
def IndexKnowledgeSoundIOP (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
    (offlineMarks : RoundSplits L.offline.shape) (offlinePlaces : ℕ)
    (linkMarks : RoundSplits L.link.shape) (linkPlaces : ℕ) (bound : ℝ≥0∞) : Prop :=
  ∃ errors : L.RoundErrors,
    errors.Within offlineMarks offlinePlaces linkMarks linkPlaces bound ∧
      L.SoundInParts relation errors

/-! ## 2. The three as one protocol -/

/-- Fixed messages of the right formats, which the type of a round asks for. No statement below
depends on them. -/
structure Fill (L : HolographicProtocol Index Request) where
  table : L.Table
  answer : L.OutOfDomainAnswer
  request : Request

/-- The round in which the prover sends a table, as an oracle, and the verifier draws the point of
that table's out-of-domain sample. -/
@[reducible] def tableRound (L : HolographicProtocol Index Request) (fill : L.Fill) : Round where
  Orc := L.Table
  Pos := Fin L.wordLength
  Sym := fun _ => L.Symbol
  rd := fun table position => table position
  Plain := Unit
  Chal := L.OutOfDomainSeed
  dOrc := fill.table
  dPlain := ()

/-- A table and its out-of-domain sample: two rounds. In the second the prover sends the answer in
the clear, and the verifier sends nothing. -/
abbrev tableRounds (L : HolographicProtocol Index Request) (fill : L.Fill) : Shape :=
  [L.tableRound fill, plainRound L.OutOfDomainAnswer Unit fill.answer]

/-- **The rounds of the whole run**, in order. -/
abbrev wholeRunShape (L : HolographicProtocol Index Request) (fill : L.Fill) : Shape :=
  L.tableRounds fill ++ (L.offline.shape ++ (L.tableRounds fill ++ (L.link.shape ++
       (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))))

/-- **The errors of the whole run, round by round**: nothing is added up. -/
def RoundErrors.wholeRun {L : HolographicProtocol Index Request} (errors : L.RoundErrors) (fill : L.Fill) :
    Err (L.wholeRunShape fill) :=
  (errors.samplePoint, 0,
    Err.app (s := L.offline.shape)
      (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)))
      errors.offline
      (errors.samplePoint, 0,
        Err.app (s := L.link.shape) (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)
          errors.link (0, errors.online)))

/-- What a full transcript of the whole run holds. -/
structure WholeRun (L : HolographicProtocol Index Request) where
  firstTable : L.Table
  firstSample : L.Sample
  offline : Tr L.offline.shape
  copy : L.Table
  copySample : L.Sample
  link : Tr L.link.shape
  /-- the request that the prover names before the online rounds; L.early of it counts -/
  named : Request
  online : Tr L.onlineBatch.loc.shape

/-- A full transcript of the whole run, read. -/
def wholeRunOf (L : HolographicProtocol Index Request) (fill : L.Fill) (τ : Tr (L.wholeRunShape fill)) :
    L.WholeRun where
  firstTable := τ.1.1
  firstSample := (τ.2.1, τ.2.2.1.2)
  offline := Tr.fst τ.2.2.2.2
  copy := (Tr.snd (s := L.offline.shape) τ.2.2.2.2).1.1
  copySample := ((Tr.snd (s := L.offline.shape) τ.2.2.2.2).2.1,
    (Tr.snd (s := L.offline.shape) τ.2.2.2.2).2.2.1.2)
  link := Tr.fst (Tr.snd (s := L.offline.shape) τ.2.2.2.2).2.2.2.2
  named := (Tr.snd (s := L.link.shape) (Tr.snd (s := L.offline.shape) τ.2.2.2.2).2.2.2.2).1.2
  online := (Tr.snd (s := L.link.shape) (Tr.snd (s := L.offline.shape) τ.2.2.2.2).2.2.2.2).2.2

/-- All three verifiers accept: the offline verifier the first table with its sample, the link's
verifier the two tables with their samples, the online verifier the request at the copy with its
sample. -/
def WholeRun.Accepted {L : HolographicProtocol Index Request} (run : L.WholeRun) (request : Request) : Prop :=
  L.offline.accept run.firstSample run.firstTable run.offline = true ∧
  L.link.accept (run.firstSample, run.copySample) (run.firstTable, run.copy) run.link = true ∧
  L.onlineBatch.loc.accept (request, run.copySample) run.copy run.online = true

/-- **THE CONCLUSION.** For every request whose part that is fixed first is the named one's: if all
three verifiers accept, then the extractor answers an index, the copy decodes to THAT index, and the
relation holds of THAT index and the request. -/
def WholeRun.Concludes {L : HolographicProtocol Index Request} (relation : Index → Request → Prop)
    (run : L.WholeRun) : Prop :=
  ∀ request, L.early request = L.early run.named → run.Accepted request →
    ∃ index, L.extractIndex run.firstTable run.firstSample = some index ∧
      L.decodeIndex run.copy run.copySample = some index ∧ relation index request

/-- **Round-by-round knowledge soundness of the whole run FOR THE INDEX: the index is what is
extracted, and nothing else.** At
the empty transcript the prover has lost, with the errors of the whole run, towards the
conclusion. -/
def WholeRunSound (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
    (errors : L.RoundErrors) (fill : L.Fill) : Prop :=
  Doomed (L.wholeRunShape fill) (errors.wholeRun fill) fun τ =>
    (L.wholeRunOf fill τ).Concludes relation

/-- **The state function of the whole run**, on partial transcripts: "the prover has lost". -/
def wholeRunState (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
    (errors : L.RoundErrors) (fill : L.Fill) : PTr (L.wholeRunShape fill) → Prop :=
  Lost (L.wholeRunShape fill) (errors.wholeRun fill) fun τ =>
    (L.wholeRunOf fill τ).Concludes relation

end HolographicProtocol

/-! ## 3. The statements -/

namespace Spec

/-- States: soundness in parts is the premise of the compiler's theorem, at the witness type Unit. -/
def soundInParts_iff_soundAtR : Prop :=
  ∀ (Index Request : Type) (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
      (errors : L.RoundErrors),
    L.SoundInParts relation errors ↔
      L.SoundAtR (Wn := Unit) (fun index request _ => relation index request) (fun _ _ _ => ())
        errors.samplePoint errors.offline errors.link errors.online

/-- States: **soundness in parts gives the one statement on the whole run**, with the same errors,
where nothing of a request comes late and a batch has a place. -/
def wholeRunSound_of_soundInParts : Prop :=
  ∀ (Index Request : Type) (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
      (errors : L.RoundErrors) (fill : L.Fill),
    L.late = none → 0 < L.maxBatchSize → L.SoundInParts relation errors → L.WholeRunSound relation errors fill

/-- States: **the four laws of the state function.** -/
def wholeRunState_laws : Prop :=
  ∀ (Index Request : Type) (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
      (errors : L.RoundErrors) (fill : L.Fill),
    L.WholeRunSound relation errors fill →
    L.wholeRunState relation errors fill (PTr.empty _) ∧
    (∀ (τ : AtP (L.wholeRunShape fill)) (message : τ.round.Msg),
      L.wholeRunState relation errors fill (.atP τ) →
      L.wholeRunState relation errors fill (.atV (τ.snoc message))) ∧
    (∀ τ : AtV (L.wholeRunShape fill), L.wholeRunState relation errors fill (.atV τ) →
      cnt (fun challenge : τ.round.Chal =>
          ¬ L.wholeRunState relation errors fill (τ.snoc challenge)) ≤
        τ.err (errors.wholeRun fill)) ∧
    (∀ τ : Tr (L.wholeRunShape fill),
      L.wholeRunState relation errors fill (.full τ) ↔ (L.wholeRunOf fill τ).Concludes relation)

/-- States: a prover that has lost at the start reaches a transcript that is not bad for it with
probability at most the sum of the rounds' errors, each multiplied by the number of challenges that
are cleared to one; over uniform challenges, cleared. For every list of rounds, every strategy and
every clearing. (Where nothing is cleared: the plain sum, over uniform challenges.) -/
def probability_of_doomed : Prop :=
  ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop) (β : Type) (prover : Strat s β)
      (clearing : Clearing s) (toOne : Err s),
    clearing.AtMostToOne toOne → Doomed s ε bad →
    pr (unif (Rho s)) {ρ | ¬ bad (prover.run (clearing.cleared ρ)).1} ≤
      (Err.timesByRound toOne ε).sumOfProbabilities

/-- States: if every error is at most bound, as a probability, the sum is at most the number of
rounds times bound. -/
def sumOfProbabilities_le : Prop :=
  ∀ (s : Shape) (ε : Err s) (bound : ℝ≥0∞), Err.Below ε bound →
    ε.sumOfProbabilities ≤ (s.length : ℝ≥0∞) * bound

/-- States: **for every prover of the whole run**, the probability, over uniform challenges, cleared,
that the conclusion fails is at most the sum of the rounds' errors, each multiplied by the number of
challenges that are cleared to one. -/
def wholeRunSound_probability : Prop :=
  ∀ (Index Request : Type) (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
      (errors : L.RoundErrors) (fill : L.Fill) (β : Type) (prover : Strat (L.wholeRunShape fill) β)
      (clearing : Clearing (L.wholeRunShape fill)) (toOne : Err (L.wholeRunShape fill)),
    clearing.AtMostToOne toOne → L.WholeRunSound relation errors fill →
    pr (unif (Rho (L.wholeRunShape fill)))
        {ρ | ¬ (L.wholeRunOf fill (prover.run (clearing.cleared ρ)).1).Concludes relation} ≤
      (Err.timesByRound toOne (errors.wholeRun fill)).sumOfProbabilities

/-- States: **the definition gives the one statement**, every round of the whole run at most bound. -/
def wholeRunSound_of_indexKnowledgeSoundIOP : Prop :=
  ∀ (Index Request : Type) (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
      (offlineMarks : RoundSplits L.offline.shape) (offlinePlaces : ℕ) (linkMarks : RoundSplits L.link.shape)
      (linkPlaces : ℕ) (bound : ℝ≥0∞) (fill : L.Fill),
    L.late = none → 0 < L.maxBatchSize → 0 < offlinePlaces → 0 < linkPlaces →
    L.IndexKnowledgeSoundIOP relation offlineMarks offlinePlaces linkMarks linkPlaces bound →
    ∃ errors : L.RoundErrors,
      Err.Below (errors.wholeRun fill) bound ∧ L.WholeRunSound relation errors fill

end Spec

end Iop
