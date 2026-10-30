-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompilerTheorems.lean: the two compiler theorems, as statements.

L is the protocol's type (Iop.HolographicProtocol; its fields are spelled out in Protocol.lean). offline: the proof
in the key file · link: the proof that ties a copy of the table to the first · online: a request's
proof.

1.  WHAT IS CLAIMED, OF WHAT: nothing is proved here; this file proves neither completeness nor
    zero knowledge of the protocol. Two statements are made of compileOverTypedOracles: the committer, prover
    and verifier that our commit-and-prove variant of the BCS transformation makes of ANY protocol,
    its three provers, a layout of hash queries and settings.
2.  COMPLETE: if the three provers are complete as interactive oracle proofs, the compiled verifier
    rejects the compiled committer and prover with probability at most (the three searches for
    nonces fail) + the provers' errors. This is of one fresh commitment and one proof; index and request are
    fixed before the oracles are drawn.
3.  INDEX PRIVACY (the compiled scheme's zero knowledge): if they are honest-verifier zero knowledge
    as interactive oracle proofs, then whatever ANY verifier sees of one commitment's life, with t
    queries and n proofs, is within a written error of what a NAMED simulator makes, which is built
    from the provers' three simulators and holds tables of a fixed index. Each request is picked
    from the verifier's view so far by a chooser that may know the index, among the requests that
    the prover serves at that index; the whole key is shown from the start.
4.  On the provers: completeness and zero knowledge as interactive oracle proofs, and one more, that
    the strings from which salts start are sent in the clear, at every request and every message
    at which the prover does not withhold. It is empty where salts start with constants; at the
    byte format's starts it is a condition on the provers. The premises on settings run over the provers' coins. Of the
    public premises, those for index privacy are shown at the protocol in CompilerPublicAtFiles.lean; those for
    completeness in PublicForCompletenessAtHome.lean.
5.  THE SIMULATOR IS GIVEN the public parameters, each request with its claimed output, and the hash
    queries, which it answers. It is given no index. It asks each table's seed as the committer
    does; it programs the oracle elsewhere.
6.  «HONEST VERIFIER» is a premise on the interactive oracle proofs alone. After hashing the
    verifier is ANY adversary within its queries, adaptive in requests.
7.  THE ERROR: (a copy is drawn too often) + the chance that a prover aborts for a reason that depends on its secrets, once for the
    offline run, once a copy, once a request + (the adversary's queries hit a salt, a chain value or a nonce's query):
    indexPrivacyError.
8.  NOT CLAIMED: more than one request a proof (at two, the statement with this simulator is false,
    by a reading) · masks derived from a short key (all coins are fresh and uniform) · requests
    that the prover does not serve (the statements at compile and above speak of them) · more than copies × sessionsPerCopy requests · a second commitment
    · a program. Where salts start with constants the compiled prover's salts are not the programs'.
9.  NOT COVERED: one hash function, the 256-bit commitment and verify: they are in
    CompilerTheoremsAtVerify.lean.
10. EACH IS WORTH LITTLE ALONE: both must stand AT ONE VALUE of provers and settings
    (Spec.compiled_both), with both numbers named.
-/
import Johnson.Face.Compiler
import VerifiableInference.Final.ZeroKnowledgeBeforeHashing
import Johnson.WholeKey.Statement
import Johnson.WholeKey.Complete
import Johnson.Prover.All.CompleteAsIOPForTheCompiler

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## 1 Completeness as interactive oracle proofs, at a wiring -/

variable {I X : Type}

/-- The errors of the three proofs. -/
structure CompletenessErrors where
  offline : ℝ≥0∞
  link : ℝ≥0∞
  online : ℝ≥0∞

variable {L : HolographicProtocol I X} {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}

/-- The library's three provers as a value of HonestProvers. -/
def HonestProvers.ofThreeProvers (Hs : ThreeProvers L) : HonestProvers L := ⟨Hs.T, Hs.Lk, Hs.B⟩

/-- The three run simulators in the library's record. -/
def RunSimulators.toSims (simulators : RunSimulators L) : Sims L :=
  ⟨simulators.offline, simulators.link, simulators.online⟩

/-- The work bits, read off the layout of queries. -/
def HashLayout.work (w : HashLayout L offlineRoundMarks linkRoundMarks) : PartsWork L :=
  partsWorkOfWire (aT := offlineRoundMarks) (aL := linkRoundMarks) w.queryLayout

/-- **Complete as interactive oracle proofs, at a layout**, over the provers' coins and the
challenges together. Served: the requests that the honest prover serves. -/
abbrev CompleteBeforeHashingAt (w : HashLayout L offlineRoundMarks linkRoundMarks)
    (provers : HonestProvers L) (Served : I → X → Prop) (E : CompletenessErrors) : Prop :=
  CompleteInParts L provers w.work w.seedQueries.num Served E.offline E.link E.online

/-! ## 2 The public conditions: on the protocol and the wiring; no prover, coin or simulator occurs
in them -/

/-- **Public, for index privacy.** The library's fields of this kind, at all seeds, in full words.
PROVED at the release's description, for public files in scope, at 44,040,191 columns and reads 62,
62, 62 and 64, up to 710,324 copies and 688,127 sessions a copy (CompilerPublicAtFiles.lean). Two
numbers of the settings occur: the copies and the search limits. -/
structure PublicForIndexPrivacy (w : HashLayout L offlineRoundMarks linkRoundMarks) (N : Budget) (furtherCopies
  sessionsPerCopy : ℕ)
    (limitOffline limitLink limitOnline : ℕ → ℕ) : Prop where
  /-- a table hides the index below N.columns opened columns, with its sample; the three verifiers'
  reads are counted -/
  tableHides : Hiop.Seeded.ReadsG L (fun _ => True) N.columns N.offlineReads N.linkReadsFirst
    N.linkReadsCopy N.onlineReads
  firstTableBudget : N.offlineReads + (furtherCopies + 1) * N.linkReadsFirst ≤ N.columns
  copyBudget : N.linkReadsCopy + sessionsPerCopy * N.onlineReads ≤ N.columns
  readsIgnoreNoncesOffline : ReadsFree (batTC L offlineRoundMarks) (wTC w.queryLayout).sh
  readsIgnoreNoncesLink : ReadsFree (batLC L linkRoundMarks) (wLC w.queryLayout).sh
  readsIgnoreNoncesOnline : ReadsFree L.onlineBatch (wBC w.queryLayout).sh
  layoutIsLawful : OKA w.queryLayout w.answerCode
  everyRoundHasAFormat : offlineRoundMarks.Fmt ∧ linkRoundMarks.Fmt ∧ L.onlineBatch.ann.Fmt
  noncesAreReadBackOffline : NoncesBack L.offline.shape offlineRoundMarks (wTC w.queryLayout).sh
    limitOffline 0
  noncesAreReadBackLink : NoncesBack L.link.shape linkRoundMarks (wLC w.queryLayout).sh limitLink
    0
  noncesAreReadBackOnline : NoncesBack L.onlineBatch.loc.shape L.onlineBatch.ann (wBC w.queryLayout).sh limitOnline
    0
  seedQueriesAreFirstTries : SeedPlain w.queryLayout w.seedQueries
  marksAreCoherent : offlineRoundMarks.Coherent ∧ linkRoundMarks.Coherent ∧ L.onlineBatch.ann.Coherent
  verifiersReadWhereTheySay : L.offline.IsLocal ∧ L.link.IsLocal ∧ L.onlineBatch.loc.IsLocal

/-- **Public, for completeness.** The laws on searches and wires are proved at every value of the
readings of the bounded form of the release's description, at its reference readings
(Johnson/Prover/At/HomeAt.lean). -/
structure PublicForCompleteness (w : HashLayout L offlineRoundMarks linkRoundMarks) (limitOffline limitLink limitOnline : ℕ
  → ℕ)
    : Prop where
  searches : LawFit w.queryLayout w.seedQueries limitOffline limitLink limitOnline
  layout : WiresFit w.queryLayout w.answerCode

/-! ## 3 The conditions on the settings: the compiler's own -/

/-- At the compiler's own honest side the laws on coins hold exactly where seven lengths of salt
starts do (within the window of rounds); the lengths that the format asks hold exactly where these
do at every round and five more clauses: the filler has the free bits' length; the three slots fit;
the salts have length 0 or the table fits its tree. -/
structure SettingsFit (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L) (s : CompiledSettings w
  provers) : Prop where
  coins : CoinsFit w.queryLayout w.compilerParameters (honestSide w provers s) s.coinNumbers
  lengths : SideFit w.queryLayout w.compilerParameters (honestSide w provers s).side

/-- **THE ONE PREMISE THAT TIES SETTINGS AND PROVERS**: the run values, of which salt starts are
made, stand in the plain parts of the honest run wherever the prover does not withhold. Neither
acceptance nor simulation gives it. -/
def RunValuesAreSent (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L) (s : CompiledSettings w
  provers)
    (inRange : I → Prop) : Prop :=
  RunVals (honestSide w provers s) inRange

/-- At plain starts it holds of every prover. -/
def Spec.runValues_plain : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (offlineRoundMarks : RoundSplits L.offline.shape) (linkRoundMarks : RoundSplits L.link.shape) (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers :
                                     HonestProvers L)
    (s : CompiledSettings w provers) (inRange : I → Prop), s.RunValues = Unit → RunValuesAreSent w provers s
      inRange

/-! ## 4 The simulator and the two errors, by name -/

/-- The numbers as the library's: the simulators' errors are 0 (the runs are exact off the stops),
and no seed is shut out. -/
def numbersOf (N : Budget) (sessionsPerCopy : ℕ) : NumsW :=
  ⟨N.columns, N.offlineReads, N.linkReadsFirst, N.linkReadsCopy, N.onlineReads, sessionsPerCopy, 0,
    0, 0,
    N.offlineStops, N.linkStops, N.onlineStops, 0⟩

/-- **THE COMPILED SIMULATOR**, built from the three run simulators: a reduction that does all hash
work (trees, salts, chains, searches, programmed answers) around the simulated game of the whole
view, which keeps tables of fixedIndex. -/
def compiledSimulator (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L) (s : CompiledSettings w
  provers)
    (simulators : RunSimulators L) (fixedIndex : I) (sessionsPerCopy : ℕ) :=
  simWholeKey w.queryLayout w.seedQueries w.answerCode w.fixedSample (honestSide w provers s).side
    simulators.toSims fixedIndex sessionsPerCopy (fun _ => True) Unit

/-- At t queries and n requests, with M = furtherCopies: pOver (M+1) sessionsPerCopy n +
(offlineStops + (M+1) · linkStops + n · onlineStops) + costTotal … t. -/
def indexPrivacyError (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L) (s : CompiledSettings w
  provers)
    (N : Budget) (sessionsPerCopy : ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  zetaW w.queryLayout w.seedQueries w.compilerParameters (honestSide w provers s) s.coinNumbers
    (numbersOf N sessionsPerCopy)

/-- Three times «no nonce within the limit passes» + offline + link + online. -/
def completenessError (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L)
    (s : CompiledSettings w provers) (E : CompletenessErrors) : ℝ≥0∞ :=
  alphaAll w.queryLayout s.searchLimitOffline s.searchLimitLink s.searchLimitOnline 0 0 E.offline
    E.link E.online

/-! ## 5 THE TWO COMPILER THEOREMS, for any protocol -/

namespace Spec

/-- **INDEX PRIVACY OF THE COMPILED SCHEME.** On the provers: zero knowledge as interactive oracle
proofs, and RunValuesAreSent. On the settings: the laws on coins. Public: PublicForIndexPrivacy. The
relation lies in Served. -/
def compiled_indexPrivacy : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (offlineRoundMarks : RoundSplits L.offline.shape) (linkRoundMarks : RoundSplits L.link.shape) (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers :
                                     HonestProvers L)
    (s : CompiledSettings w provers) (simulators : RunSimulators L) (inRange : I → Prop) (Served : I → X →
      Prop)
    (N : Budget) (sessionsPerCopy : ℕ) (R : ZKCP.Gen.RelPair I X Unit Unit) (fixedIndex : I),
    HonestVerifierZeroKnowledge w.work provers simulators inRange Served N →
    RunValuesAreSent w provers s inRange →
    CoinsFit w.queryLayout w.compilerParameters (honestSide w provers s) s.coinNumbers →
    PublicForIndexPrivacy w N s.furtherCopies sessionsPerCopy s.searchLimitOffline s.searchLimitLink
      s.searchLimitOnline →
    (∀ i x u, R.yes i x u → Served i x) →
    ZKCP.Gen.PrivacyOn R (compileOverTypedOracles w provers s) 1
      (compiledSimulator w provers s simulators fixedIndex sessionsPerCopy)
      (indexPrivacyError w provers s N sessionsPerCopy) inRange

/-- **COMPLETENESS OF THE COMPILED SCHEME**, from completeness over the provers' coins and the
challenges together. On the settings: the lengths. Public: PublicForCompleteness. -/
def compiled_complete : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (offlineRoundMarks : RoundSplits L.offline.shape) (linkRoundMarks : RoundSplits L.link.shape) (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers :
                                     HonestProvers L)
    (s : CompiledSettings w provers) (Served : I → X → Prop) (E : CompletenessErrors),
    CompleteBeforeHashingAt w provers Served E →
    SideFit w.queryLayout w.compilerParameters (honestSide w provers s).side →
    PublicForCompleteness w s.searchLimitOffline s.searchLimitLink s.searchLimitOnline →
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Served))
      (compileOverTypedOracles w provers s) 1 (completenessError w provers s E)

/-- **The same, from the stronger form**, in which each run fails rarely at every coin. -/
def compiled_complete_atEveryCoin : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (offlineRoundMarks : RoundSplits L.offline.shape) (linkRoundMarks : RoundSplits L.link.shape) (w : HashLayout L offlineRoundMarks linkRoundMarks)
    (provers : HonestProvers L) (s : CompiledSettings w provers) (Served : I → X → Prop)
    (E : CompletenessErrors),
    CompleteBeforeHashingAt w provers Served E →
    CompleteAtEveryCoin L provers w.work Served E.offline E.link E.online →
    SideFit w.queryLayout w.compilerParameters (honestSide w provers s).side →
    PublicForCompleteness w s.searchLimitOffline s.searchLimitLink s.searchLimitOnline →
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Served))
      (compileOverTypedOracles w provers s) 1 (completenessError w provers s E)

/-- **BOTH, AT ONE VALUE**: one w, one provers, one s, one Served, one reading of the work bits, by
the statement's form. -/
def compiled_both : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (offlineRoundMarks : RoundSplits L.offline.shape) (linkRoundMarks : RoundSplits L.link.shape) (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers :
                                     HonestProvers L)
    (s : CompiledSettings w provers) (simulators : RunSimulators L) (inRange : I → Prop) (Served : I → X →
      Prop)
    (N : Budget) (sessionsPerCopy : ℕ) (E :
      CompletenessErrors)
    (fixedIndex : I),
    CompleteBeforeHashingAt w provers Served E →
    HonestVerifierZeroKnowledge w.work provers simulators inRange Served N →
    RunValuesAreSent w provers s inRange →
    (∀ i x, Served i x → inRange i) →
    SettingsFit w provers s →
    PublicForCompleteness w s.searchLimitOffline s.searchLimitLink s.searchLimitOnline →
    PublicForIndexPrivacy w N s.furtherCopies sessionsPerCopy s.searchLimitOffline s.searchLimitLink
      s.searchLimitOnline →
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Served))
        (compileOverTypedOracles w provers s) 1 (completenessError w provers s E) ∧
      ZKCP.Gen.PrivacyOn (ZKCP.Special.toPair (ZKCP.languageRelation Served)) (compileOverTypedOracles w
        provers s) 1
        (compiledSimulator w provers s simulators fixedIndex sessionsPerCopy)
        (indexPrivacyError w provers s N sessionsPerCopy) inRange

end Spec
end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.CompletenessErrors
#print axioms VerifiableInference.Compilation.HashLayout.work
#print axioms VerifiableInference.Compilation.CompleteBeforeHashingAt
#print axioms VerifiableInference.Compilation.PublicForIndexPrivacy
#print axioms VerifiableInference.Compilation.PublicForCompleteness
#print axioms VerifiableInference.Compilation.SettingsFit
#print axioms VerifiableInference.Compilation.RunValuesAreSent
#print axioms VerifiableInference.Compilation.Spec.runValues_plain
#print axioms VerifiableInference.Compilation.numbersOf
#print axioms VerifiableInference.Compilation.compiledSimulator
#print axioms VerifiableInference.Compilation.indexPrivacyError
#print axioms VerifiableInference.Compilation.completenessError
#print axioms VerifiableInference.Compilation.Spec.compiled_indexPrivacy
#print axioms VerifiableInference.Compilation.Spec.compiled_complete
#print axioms VerifiableInference.Compilation.Spec.compiled_complete_atEveryCoin
#print axioms VerifiableInference.Compilation.Spec.compiled_both
