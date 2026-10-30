-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/RoadAtSlot.lean: THE ROAD'S ZERO-KNOWLEDGE HALF, AT THE LIBRARY'S slotSystem.

1.  At any description: the compiler's theorem at each value of the public reading, the library's
    passage to one hash function and to the commitment alone, and the passage to the argument system
    give zero knowledge at slotSystem, from exactly the premises that this road spends.
2.  At flashProveAtFiles: what is public is shown there, and RoadZeroKnowledgePremises is the rest.
3.  That compile is flashSlotF is not used here: it is one last step, in FinalRoadProof.lean.
4.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the
    protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.PublicAtFlash
import VerifiableInference.Compilation.FinalRoad
import Johnson.T3.CompiledPrivacy
import VerifiableInference.Final.RefuseUnserved
import Johnson.FrontRoad.FrontId
import Johnson.FrontRoad.PremAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch.Cms (NoRepeat IsOther)
open IntegerTransformer (Settings)

section AtADescription

variable (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.C Z).I) (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (pair : Digest → D.More → T.D) (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X)
  (provers : HonestProvers ((D.F Z).withProvers (D.P Z)))
  (settings : (reading : T.D) →
    CompiledSettings ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers)
  (firstBlockTest : (reading : T.D) → Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256
    (D.input Z c₀ m₀).queryLayout.K (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier (D.input Z c₀ m₀).protocol
                (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

set_option quotPrecheck false

local notation "𝕀" =>
  atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
local notation "𝕎" => (wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading
local notation "ℍ" =>
  fun reading => AtRecs.side (honestSide
    ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers (settings reading))

include firstBlockTest in
/-- **ZERO KNOWLEDGE AT slotSystem, at a description**, from what this road spends. -/
theorem zeroKnowledge_atSlot (N : Budget) (sessionsPerCopy : ℕ)
    (inRange : (D.C Z).I → Prop) (Served : (D.C Z).I → (D.C Z).X → Prop)
    (simulators : RunSimulators ((D.F Z).withProvers (D.P Z))) (fixedIndex : (D.C Z).I)
    (domain : ModelWeights s → List Token → List Token → Prop)
    (back : (D.C Z).X → List Token × List Token) (ζ : ℕ → ℕ → ℝ≥0∞)
    (t3 : ∀ d, HonestVerifierZeroKnowledge (𝕎 d).work provers simulators inRange Served N)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (forIndexPrivacy : ∀ d, PublicForIndexPrivacy (𝕎 d) N (settings d).furtherCopies sessionsPerCopy
      (settings d).searchLimitOffline (settings d).searchLimitLink (settings d).searchLimitOnline)
    (runValues : ∀ d, RunValuesAreSent (𝕎 d) provers (settings d) inRange)
    (coins : ∀ d, CoinsFit (𝕎 d).queryLayout (𝕎 d).compilerParameters
      (honestSide (𝕎 d) provers (settings d)) (settings d).coinNumbers)
    (coinRange : ∀ d, coinsRange (ℍ d) ∣ coinBound + 1)
    (range : ∀ w, inRange (idx w))
    (tie : ∀ w p o, domain w p o → ModelOutput s w p o →
      ∃ x, (D.input Z c₀ m₀).buildInstance (p, o) [] = some x ∧ Served (idx w) x ∧ back x = (p, o))
    (below : ∀ d t n, indexPrivacyError (𝕎 d) provers (settings d) N sessionsPerCopy t n ≤ ζ t n) :
    ZeroKnowledgeOn (slotSystem D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound) domain
      fun t n => ζ (t + 1) n := by
  have hp : ZKCP.HasStrongIndexPrivacyWith
      (ZKCP.languageRelation fun w (x : List Token × List Token) =>
        domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2)
      (frontId D Z c₀ m₀ T ℍ s idx x₀ Form parse write)
      (compiledSimulatorAtVerify 𝕀 simulators fixedIndex sessionsPerCopy back)
      fun t n => ζ (t + 1) n :=
    privacy_frontId D Z c₀ m₀ T ℍ s idx x₀ Form parse write back
      (ZKCP.languageRelation Served) _ (fun _ => ())
      (fun d => compiledSimulator (𝕎 d) provers (settings d) simulators fixedIndex sessionsPerCopy)
      ζ inRange noCoin asks once spare
      (fun d => privacyOn_mono
        (compiled_indexPrivacy _ _ _ _ _ _ provers (settings d) simulators inRange Served N
          sessionsPerCopy (ZKCP.Special.toPair (ZKCP.languageRelation Served)) fixedIndex (t3 d)
          (runValues d) (coins d) (forIndexPrivacy d) fun _ _ _ hy => hy)
        (below d))
      range (fun _ => rfl)
      fun w x' hr => by
        obtain ⟨x, hb, hy, hbk⟩ := tie w x'.1 x'.2 hr.1 hr.2
        have hb' : (D.input Z c₀ m₀).buildInstance x' [] = some x := hb
        have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
          unfold instOf
          rw [hb']
          rfl
        rw [hi]
        exact ⟨hy, hbk⟩
  exact slot_zeroKnowledgeOn_of_relationOn D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound domain _ _
    noCoin coinRange hp

end AtADescription

section AtFlashProve
variable (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings)

/-- The honest side at a value of the public reading. -/
abbrev honestPartSide (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) :=
  (honestSide (layoutAtReading files settings honest reading) honest.provers
    (honest.compiledSettings reading)).side

/-- **The library's argument system at flashProveAtFiles's honest part.** -/
abbrev flashSlot : ArgumentSystem :=
  slotSystem flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) (honestPartSide files settings honest)
    settings (backThe files settings) honest.fallbackInstance flashProveDescription.Form (flashProveDescription.parse files)
    (bytesWriter files) honest.coinBound

/-- **flashSlot with committer and prover by the third exit: the system that compile is.** -/
abbrev flashSlotF : ArgumentSystem :=
  slotSystemF flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) (honestPartSide files settings honest)
    (flashFirstBlockTest files) settings (backThe files settings) honest.fallbackInstance flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files) honest.coinBound

variable {files settings} in
/-- The least error that bounds every reading's. -/
def roadError (honest : HonestProversAndSettingsAtFiles files settings) (l : RoadLetters files) (t n : ℕ) :
    ℝ≥0∞ :=
  ⨆ reading, indexPrivacyError (layoutAtReading files settings honest reading) honest.provers
    (honest.compiledSettings reading) l.budget honest.onlineRunsPerCopy t n

/-- **What the zero-knowledge half of the road spends.** -/
structure RoadZeroKnowledgePremises (zeroKnowledgeError : ℝ≥0∞) (l : RoadLetters files) : Prop where
  zeroKnowledge : ∀ reading, HonestVerifierZeroKnowledge
    (layoutAtReading files settings honest reading).work honest.provers l.simulators l.inRange
    l.Served l.budget
  runValues : ∀ reading, RunValuesAreSent (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading) l.inRange
  coins : ∀ reading, CoinsFit (layoutAtReading files settings honest reading).queryLayout
    (layoutAtReading files settings honest reading).compilerParameters
    (honestSide (layoutAtReading files settings honest reading) honest.provers
      (honest.compiledSettings reading)) (honest.compiledSettings reading).coinNumbers
  copies : ∀ reading, (honest.compiledSettings reading).furtherCopies + 1 ≤ 710324
  sessions : honest.onlineRunsPerCopy ≤ 688127
  coinRange : ∀ reading, coinsRange (honestSide (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading)).side ∣ honest.coinBound + 1
  range : ∀ weights, l.inRange (backThe files settings weights)
  tie : TieOn flashProveDescription files allZeroDigest [] settings (backThe files settings) l.back (CanServe settings) l.Served
  refusesUnserved : honest.provers.RefusesUnserved l.Served
  refusedIsUnserved : ∀ weights request,
    VerifiableInference.AtEveryRequest.requestOutcome settings weights request = .refused →
    ¬ l.Served (backThe files settings weights)
      (instOf (flashProveDescription.input files allZeroDigest []) honest.fallbackInstance request)
  hidingBelow : ∀ reading asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
    indexPrivacyError (layoutAtReading files settings honest reading) honest.provers
      (honest.compiledSettings reading) l.budget honest.onlineRunsPerCopy (asked + 1) replies ≤
      zeroKnowledgeError

variable {files settings honest} in
/-- The road's premises hold these. -/
theorem RoadPremises.toZeroKnowledge {zeroKnowledgeError : ℝ≥0∞} {l : RoadLetters files}
    (road : RoadPremises files settings honest zeroKnowledgeError l) :
    RoadZeroKnowledgePremises files settings honest zeroKnowledgeError l :=
  ⟨road.zeroKnowledge, road.runValues, fun reading => (road.settingsFit reading).coins, road.copies,
    road.sessions, road.coinRange, road.range, road.tie, road.refusesUnserved,
    road.refusedIsUnserved, road.hidingBelow⟩

/-- **Zero knowledge on the requests that can be served, at flashSlot.** -/
theorem road_zeroKnowledge_atSlot (zeroKnowledgeError : ℝ≥0∞) (l : RoadLetters files)
    (scope : InScope files = true) (fixedIndex : (flashProveDescription.C files).I)
    (road : RoadZeroKnowledgePremises files settings honest zeroKnowledgeError l) :
    ZeroKnowledgeOn (flashSlot files settings honest) (CanServe settings)
      fun t n => roadError honest l (t + 1) n :=
  zeroKnowledge_atSlot flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq honest.fallbackInstance
    honest.provers honest.compiledSettings (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files) l.budget honest.onlineRunsPerCopy l.inRange l.Served l.simulators fixedIndex
    (CanServe settings) l.back (roadError honest l) road.zeroKnowledge
    (familyLaws_the files).noCoin (familyLaws_the files).asks (familyLaws_the files).once
    (familyLaws_the files).spare
    (fun reading => flash_forIndexPrivacy files settings honest.fallbackInstance scope _ _
      (road.copies reading) road.sessions l.offlineStops l.linkStops l.onlineStops _ _ _ reading)
    road.runValues road.coins road.coinRange road.range road.tie
    (fun reading t n => le_iSup (fun reading => indexPrivacyError
      (layoutAtReading files settings honest reading) honest.provers
      (honest.compiledSettings reading) l.budget honest.onlineRunsPerCopy t n) reading)

end AtFlashProve

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledge_atSlot
#print axioms VerifiableInference.Compilation.roadError
#print axioms VerifiableInference.Compilation.RoadPremises.toZeroKnowledge
#print axioms VerifiableInference.Compilation.road_zeroKnowledge_atSlot
