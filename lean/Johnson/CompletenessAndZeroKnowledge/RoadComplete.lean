-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/RoadComplete.lean: THE ROAD'S COMPLETENESS HALF, AT THE LIBRARY'S slotSystem.

1.  At any description: the compiler's theorem at each value of the public reading, the library's
    passage to one hash function and to the commitment alone, and the passage to the argument system
    give completeness at slotSystem, from exactly the premises that this road spends, with the
    parser undoing the writer up to an error.
2.  At flashProveAtFiles: what is public is shown there, and RoadCompletePremises is the rest.
3.  That compile is flashSlotF is not used here: it is one last step, in FinalRoadProof.lean.
4.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the
    protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.RoadAtSlot
import VerifiableInference.Final.CompilerComplete
import Johnson.FrontRoad.CompleteUpTo
import Johnson.FrontRoad.FitsOf
import Johnson.FrontRoad.HonAt

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
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

set_option quotPrecheck false

local notation "𝕎" => (wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading
local notation "ℍ" =>
  fun reading => AtRecs.side (honestSide
    ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers (settings reading))

/-- **COMPLETENESS AT slotSystem, at a description**, from what this road spends. -/
theorem complete_atSlot (Served : (D.C Z).I → (D.C Z).X → Prop) (E : CompletenessErrors) (domain : ModelWeights s → List Token → List Token → Prop)
    (α γ : ℝ≥0∞)
    (t2 : ∀ d, CompleteBeforeHashingAt (𝕎 d) provers Served E)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (scope : InScope Z = true) (total : ∀ ck, ∃ code, T.encT ck = some code)
    (forCompleteness : ∀ d, PublicForCompleteness (𝕎 d) (settings d).searchLimitOffline
      (settings d).searchLimitLink (settings d).searchLimitOnline)
    (lengths : ∀ d, SideFit (𝕎 d).queryLayout (𝕎 d).compilerParameters (ℍ d))
    (coinRange : ∀ d, coinsRange (ℍ d) ∣ coinBound + 1)
    (undo : UndoUpTo D Z c₀ m₀ T ℍ idx Served parse write γ)
    (tie : ∀ w p o, domain w p o → ModelOutput s w p o →
      ∃ x, (D.input Z c₀ m₀).buildInstance (p, o) [] = some x ∧ Served (idx w) x)
    (below : ∀ d, completenessError (𝕎 d) provers (settings d) E ≤ α) :
    CompleteOn (slotSystem D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound) domain (α + γ) := by
  have hc : ZKCP.HasCompletenessError
      (ZKCP.languageRelation fun w (x : List Token × List Token) =>
        domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2)
      (frontId D Z c₀ m₀ T ℍ s idx x₀ Form parse write) (α + γ) :=
    frontIdCompleteUpTo D Z c₀ m₀ T ℍ s idx x₀ Form parse write pair Unit Unit
      (ZKCP.languageRelation Served) _ α γ noCoin asks once spare
      (fits_of_eq D Z c₀ m₀ T pair agree) reads scope undo total
      (fun d => completeness_mono
        (compiled_complete_holds _ _ _ _ _ _ provers (settings d) Served E (t2 d) (lengths d)
          (forCompleteness d))
        (below d))
      fun w x' hr => tie w x'.1 x'.2 hr.1 hr.2
  exact slot_completeOn_of_relationOn D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound domain
    (α + γ) noCoin coinRange hc

end AtADescription

section AtFlashProve
variable (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings)

/-- **What the completeness half of the road spends.** -/
structure RoadCompletePremises (l : RoadLetters files) (α γ : ℝ≥0∞) : Prop where
  complete : ∀ reading, CompleteBeforeHashingAt (layoutAtReading files settings honest reading)
    honest.provers l.Served l.errors
  parserUpTo : UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
    (honestPartSide files settings honest) (backThe files settings) l.Served (flashProveDescription.parse files)
    (bytesWriter files) γ
  lengths : ∀ reading, SideFit (layoutAtReading files settings honest reading).queryLayout
    (layoutAtReading files settings honest reading).compilerParameters
    (honestPartSide files settings honest reading)
  coinRange : ∀ reading, coinsRange (honestPartSide files settings honest reading) ∣ honest.coinBound + 1
  tie : ∀ w p o, CanServe settings w p o → ModelOutput settings w p o →
    ∃ x, (flashProveDescription.input files allZeroDigest []).buildInstance (p, o) [] = some x ∧ l.Served (backThe files settings w) x
  errorAtReading : ∀ reading, completenessError (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading) l.errors ≤ α
  errorsBelow : α + γ ≤ finalCompletenessError

variable {files settings honest} in
/-- The road's premises hold these, at the least error that bounds every reading's. -/
theorem RoadPremises.toComplete {zeroKnowledgeError : ℝ≥0∞} {l : RoadLetters files}
    (road : RoadPremises files settings honest zeroKnowledgeError l) :
    RoadCompletePremises files settings honest l
      (⨆ reading, completenessError (layoutAtReading files settings honest reading) honest.provers
        (honest.compiledSettings reading) l.errors) l.parserError :=
  haveI : Nonempty (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D := ⟨Prod.mk allZeroDigest []⟩
  ⟨road.complete, road.parserUpTo, fun reading => (road.settingsFit reading).lengths, road.coinRange,
    fun w p o hd hm => (road.tie w p o hd hm).imp fun _ h => ⟨h.1, h.2.1⟩,
    fun reading => le_iSup (fun reading => completenessError
      (layoutAtReading files settings honest reading) honest.provers
      (honest.compiledSettings reading) l.errors) reading,
    by
      rw [ENNReal.iSup_add]
      exact iSup_le road.completenessBelow⟩

/-- **Completeness on the requests that can be served, at flashSlot.** -/
theorem road_complete_atSlot (l : RoadLetters files) (α γ : ℝ≥0∞) (scope : InScope files = true)
    (road : RoadCompletePremises files settings honest l α γ) :
    CompleteOn (flashSlot files settings honest) (CanServe settings) (α + γ) :=
  complete_atSlot flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq honest.fallbackInstance
    honest.provers honest.compiledSettings honest.coinBound flashProveDescription.Form (flashProveDescription.parse files)
    (bytesWriter files) l.Served l.errors (CanServe settings) α γ
    road.complete (familyLaws_the files).noCoin (familyLaws_the files).asks
    (familyLaws_the files).once (familyLaws_the files).spare (familyLaws_the files).reads scope
    (familyLaws_the files).total
    (fun reading => flash_forCompleteness files settings honest.fallbackInstance _ _ _ reading)
    road.lengths road.coinRange road.parserUpTo road.tie road.errorAtReading

end AtFlashProve

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.complete_atSlot
#print axioms VerifiableInference.Compilation.RoadPremises.toComplete
#print axioms VerifiableInference.Compilation.road_complete_atSlot
