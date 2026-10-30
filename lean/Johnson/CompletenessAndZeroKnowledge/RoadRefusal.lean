-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/RoadRefusal.lean: AT A REFUSED REQUEST THE PROVER HANDS OUT NO PROOF, AT THE LIBRARY'S slotSystem.

1.  From two things: the online prover withholds at every message of a request that is not served, and
    a refused request is not served, at the instance that it builds or at the fallback instance.
2.  The writer sends a proof without a string to the empty form, so that form is all the prover can
    return, under every hash function and at all coins.
3.  That compile is flashSlotF is not used here: it is one last step, in FinalRoadProof.lean.
-/
import Johnson.CompletenessAndZeroKnowledge.RoadAtSlot
import Johnson.CompletenessAndZeroKnowledge.BytesWriterNoProof
import VerifiableInference.Final.CompileHandsNoProof

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover VerifiableInference.OnPublicFiles
open VerifiableInference.AtEveryRequest (HandsOutNoProof requestOutcome)
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
local notation "ℍ" =>
  fun reading => AtRecs.side (honestSide
    ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers (settings reading))

/-- **At a refused request slotSystemF's prover hands out no proof, at a description.** -/
theorem handsOut_atSlot (outcome : ModelWeights s → AtEveryRequest.Request → AtEveryRequest.Outcome)
    (Served : (D.C Z).I → (D.C Z).X → Prop) (noProof : Form)
    (refuses : provers.RefusesUnserved Served) (writes : (𝕀).WritesNoProof noProof)
    (unserved : ∀ weights request, outcome weights request = .refused →
      ¬ Served (idx weights) (instOf (D.input Z c₀ m₀) x₀ request)) :
    HandsOutNoProof (slotSystemF D Z c₀ m₀ T ℍ firstBlockTest s idx x₀ Form parse write coinBound)
      (fun weights request => outcome weights request = .refused) (· = noProof) :=
  fun weights randomness request hash form refused hf =>
    support_ofUpload _
      (compile_prove_ends D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
        Served noProof refuses writes weights randomness request (unserved weights request refused))
      hash form ((PMF.mem_support_iff _ _).2 hf)

end AtADescription

variable (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings)

/-- The writer of the three files sends a proof without a string to the empty form. -/
theorem flash_writesNoProof : (flashProveAtFiles files settings honest).WritesNoProof noProofForm :=
  fun typed h => bytesWriterAt_noProof (FlashProve.dataAtFiles flashProveData files) typed h

/-- **At a refused request flashSlotF's prover hands out no proof.** -/
theorem road_handsOut_atSlot (Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop)
    (refuses : honest.provers.RefusesUnserved Served)
    (unserved : ∀ weights request, requestOutcome settings weights request = .refused →
      ¬ Served (backThe files settings weights)
        (instOf (flashProveDescription.input files allZeroDigest []) honest.fallbackInstance request)) :
    HandsOutNoProof (flashSlotF files settings honest)
      (fun weights request => requestOutcome settings weights request = .refused)
      (· = noProofForm) :=
  handsOut_atSlot flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq honest.fallbackInstance
    honest.provers honest.compiledSettings (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files) (requestOutcome settings) Served noProofForm refuses
    (flash_writesNoProof files settings honest) unserved

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.handsOut_atSlot
#print axioms VerifiableInference.Compilation.flash_writesNoProof
#print axioms VerifiableInference.Compilation.road_handsOut_atSlot
