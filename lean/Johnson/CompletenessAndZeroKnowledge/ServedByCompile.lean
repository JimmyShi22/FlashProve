-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ServedByCompile.lean: the compiler's two statements on completeness and zero knowledge, at flashProveAtFiles.

1.  WHAT IS CLAIMED: from RoadPremises, completeOfCompile_holds and zeroKnowledgeOfCompile_holds themselves give completeness and zero knowledge of compile
    (flashProveAtFiles …) on the requests that can be served: their five premises at flashProveAtFiles, one by one.
2.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.FinalRoadProof
import Johnson.CompletenessAndZeroKnowledge.PublicAtFlash
import VerifiableInference.Final.CompilerAtVerifyProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles
open VerifiableInference.AtEveryRequest (WithinBudget)
open IntegerTransformer (Settings)

variable (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings)

/-- The road's premises are the premises of the two statements, at flashProveAtFiles. -/
theorem settings_of_road {ζ : ℝ≥0∞} {l : RoadLetters files} (road : RoadPremises files settings honest ζ l)
    (budget : WithinBudget (compile (flashProveAtFiles files settings honest)) honestQueryBudget) :
    SettingsPremises (flashProveAtFiles files settings honest) honestQueryBudget :=
  ⟨road.settingsFit, road.coinRange, budget⟩

theorem tie_of_road {ζ : ℝ≥0∞} {l : RoadLetters files} (road : RoadPremises files settings honest ζ l)
    (servedInRange : ∀ i x, l.Served i x → l.inRange i) :
    ModelTie (flashProveAtFiles files settings honest) l.inRange l.Served (CanServe settings) l.back :=
  ⟨road.range, servedInRange, road.tie⟩

theorem format_of_road {ζ : ℝ≥0∞} {l : RoadLetters files} (road : RoadPremises files settings honest ζ l) :
    ProversMeetTheFormat (flashProveAtFiles files settings honest) l.inRange l.Served l.parserError :=
  ⟨road.runValues, road.parserUpTo⟩

/-- **Completeness on the requests that can be served, by completeOfCompile_holds.** -/
theorem complete_by_compile (scope : InScope files = true) {ζ : ℝ≥0∞} {l : RoadLetters files}
    (road : RoadPremises files settings honest ζ l) (servedInRange : ∀ i x, l.Served i x → l.inRange i)
    (budget : WithinBudget (compile (flashProveAtFiles files settings honest)) honestQueryBudget) :
    CompleteOn (compile (flashProveAtFiles files settings honest)) (CanServe settings) finalCompletenessError := by
  have hC := road.toComplete
  have h := completeOfCompile_holds flashProveDescription files settings (backThe files settings) allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
    Prod.mk (familyLaws_the files).eq honest.fallbackInstance honest.provers honest.compiledSettings
    (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files) honestQueryBudget
    l.budget honest.onlineRunsPerCopy l.inRange l.Served l.errors (CanServe settings) l.back _ l.parserError
    road.complete
    (flash_publicPremises files settings honest scope road.copies road.sessions l.offlineStops l.linkStops l.onlineStops)
    (settings_of_road files settings honest road budget) (tie_of_road files settings honest road servedInRange)
    (format_of_road files settings honest road) hC.errorAtReading
  exact fun w p o hd hm => le_trans (h w p o hd hm) hC.errorsBelow

/-- **Zero knowledge on the requests that can be served, by zeroKnowledgeOfCompile_holds.** -/
theorem zeroKnowledge_by_compile (scope : InScope files = true) {ζ : ℝ≥0∞} {l : RoadLetters files}
    (road : RoadPremises files settings honest ζ l) (servedInRange : ∀ i x, l.Served i x → l.inRange i)
    (budget : WithinBudget (compile (flashProveAtFiles files settings honest)) honestQueryBudget)
    (fixedIndex : (flashProveDescription.C files).I) :
    ∃ error : ℕ → ℕ → ℝ≥0∞, (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ ζ) ∧
      ZeroKnowledgeOn (compile (flashProveAtFiles files settings honest)) (CanServe settings) error :=
  ⟨fun t n => roadError honest l (t + 1) n,
    fun asked replies ha hr => iSup_le fun reading => road.hidingBelow reading asked replies ha hr,
    (zeroKnowledgeOfCompile_holds flashProveDescription files settings (backThe files settings) allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      Prod.mk (familyLaws_the files).eq honest.fallbackInstance honest.provers honest.compiledSettings
      (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files) honestQueryBudget
      l.budget honest.onlineRunsPerCopy l.inRange l.Served l.simulators fixedIndex (CanServe settings) l.back
      (roadError honest l) l.parserError road.zeroKnowledge
      (flash_publicPremises files settings honest scope road.copies road.sessions l.offlineStops l.linkStops l.onlineStops)
      (settings_of_road files settings honest road budget) (tie_of_road files settings honest road servedInRange)
      (format_of_road files settings honest road)
      (fun reading t n => le_iSup (fun reading => indexPrivacyError (layoutAtReading files settings honest reading)
        honest.provers (honest.compiledSettings reading) l.budget honest.onlineRunsPerCopy t n) reading)).1⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.complete_by_compile
#print axioms VerifiableInference.Compilation.zeroKnowledge_by_compile
