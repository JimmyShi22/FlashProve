-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/ParserAtTerm.lean: the parser at the plug, at the honest provers (E2E/TheHonestProver.lean).
-/
import AtFullSide.CompletenessAndZeroKnowledge.PlugAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest.Term (OnlineReturn)
open VerifiableInference.Desc (Chain)
open P5J
open Johnson.Face
open IntegerTransformer (Settings)

/-- Given by hand, as in E2E/TheHonestProver.lean. -/
local instance (priority := high) parserAtRunValueNonempty : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) parserAtPurseNonempty (l : List (ProofFile.Honest.Addr × ProofFile.Honest.Due)) : Nonempty (ProofFile.Honest.Purse l) :=
  ⟨ProofFile.Honest.Purse.any l⟩

section Left
variable (parts : (files : PublicFiles) → Parts files) (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)

/-- The strategies' law at the arms of the honest provers, under refusal. -/
def TermPrints : Prop :=
  ∀ description returned places firstChain,
    honestProvers files (parts files) = honestProversGivenDescriptions files (parts files) description returned places firstChain →
    ArmPrintsRefuse (settingsOfRead pp) files (Seam.servedAt files hr)
      (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files (parts files) description returned places firstChain))
      (Seam.servedAt files hr)
      (rvKey (parts files).book runValueBytes runValueBytes)
      (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2))

/-- What is asked of the parser at an honest part. -/
abbrev ParserAt (honest : HonestProversAndSettingsAtFiles files (settingsOfRead pp)) : Prop :=
  UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) (honestPartSide files (settingsOfRead pp) honest)
    (backThe files (settingsOfRead pp)) (Seam.servedAt files hr) (flashProveDescription.parse files) (bytesWriter files) sixTimes

/-- The same at an arm. -/
theorem parser_arm (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (description : OfflineDescription) (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl)
    (hPrint : ArmPrintsRefuse (settingsOfRead pp) files (Seam.servedAt files hr)
      (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files (parts files) description returned places firstChain))
      (Seam.servedAt files hr)
      (rvKey (parts files).book runValueBytes runValueBytes)
      (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2))) :
    ParserAt files hr
      (theHonestPartOf files (settingsOfRead pp) neverBuiltRequest
        ((HonestProvers.ofThreeProvers (honestProversGivenDescriptions files (parts files) description returned places firstChain)).refuseUnserved
          (Seam.servedAt files hr))
        ((formatStarts (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files (parts files) description returned places firstChain))
          (flashRounds files) (rvKey (parts files).book runValueBytes runValueBytes)
          (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2)) (linkRun, linkRun)
          (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀)
          (pvZ files (dataAtFiles flashProveData files).P)).underRefusal (Seam.servedAt files hr))
        (writtenLimits files) (flashProveRequestLeafSaltLayout files 40)) :=
  parser_generic files scope live
    (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files (parts files) description returned places firstChain))
    (Seam.servedAt files hr) (Seam.servedAt files hr)
    (rvKey (parts files).book runValueBytes runValueBytes) (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2))
    (fun _ => ⟨runValueBytes_size _, runValueBytes_size _⟩) (fun _ => ⟨runValueBytes_size _, runValueBytes_size _⟩)
    (sendsItsRunValues_term files (parts files) description returned places firstChain (flashRounds files)
      (linkRun, linkRun) fun _ => True)
    pr_coin_refused_le pr_coin_refused_le hPrint

/-- **The parser at the plug.** hPrint: the strategies' law, at each arm under refusal. -/
theorem term_parserUpTo (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (hPrint : TermPrints parts files hr) :
    ParserAt files hr (plugPartAt (termLetters parts) files (settingsOfRead pp) hr) := by
  have h := termStarts_elim files (parts files)
    (fun H s => ParserAt files hr (theHonestPartOf files (settingsOfRead pp) neverBuiltRequest
      ((HonestProvers.ofThreeProvers H).refuseUnserved (Seam.servedAt files hr)) (s.underRefusal (Seam.servedAt files hr))
      (writtenLimits files) (flashProveRequestLeafSaltLayout files 40)))
    (fun d r p c e => parser_arm parts files hr scope live d r p c (hPrint d r p c e))
    (honestProvers_arm_in_use files (parts files) scope live)
  exact h

end Left

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.TermPrints
#print axioms VerifiableInference.Compilation.parser_arm
#print axioms VerifiableInference.Compilation.term_parserUpTo
