-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/ProofAtNameRows.lean: the last step from the seven fields of
`RowsOfProofFile` (Johnson/Goal/Skeleton/ProofFile.lean) to `ProofFileAt Z`, for theorems that state
the fields with `reqWithoutReply` (it sets a request's reply to 0) as the map `early`.

  `proofFileAt_of_rows`: its premise `rows` takes `early` as a variable, with a proof that
    early = reqWithoutReply. The reason: `early` appears in the type of Tl, and the map `early` of
    `dataAtFiles flashProveData Z` equals `reqWithoutReply` only by `early_of_live`
    (Johnson/Goal/Skeleton/ProofAtName.lean), where `protocolDataWellFormed` says yes, not by definition. A user
    removes the variable by `subst` and calls its own theorem. The other premises: `protocolDataWellFormed` says
    yes at Z, and `theProofRun (asDescriptionFiles Z) = (FP.pull instP).run`.
    `rows` asks the fields for every P and Tl, though the proof uses only those of
    `dataAtFiles flashProveData Z`: with `early` a variable these cannot be named. The theorems that end in the
    seven fields hold for every P and Tl, so this costs their users nothing.

Limits. This file only combines statements. It proves none of the seven fields, so it does not show
that the proof file's protocol is sound. That the equation on `theProofRun`
holds is not shown here; where it fails the theorem says nothing.

(Where this and lean/THEOREM.md differ, the page holds.)

-/
import Johnson.Goal.Skeleton.ProofAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc
open _root_.Run (ckP)
open OnBytes.Road OnBytes.Road.L5
open LPFD.Full (XF sBG saltG KF)
open PV.EntryFive (dsF xsF)

/-- **The seven fields with `early := reqWithoutReply` give `ProofFileAt Z`, where `protocolDataWellFormed` says
yes and `theProofRun (asDescriptionFiles Z)` is FP's run pulled back along instP.** -/
theorem proofFileAt_of_rows (Z : PublicFiles) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {XiP : Type}
    (FP : FileDescription XiP) (instP : XF × RecFull → XiP)
    (seat_proof_file : theProofRun (asDescriptionFiles Z) = (FP.pull instP).run)
    (rows : ∀ early : XF → XF, early = reqWithoutReply →
      ∀ {P : (threeProtocolsAtFullSize (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
          (dpZ Z) (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP dsF xsF (dataAtFiles flashProveData Z).dec
          (dataAtFiles flashProveData Z).G.rec₀ (recZ Z) (depthZ Z) early (saltG (dataAtFiles flashProveData Z).G)).Provers}
        (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).DK (dpZ Z)
          (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP dsF xsF (dataAtFiles flashProveData Z).dec
          (dataAtFiles flashProveData Z).G.rec₀ (recZ Z) (depthZ Z) early (saltG (dataAtFiles flashProveData Z).G)
          (KF (dataAtFiles flashProveData Z).DK (dpZ Z)) P),
        ∃ L : ProofLetters (innerCompilerInputAtFullSize Tl) (soundnessAnalysisDataAtFullSize Tl) (chainsP Z),
          RowsOfProofFile (r := innerCompilerInputAtFullSize Tl) (b := soundnessAnalysisDataAtFullSize Tl)
            (wholeDesc (ckP .two) ((dpZ Z).at aF) (front₀ (recZ Z)) (join₀ (recZ Z)) ByteArray.empty
              silP (dataAtFiles flashProveData Z).runP) L (soundnessAnalysisDataAtFullSize Tl).εs) :
    ProofFileAt Z := by
  have e : (dataAtFiles flashProveData Z).runP = (FP.pull instP).run := by
    rw [runP_the_at Z _ seat_proof_file, hl]
    rfl
  obtain ⟨L, R⟩ := rows (earlyZ Z) (early_of_live Z hl) ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)
  rw [eps_the Z] at R
  exact ⟨XiP, FP, instP, L, seat_proof_file,
    (congrArg (fun D => RowsOfProofFile (r := rZ Z) (b := bZ Z) D L _) (congrArg (descPr Z) e)).mp
      R⟩

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofFileAt_of_rows
