-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallsPaidOfLines.lean: the falls' measure of the online prover at the room of the
completeness error, with the debt of the marks of the kind K3 paid: theFallsArePaid with its premise
hK3 filled by lookupMarksPayTheFallsPremise.

  theFallsArePaid_of_lines   TheFallsArePaid from ShareLines alone

Limits. ShareLines is a premise. Nothing here says that a proof is accepted.
-/
import Johnson.P1K8R.FallsArePaid
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupMarksPayTheFallsPremise

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheSides AtPublicFiles.TheFalls
open VerifiableInference.Desc (Chain Block)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/-- **The falls have at most the room, from the stated shares' test alone.** -/
theorem theFallsArePaid_of_lines {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (lines : ∀ returned : OnlineReturn Z, onlineMaker Z = .ok returned →
      ShareLines returned.Z returned.G)
    (Relation : FullSizeMatrix → XF → Prop) : TheFallsArePaid Z Relation := by
  refine theFallsArePaid scope hr live lines ?_ Relation
  intro returned hM firstChain hC Bs _ A b b' Bt hsplit
  obtain ⟨Np, cF, D, r, L, -, hcF⟩ := return_laid live hM
  obtain rfl : firstChain = cF := Except.ok.inj (hC.symm.trans hcF)
  obtain ⟨xh, h⟩ := head_at_laid Z scope live L
  have hne : firstChain.blocksInOrder ≠ [] := by
    intro hnil
    have hlen : firstChain.blocksInOrder.length = 358 := by
      rw [← List.length_map (f := (·.place)), ProofFile.Honest.places_full h]
      exact ps_length
    rw [hnil] at hlen
    cases hlen
  exact ProofFile.Honest.K3.Term.lookupMarksPayTheFallsPremise h Bs
    (List.dropLast_append_getLast hne).symm A b b' Bt hsplit

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.theFallsArePaid_of_lines
