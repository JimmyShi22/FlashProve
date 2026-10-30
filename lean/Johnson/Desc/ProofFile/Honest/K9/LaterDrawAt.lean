-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/LaterDrawAt.lean: FOR THE ITEM "totalB": THE NAMED PREMISE `LaterDraw` OF THE
SMALLNESS TEST's HOUSE's `termsBack_four` (Honest/K8/TermsBackFour.lean): PAID, AT EVERY PLACE p: the draw's yes lays
"a ledger is open and is later than the ledger in front". A statement and its proof; no goal is stated.
  **`laterDraw_at`**   `ProofFile.Honest.K8.LaterDraw p`, at every p: by `draw_is` and `set_fork` (Honest/K9/LedgerOf.lean:
      the whole state behind a yes of the draw, written out) and the library's `later_of_same`: the draw turns none of
      the fields that "later" reads (by unfolding): "later" is met by a ledger that is the same in those five fields: it
      is no step on
No premise. On the verifier's own text.
GROUND: beside the sealed library, that house's files (Honest/K8/, Johnson/Desc/K8/Honest/), the frame's beneath them,
and our own.
WHAT IS NOT CLAIMED. That a draw says yes. No member; called by Honest/K9/TotalAtt.lean, TotalHead.lean and
TotalLay.lean. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf
import Johnson.Desc.ProofFile.Honest.K8.TermsBackFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **The draw's yes lays "later than the ledger in front".** -/
theorem laterDraw_at (p : Desc.K9.Where) : ProofFile.Honest.K8.LaterDraw p := by
  intro s a x t₁ ha h
  rw [draw_is p s t₁ x a ha h]
  exact ⟨_, set_fork s a _ ha, K9L.later_of_same _ _ rfl rfl rfl rfl rfl⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.laterDraw_at
