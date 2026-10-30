-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionEntry.lean: what the attention segments' own rounds (kind K5: the label of that sub-protocol
in the description) hand in for their lot at the base filling: k5Entry. It says nothing of what the lot
pays. No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.TheKOfRecord
import E2E.AttentionSlotAtTheFilling

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open ProofFile.Honest.Term (baseFilling)

/-- **What this kind hands in for its lot.** -/
def k5Entry (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) : LotEntry (baseFilling files) Z Gr :=
  ⟨attentionBaseLot, attention_named_base files, attention_fit_at_name files Z Gr⟩

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.k5Entry
