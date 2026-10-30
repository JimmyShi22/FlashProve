-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/EntryOfRecord.lean: k11Entry: what the kind K11 hands in for the K of record
(E2E/TheKOfRecord.lean): its lot with its simulator, that a lot of the filling bears its name, and
that it has that lot's sides.
-/
import AtFullSide.K11.StandsAtTheG
import E2E.TheKOfRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K11
open ProofFile.Honest.Term (baseFilling)
open AtPublicFiles.TheSides (LotEntry)

/-- **K11's entry.** -/
def k11Entry (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    LotEntry (baseFilling files) Zq G :=
  ⟨k11LotAtBase, k11_named files, k11Lot_fit files Zq G⟩

end AtFullSide.K11

#print axioms AtFullSide.K11.k11Entry
