-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/K2Entry.lean: the entry of the kind "the code switch" (K2) in the K of record
(E2E/TheKOfRecord.lean): its lot baseSimLot, that a lot of the base filling bears its name, and that it
has that lot's sides.

  k2Entry   the entry

Limits. A definition from AtFullSide/K2/BaseSlot.lean. Nothing here says that the lot pays: that is
kindShare_k2.
-/
import AtFullSide.K2.BaseSlot
import E2E.TheKOfRecord
import E2E.BaseMaker

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open AtPublicFiles.TheSides
open ProofFile.Honest.Term (baseFilling)

/-- **K2's entry.** -/
def k2Entry (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotEntry (baseFilling files) Z G where
  slot := baseSimLot
  named := baseSimLot_named
  fit := baseSimLot_fit Z G

end AtFullSide.K2

#print axioms AtFullSide.K2.k2Entry
