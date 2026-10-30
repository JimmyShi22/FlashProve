-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupEntryOfRecord.lean: AT THE BASE PROVER. The kind "lookup" (K3): WHAT IT HANDS IN
FOR ITS LOT: the field `k3` of `AtPublicFiles.TheSides.TheThirteen` (E2E/TheKOfRecord.lean, of other authors):
an `AtPublicFiles.TheSides.LotEntry (baseFilling files) Z G`. That record has three fields: `slot` (the lot of
lettered rows), `named` (a lot of the filling bears its name), `fit` (its rows' sides are the sides
of every lot of the filling that bears its name).

  `k3Entry`                          the entry: slot := `lookupSimulatorLotAtTheBaseProver`; the two
                                     laws are `lookupLotFitsTheKindsRowsAtTheBaseProver`'s
                                     (LookupLotIsAmongTheKindsRows.lean). No premise.
  `k3Entry_slot`                     the entry's lot, by name: by rfl
  `lookupLotIsLaidAtTheKOfRecord`    where the thirteen's field k3 is the entry, the lookups' lot is
                                     one of the lots of `theK E apart R`: the premise `laid` of the
                                     lookups' lines at `theGOfReturn`

Limits. A definition and two small laws on a list of lots. That the thirteen names are apart, the
other twelve entries and the later chains' rows are letters here: of other authors. Nothing here
says that the lot pays. THE PROOF FILE'S FIFTY PLACES ALONE. Nothing on any property of the
protocol.
-/
import E2E.TheKOfRecord
import E2E.Lookup.LookupLotIsAmongTheKindsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.Term
open AtPublicFiles.TheSides (LotEntry TheThirteen LaterRows theK mem_theK)

/-- **What the kind K3 hands in for its lot**, at the base filling. No premise. -/
def k3Entry (files : VerifierAndGoals.PublicFiles) (publicPart : Pub) (ground : Ground) :
    LotEntry (baseFilling files) publicPart ground where
  slot := lookupSimulatorLotAtTheBaseProver
  named := (lookupLotFitsTheKindsRowsAtTheBaseProver files publicPart ground).1
  fit := fun L isALot bearsTheName =>
    (lookupLotFitsTheKindsRowsAtTheBaseProver files publicPart ground).2 L isALot bearsTheName.symm

/-- The entry's lot, by name. -/
theorem k3Entry_slot (files : VerifierAndGoals.PublicFiles) (publicPart : Pub) (ground : Ground) :
    (k3Entry files publicPart ground).slot = lookupSimulatorLotAtTheBaseProver := rfl

/-- **The lookups' lot is among the lots of the K of record**, where the field k3 is the entry. -/
theorem lookupLotIsLaidAtTheKOfRecord {files : VerifierAndGoals.PublicFiles} {publicPart : Pub} {ground : Ground}
    (E : TheThirteen (baseFilling files) publicPart ground)
    (isTheEntry : E.k3 = k3Entry files publicPart ground)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (R : LaterRows (baseFilling files) publicPart ground) :
    lookupSimulatorLotAtTheBaseProver ∈ (theK E apart R).lots := by
  have laid := mem_theK (e := E.k3) (by simp [TheThirteen.entries]) apart R
  rw [isTheEntry] at laid
  exact laid

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.k3Entry
#print axioms AtPublicFiles.Lookup.k3Entry_slot
#print axioms AtPublicFiles.Lookup.lookupLotIsLaidAtTheKOfRecord
