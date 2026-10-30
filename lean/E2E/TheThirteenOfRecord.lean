-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheThirteenOfRecord.lean: THE ENTRIES OF RECORD, ONE FOR EACH OF THE BASE FILLING'S THIRTEEN LOTS, AS
EACH KIND'S HOUSE HANDED THEM IN.

  theThirteen            the value
  theThirteen_apart      their names are apart

Limits. Definitions on names and sides. Nothing here says that a lot pays. This file proves nothing
about completeness, soundness or zero knowledge.
-/
import AtFullSide.K13.EntriesForTheK
import AtFullSide.K2.K2Entry
import AtFullSide.K11.EntryOfRecord
import AtFullSide.K8.K8Entry
import AtFullSide.E2E.OutputHeadEntryOfRecord
import E2E.ReplyShareAtTheG
import E2E.AttentionEntry
import AtFullSide.K10.K10Entry
import AtFullSide.K12.K12Entry
import E2E.Lookup.LookupEntryOfRecord
import AtFullSide.K4.K4sEntryInTheK

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open ProofFile.Honest.Term (baseFilling)

/-- **The entries of record.** -/
def theThirteen (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    TheThirteen (baseFilling files) Z G where
  k1 := AtFullSide.K13.k1EntryAtBase files Z G
  k2 := AtFullSide.K2.k2Entry files Z G
  k7 := k7Entry files Z G
  k11 := AtFullSide.K11.k11Entry files Z G
  k13 := AtFullSide.K13.k13EntryAtBase files Z G
  k3 := AtPublicFiles.Lookup.k3Entry files Z G
  k4 := AtFullSide.K4.k4Entry files Z G
  k5 := k5Entry files Z G
  k6 := AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Entry files Z G
  k8 := ProofFile.Honest.K8.k8Entry files Z G
  k10 := ProofFile.Honest.K10.k10Entry files Z G
  k12 := ProofFile.Honest.K12.Sim2.k12Entry files Z G
  w := AtFullSide.K13.wEntryAtBase files Z G

/-- **Their names are apart.** -/
theorem theThirteen_apart (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((theThirteen files Z G).entries.map (·.slot.name)).Nodup := by
  have e : (theThirteen files Z G).entries.map (·.slot.name) =
      (baseFilling files).lots.map (·.name) := rfl
  rw [e]
  exact ProofFile.Honest.K10.baseNamesApart files

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.theThirteen
#print axioms AtPublicFiles.TheSides.theThirteen_apart
