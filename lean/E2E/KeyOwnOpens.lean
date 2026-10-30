-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnOpens.lean: the own test's declared openings against the three taken trees, at the written place. The first half
of the clause `opens` of `OwnAsks`. A closed line that can say no; its law at every job with that place.

  `opensFitB_KW`, `opensFit_KW`.

What stays open. `OldAt`: that the tables at hand hold the job's trees' columns. That is the tie of the tables of the two
earlier chains to the job's members, a debt of its own.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.K12.Law.PlacesKeyFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest.K12 (TestJob OpensFit opensFitB opensFit_of_B)
open H2K.Member (piKWFull)

theorem opensFitB_KW : opensFitB false piKWFull.nums.stages
    (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds [13, 22, 22]
    [.taken 0 0, .taken 0 5, .taken 1 1] 0 = true := by decide +kernel

/-- **At every job at the written place whose fresh table has come earlier.** -/
theorem opensFit_KW {W X : Type} (J : TestJob W X) (hJ : J.p = piKWFull) (hfr : J.fresh.isNone = false) :
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds [13, 22, 22]
      (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0)) 0 :=
  opensFit_of_B _ _ _ _ _ (by rw [hfr, hJ]; exact opensFitB_KW)

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.opensFitB_KW
#print axioms AtPublicFiles.KeyLastChain.opensFit_KW
