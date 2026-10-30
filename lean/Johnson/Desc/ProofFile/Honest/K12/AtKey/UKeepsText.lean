-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UKeepsText.lean: one value for the letter `keeps` of the key file's shared thread off the
members 1 to 8 (there the linear claim's own `keeps2` stands: `keepsAll`, Honest/K14/Thread2.lean). Each clause names one
member. A definition alone, over files of the description's own text: what it says at each member is UKeeps.lean's.

  `keepsKey`   member 0: the same state · member 9: the sub-protocol of the test on G_u, at the written place, has returned
               the second state at the first · member 10: the statement has grown and the sample rows stay · member 11:
               the same state · elsewhere nothing

Limits.
- A definition; no statement.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.AtPlan
import Johnson.HB.LLHARD.KB8.Written
import Johnson.Desc.Grows
import Johnson.Desc.K1.Law.SmpStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Block Grows)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open _root_.Desc.K14 (St)

/-- **The letter `keeps` at the key file's shared thread.** -/
def keepsKey (b : ℕ) (s s' : St) : Prop :=
  (b = 0 → s' = s) ∧
    (b = 9 → ∃ rs gs, (VerifiableInference.Desc.K12.Seat.onGu
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Johnson.KB8.laterPlacesFull.U) : Block T12 Unit)).decide s rs gs =
        .ok s') ∧
    (b = 10 → Grows s.st s'.st ∧ SmpStay s.st s'.st) ∧ (b = 11 → s' = s)

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.keepsKey
