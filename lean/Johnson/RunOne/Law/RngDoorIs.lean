-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngDoorIs.lean: WHAT THE DOOR INTO THE KEY FILE's FIRST PROXIMITY TEST HANDS THE TEST. One statement with its proof, by the door's own text.
OBJECT. `enterAndAsk (enterRanges one) π` (Johnson/Desc/Key/Ranges.lean): it makes the test's state out of the verifier's state, then asks six things of it, and hands it on unturned.
USER. K12Back15.lean. Nobody else imports this file yet.
  door_is: where the door accepts and returns t: t = recD s (RngAtKeyD.lean): the verifier's statement, book and roots; its group's number; nothing passed; the mask that rides.
Limits. Nothing on what the six questions say. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.RngAtKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngAtKeyD
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState enterRanges)
open VerifiableInference.Desc.K12 (T12 P12)
open Johnson.RunOne.Law.RngAsked

/-- **The test's state behind the door is the one made of the verifier's state.** -/
theorem door_is (one : OneTime) (π : P12) (s : FirstState) (t : T12)
    (h : enterAndAsk (enterRanges one) π s = .ok t) : t = recD s := by
  unfold enterAndAsk at h
  obtain ⟨t1, h5, h6⟩ := bindE_ok h
  obtain ⟨_, _, h8⟩ := mapE_ok h6
  subst h8
  unfold rangesRecord at h5
  obtain ⟨l, h9, h10⟩ := mapE_ok h5
  obtain ⟨_, _, rfl⟩ := laidD_ok h9
  exact h10.symm

end Johnson.RunOne.Law.RngAtKeyD

#print axioms Johnson.RunOne.Law.RngAtKeyD.door_is
