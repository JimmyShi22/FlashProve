-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/DoorRider.lean: the linear claim's second part ("K14, second
part", the first member of a proof file's last chain): A CLAUSE FOR THE LETTER rides OF THE LAST
CHAIN's THREAD (Honest/Thread/Riders.lean) THAT SPEAKS AT BORDER 0 ALONE: the eleven tests of
secondDoor (Honest/K14/SecondDoor.lean) are true at the state. One definition; no theorem.

Why. The member's accept follows from these eleven tests (second_acceptedS_last, SecondDoor.lean).
They speak of what the two earlier chains have left, which the last chain's invariant does not
otherwise hold. Laid as a clause of the rider at border 0, they are part of the invariant in front
of the member; whoever shows the invariant where the chain is entered shows them there, with both
earlier chains' ends at hand (second_door_thr, Honest/K14/SecondAtRun.lean). The clause ends at
border 0, so no member has to keep it.

What is not claimed. That the clause holds at any state. Nothing on completeness, soundness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondDoor
import Johnson.Desc.ProofFile.Honest.Thread.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃ P₁₄)

/-- **A clause of the rider that speaks at border 0 alone**: the eleven tests of secondDoor are true
at the state. -/
def doorRider (W : Type) (p : P₁₄) : RiderCl W S₃ :=
  ⟨0, 0, fun _ _ s => ok (secondDoor p s) = true⟩

end ProofFile.Honest.K14
