-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RidesAtFirst.lean: THE STATEMENT "RIDES PAST" (`RidesPastS`) AT ALL 75 BORDERS OF THE KIND K9, AT THE FIRST CHAIN's THREAD
OF THE ONLINE PART AS A NAMED TERM (`firstThread`, Honest/Thread/TheFirstThread.lean), at any return A of the maker and the head at that
return; and with it three of the five statements together at all 75.

  **`k9_ridesPastS_first`**   l < 25, every Said: `RidesPastS (firstThread h parts w) Said` at 14 l + `IM.nAt l` + 2, + 4, + 6. Three calls:
                            Honest/K9/RidesBat.lean, RidesEq.lean, RidesShut.lean, each general in the family of clauses of "keeps";
                            here at the thread's own family, whose clause at this kind gives this kind's clause by projection

Limits. The head at the return is a hypothesis. Nothing here says that any item holds at any state. That the thread's invariant
holds at any run is not proved here. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RidesBat
import Johnson.Desc.ProofFile.Honest.K9.RidesEq
import Johnson.Desc.ProofFile.Honest.K9.RidesShut
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **"Rides past" at this kind's 75 borders, at the first thread.** -/
theorem k9_ridesPastS_first (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (hl : l < 25) :
    RidesPastS (firstThread h parts w) Said (14 * l + IM.nAt l + 2) ∧
      RidesPastS (firstThread h parts w) Said (14 * l + IM.nAt l + 4) ∧
      RidesPastS (firstThread h parts w) Said (14 * l + IM.nAt l + 6) :=
  ⟨k9_ridesPastS_bat h.head A.H parts.script _ _ _ _ _ _ _ _ _ w Said (fun _ _ _ _ a => a.1.1.1.1.1) l hl,
    k9_ridesPastS_eq h.head A.H parts.script _ _ _ _ _ _ _ _ _ w Said (fun _ _ _ _ a => a.1.1.1.1.1) l hl,
    k9_ridesPastS_shut_exact h.head A.H parts.script _ _ _ _ _ _ _ _ w (fun _ _ _ a => a.1.1.1.1.1) _ Said l hl⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_ridesPastS_first
