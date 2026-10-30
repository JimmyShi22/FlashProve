-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Later/AtFull.lean: the ten facts on the proof file's two later chains
(`LaterPaid`, Johnson/AtFull/Later/Paid.lean) at the library's written copy of the full-size public
files (`VerifierAndGoals.storedPublicFiles`, as Ladder/Stored.lean spells it). One call.

  `later_zFull`: under two closed facts on the layout file (its size; what the layout's reader
    returns), at whatever public part X₀ and planner's answer m the two makers return there:
    there are two seats A and B at which all ten hold.

By: `publicOfO_zFull_all` (Johnson/AtFull/Public/AtX0All.lean) gives six of the seven premises
of `later_paid` from the layout file's size; the seventh is bL.

Limits. hsz AND bL ARE PREMISES HERE. No Lean statement ties `VerifierAndGoals.storedPublicFiles` to the files of a
release's example folder; the example's weights are synthetic. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Later.Paid
import Johnson.AtFull.Public.AtX0All

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Later
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G.OfPlan (Made)
open _root_.AtFull.Top (ZqM)

/-- **The two later chains at the written copy of the full-size public files.** -/
theorem later_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (bL : OnBytes.Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some Johnson.AtFull.LayoutRead.LW)
    {X₀ : OnBytes.Model.Verify.Public} {m : Made}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      LaterPaid (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) A B := by
  obtain ⟨X₁, hX₁, F⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  have e : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX)
  rw [e] at F
  obtain ⟨hG, hA, hV, ha, P, hc⟩ := F
  exact later_paid hX hm P hG hA hV bL ha hc

end Johnson.AtFull.Later

#print axioms Johnson.AtFull.Later.later_zFull
