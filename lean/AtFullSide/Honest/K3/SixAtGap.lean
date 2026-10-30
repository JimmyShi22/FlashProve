-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/SixAtGap.lean: the kind "lookup" (K3): the library's six statements on what the
two lookups of a link ask of the public data (`SixAt`, Johnson/AtFull/K3X/SixAt.lean) do not feel
the acceptance policy's three numbers; so, under the library's one hypothesis at the full size
(`P5J.AtMgA`, "the head"), they hold at each of the 25 links at the second of the goals' two named
sets of public files (`VerifierAndGoals.zGap`) too, and so at both. Four theorems; no definition; nothing is
evaluated here.

What is shown.
  `lookAt_withPol`: `lookAt` (Johnson/Desc/First/Look/LookAt.lean) at `X.withPol C theta cap`
  (OnBytes/Tie/PlanAtPolicy.lean) is `lookAt` at X: it reads nothing of the scan of the parameter
  file, and of the head's shape two fields that `withPol` keeps. `six_withPol`: the six statements
  at X give the six at `X.withPol C theta cap`. `six_head_zGap`: under the head at `VerifierAndGoals.zGap`:
  the six at each link below 25, at the head's own public part. `six_head_named`: the same at every
  Z with `VerifierAndGoals.NamedFiles Z`.

How the proof of the third goes. A member of the head at `VerifierAndGoals.storedPublicFiles` (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean) gives the maker's return X₀ there. The library's
`LPFPol.gap_of_full` (Johnson/LPFPol/PublicInScope.lean): at `VerifierAndGoals.zGap` the maker returns
`X₀.withPol 25856 512 1`. The head's own field pubOne at `VerifierAndGoals.zGap` says that it returns Zp.p.X:
so the two are one. Of the member at `VerifierAndGoals.storedPublicFiles` nothing is taken but that return, which is the
same at every member.

Hypotheses that remain. `h`: in `six_withPol` the six at X; in the last two the head, at every
member. `hZ`: Z is one of the two named sets.

Why here. `headMember_zFull` and SixAtHead.lean lie in this side library.

Users. FitsAtSites.lean beside it.

Limits, after those of the files called, which all hold here. Two named sets of public files, at the
full size alone. `SixAt` compares with written values: the verifier does not ask it.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.SixAtHead
import AtFullSide.Top.HeadMemberAtFull
import Johnson.LPFPol.PublicInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open VerifiableInference.Desc.First.Look (lookAt)
open Johnson.AtFull.K3X (SixAt)

/-- The public record's place of a lookup does not feel the acceptance policy's three numbers. -/
theorem lookAt_withPol (X : OnBytes.Model.Verify.Public) (C theta cap i : Nat) (d : Bool) :
    lookAt (X.withPol C theta cap) i d = lookAt X i d :=
  rfl

/-- Nor do the library's six statements at a link. -/
theorem six_withPol {X : OnBytes.Model.Verify.Public} {i : Nat} (C theta cap : Nat)
    (h : SixAt X i) : SixAt (X.withPol C theta cap) i :=
  ⟨h.calls, h.digits, h.laid, h.key, h.quiet, h.caller⟩

/-- **Under the head at the second named set of public files the six statements hold at each of the
25 links, at the head's own public part.** -/
theorem six_head_zGap {D r Zp Np cF x}
    (h : P5J.AtMgA OnBytes.secondHashFunction VerifierAndGoals.zGap D r Zp Np cF x) :
    ∀ i, i < 25 → SixAt Zp.p.X i := by
  intro i hi
  obtain ⟨_, _, Zp0, Np0, cF0, x0, h0⟩ := AtFullSide.Top.headMember_zFull
  have e0 : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol
      VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok Zp0.p.X := by
    rw [VerifiableInference.PlanWritten.publicOfO_older]
    exact h0.toAtMg.pubOne
  have e1 := LPFPol.gap_of_full e0
  rw [VerifiableInference.PlanWritten.publicOfO_older] at e1
  have hlay : VerifierAndGoals.zGap.lay = VerifierAndGoals.storedPublicFiles.lay := by
    unfold VerifierAndGoals.zGap
    dsimp only
  have e2 := h.toAtMg.pubOne
  rw [hlay] at e2
  have e : Zp.p.X = Zp0.p.X.withPol 25856 512 1 := Except.ok.inj (e2.symm.trans e1)
  rw [e]
  exact six_withPol 25856 512 1 (six_head_zFull h0 i hi)

/-- **At each of the goals' two named sets.** -/
theorem six_head_named {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.NamedFiles Z) {D r Zp Np cF x}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ i, i < 25 → SixAt Zp.p.X i := by
  rcases hZ with rfl | rfl
  · exact six_head_zFull h
  · exact six_head_zGap h

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.lookAt_withPol
#print axioms AtFullSide.Honest.K3.six_withPol
#print axioms AtFullSide.Honest.K3.six_head_zGap
#print axioms AtFullSide.Honest.K3.six_head_named
