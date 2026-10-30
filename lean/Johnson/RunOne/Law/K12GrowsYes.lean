-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12GrowsYes.lean: A YES OF THE KEY FILE's RANGES' TEST's BLOCK LEAVES A STATEMENT THAT HAS GROWN OUT OF THE ONE IN FRONT: WITH NO PREMISE BUT THE YES. Two statements with proofs.
OBJECT. `Key.rangesTest laid back N` at any state and any type of claims; and at the key file's own two doors.
USER. Other files: for "the first chain's blocks keep Grows" without a premise on the plan.
LETTERS. σ Cl st laid back N: free; hin | hout: the two doors hand the statement on. one N: free.

  seat_grows_yes: seat_grows_cl (Johnson/RunOne/Law/RngAnyCl.lean) WITHOUT its premise on the plan.
  keyD_grows_yes: keyD_grows (Johnson/RunOne/Law/RngAtKeyD.lean) WITHOUT its premise on the plan.
BY: k12_grows (H2K.Out.k12_grows, Johnson/Desc/K12/Law/GrowsTest.lean: no premise but the yes), in the place of K12Grows.k12_grows (which asks the place's early and answers = 1 besides: THE LESSER TWIN: it yields); else seat_grows' own lines (K12Grows.lean).
Limits. `Grows` says nothing on rows, pads or ledgers. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.RngAtKeyD
import Johnson.Desc.K12.Law.GrowsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12GrowsYes
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)
open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngAnyCl
open VerifiableInference.Desc (Block Grows)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)

/-- Of the block at any state and any type of claims. -/
theorem seat_grows_yes {σ Cl : Type} (st : σ → Statement) {laid : σ → Except String RangesLaid}
    {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}
    (hin : ∀ s l, laid s = .ok l → l.d.st = st s) (hout : ∀ s t s', back s t = .ok s' → st s' = t.st) :
    ∀ s rs gs s', (rangesTest (Cl := Cl) laid back N).decide s rs gs = .ok s' → Grows (st s) (st s') := by
  intro s rs gs s' h
  obtain ⟨t0, tE, h1, _, hd, hbk⟩ := decide_ok (yes_unit h)
  unfold rangesRecord at h1
  obtain ⟨l, hl, rfl⟩ := mapE_ok h1
  have g := H2K.Out.k12_grows (rangesParams N) _ tE rs gs hd
  rw [hout s tE s' hbk, ← hin s l hl]
  exact g

/-- **At the key file's own two doors.** -/
theorem keyD_grows_yes (one : OneTime) (N : H2U.PlaceNums) :
    ∀ s rs gs s', (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s' →
      Grows s.d.st s'.d.st :=
  fun s rs gs s' h => seat_grows_yes (fun s : FirstState => s.d.st) RngAtKeyD.hin RngAtKeyD.hout s rs gs s' h

end Johnson.RunOne.Law.K12GrowsYes

#print axioms Johnson.RunOne.Law.K12GrowsYes.seat_grows_yes
#print axioms Johnson.RunOne.Law.K12GrowsYes.keyD_grows_yes
