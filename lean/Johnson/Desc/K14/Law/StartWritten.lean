-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/StartWritten.lean: THE ROUND AT WHICH THE MEMBERS' BATCHING STARTS, AT THE
WRITTEN PLAN OF THE FULL SIZE, IS 48270: BY A LAW AND TWO WALKS OF THE KERNEL. Written Z x's payer
written_of_pins (Johnson/HB/LLHARD/WrittenOfPins.lean) bore one closed sentence as a premise,
"start": (cutOf ‹the written entries›).map startOf = some 48270: true by a run; Lean's kernel does
not walk cutOf at 48,293 names. HERE IT IS NO PREMISE ANY MORE.

  startOf_front      startOf of a table front ++ endCuts … without the step "M.0.call" in front is
                     the sum of the front's rounds (rounds_before_call).
  startOf_written    **cutOf ‹the written entries› = some cs → startOf cs = 48270**: front_of_base
                     (Johnson/Desc/First/Driver/CutFront.lean) at p := 48268, with the two closed
                     facts base_not_before | base_not_after (Johnson/HB/LLHARD/K13StartFacts.lean:
                     the name "BASE lambda" stands neither in front of round 48268 nor behind it).
  written_of_pins'   **Written Z x without the premise "start"**: that cutOf returns a table is what
                     pubBy's own yes says (pubBy_cuts).
What is not claimed. That cutOf returns a table at the written entries WITHOUT pubBy's yes: it has
not been walked in the kernel. written_of_pins' other premises stand. No soundness of a verifier.

-/
import Johnson.Desc.First.Driver.CutFront
import Johnson.HB.LLHARD.WrittenOfPins
import Johnson.HB.LLHARD.K13StartFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First (Cut cutOf endCuts NoM takes rounds_before_call front_of_base)
open VerifiableInference.Desc.K1 (realSized)
open H2K.Sizes (AtFull)

theorem startOf_front {front : List Cut} (hN : NoM front) (pl q b : ℕ) :
    startOf (front ++ endCuts pl q b) = takes front := by
  obtain ⟨h1, h2⟩ := rounds_before_call hN pl q b
  unfold startOf
  rw [if_pos h1, h2]
  rfl

/-- **The start at the written plan.** -/
theorem startOf_written {cs : List Cut}
    (h : cutOf (dryProofFull.1.map (·.1.entry)) = some cs) : startOf cs = 48270 := by
  obtain ⟨front, pl, q, b, rfl, hN, ht⟩ := front_of_base dryProofFull.1 (·.1.entry) h 48268
    base_not_before base_not_after
  rw [startOf_front hN, ht]

/-- **Written at the description's own public part, without the premise "start".** -/
theorem written_of_pins' {made : ByteArray → ByteArray → ByteArray → Except String OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubBy made st pol lay KL = .ok Z) (hA : AtFull Z.p.chains.made)
    (h1 : Z.plans.1 = dryProofFull.1.map (·.1.entry))
    (h2 : Z.plans.2.1 = dryProofFull.2.1.map (·.1.entry)) {x : LinSized}
    (hx : realSized = some (x, codesFull2))
    (rows : Z.first.pendingRows = 13) (lin : Z.first.lin = x.shape)
    (slots : 2 ^ Z.first.binding.logLeaves ≤ 64)
    (codes : Z.p.chains.made.sized.proof.codes = codesFull2)
    (shape : Z.p.chains.made.sized.proof.batch.shape = x.shape)
    (before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ []) :
    Written Z x := by
  have hc := pubBy_cuts hZ
  rw [h1] at hc
  refine written_of_pins hZ hA h1 h2 hx rows lin slots ?_ codes shape before
  rw [hc]
  exact congrArg some (startOf_written hc)

end Desc.K14.Law

#print axioms Desc.K14.Law.startOf_front
#print axioms Desc.K14.Law.startOf_written
#print axioms Desc.K14.Law.written_of_pins'
