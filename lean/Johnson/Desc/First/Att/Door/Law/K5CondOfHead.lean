-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CondOfHead.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION, WHERE THE VERIFIER's LIST OF ENTRY TESTS IS THAT OF Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean: "REST → CONDITION" FROM THE HEAD, ONE BOOL WITHOUT A LETTER, pads AND cells.**
It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean).
Of the condition's nine sentences: fence · oneShape are theorems from the head (fence_field | oneShape_field, Door/Law/K5HeadPaid.lean, over closed facts that Lean's kernel has walked) · sent · someMem are theorems from the
head's own test on the lookup arguments' seats (sent_all | someMem_all, Door/Law/K5SentOfK3.lean) · seatsPlan · shapesPlan follow from the Bool k5PlansB₂ (k5Tests_of_written, Door/Law/K5WrittenPlans.lean), whose two premises, the comparisons with
written values, the head gives (P5J.AtMg.pins, Johnson/P5T/FenceAtMg.lean) · pads and the two of cells are asked as they stand.
Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)
ONLY WHERE THE LIST OF Johnson/Desc/Laid/ProofAsks.lean HAS THE THIRTEEN TESTS OF ProofAsksFirstThirteenTests.lean AND THE HEAD OF Johnson/P5J/MgAtAll.lean HAS THE FIELD k3.

Main names:
  pins_at_head: under the head AtMg: madeRow Zp = true ∧ cutOf cF.blocksInOrder = cutFirstFull.
  **k5PlansB₂**: at each of the twelve groups seatsAllW g && shapesAllW g. No letter. k5PlansB₂_gives: its parts.
  **k5CondAt_of_head₂**: the head · the listed seats are L · k5PlansB₂ = true · pads · cells → K5CondAt h L.
IS IT EMPTY HERE? AN IMPLICATION. THAT k5PlansB₂ IS true IS NOT SHOWN IN LEAN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5HeadPaid
import Johnson.Desc.First.Att.Door.Law.K5CondOfWrittenK3
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.PlanWritten (madeRow cutFirstFull cut_of_row)
open P5J (AtMg AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The two comparisons with written values accept under the head.** -/
theorem pins_at_head {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) :
    madeRow Zp = true ∧ VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull :=
  ⟨h.pins.1, (cut_of_row h.pins.2).1⟩

/-- **The Bool at the written values that is left.** No letter. -/
def k5PlansB₂ : Bool := (List.range 12).all fun g => seatsAllW g && shapesAllW g

/-- What its accept says, part by part. -/
theorem k5PlansB₂_gives (h : k5PlansB₂ = true) : ∀ g, g < 12 → seatsAllW g = true ∧ shapesAllW g = true := by
  intro g hg
  unfold k5PlansB₂ at h
  have e := List.all_eq_true.1 h g (List.mem_range.2 hg)
  rwa [Bool.and_eq_true] at e

variable {x : Look.Place} {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}

/-- **REST → CONDITION: fence AND oneShape FROM THE HEAD; THE TWO TESTS ON THE PLAN FROM ONE BOOL WITHOUT A LETTER.** -/
theorem k5CondAt_of_head₂ {L : Laid} (hL : P5J.At.laid? Zp = some L) (hW : k5PlansB₂ = true) (pads : PadsAll h)
    (cells : ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx) : K5CondAt h L where
  head :=
    { fence := fence_field h
      pads := pads
      oneShape := oneShape_field h }
  each := fun g hg a x₁ ea hx =>
    { cells := cells g hg a x₁ ea hx
      tests := k5Tests_of_written h (pins_at_head h.toAtMg).1 (pins_at_head h.toAtMg).2 hx hL (k5PlansB₂_gives hW g hg).1
        (k5PlansB₂_gives hW g hg).2 (sent_all h hg hx) (someMem_all h hg hx) }

end H2K5.Door

#print axioms H2K5.Door.pins_at_head
#print axioms H2K5.Door.k5PlansB₂_gives
#print axioms H2K5.Door.k5CondAt_of_head₂
