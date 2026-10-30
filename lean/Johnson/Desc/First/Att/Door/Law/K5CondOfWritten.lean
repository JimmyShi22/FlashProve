-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CondOfWritten.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION: "REST → CONDITION"**: where two comparisons with written values accept, five of the condition's nine fields (fence · oneShape ·
seatsPlan · shapesPlan · sent) follow from ONE BOOL WITHOUT A LETTER; the other four sentences (pads · the two of cells · someMem) are asked as they stand. It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean).
The two comparisons (madeRow Zp · the written cut of the first chain) ARE PREMISES HERE, as in Door/Law/K5Written.lean: the verifier's list of entry tests asks them: they stand in its prefix that Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean pins (asksAt2).

Main names:
  **k5WrittenB**: fenceW && oneShapeW && at each of the twelve groups seatsAllW g && shapesAllW g. No letter.
  K5CondRest h: what is left with a letter: pads · cells · someMem, in the condition's own texts.
  sent_at | sent_of_written: the condition's field sent from seatsAllW g (sent_of_all, Door/Law/K5SentOfAll.lean).
  **k5CondAt_of_written**: the head · madeRow's accept · the written cut · the listed seats are L · k5WrittenB = true · K5CondRest h → K5CondAt h L.
IS IT EMPTY HERE? AN IMPLICATION. THAT k5WrittenB IS true IS NOT SHOWN: THIS TERM HAS BEEN EVALUATED NOWHERE. NO MEMBER OF K5CondRest IS SHOWN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5WrittenPlans
import Johnson.Desc.First.Att.Door.Law.K5WrittenShape
import Johnson.Desc.First.Att.Door.Law.K5SentOfAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls keptAt)
open VerifiableInference.Desc.First.FillSent (treesAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.PlanWritten (madeRow cutFirstFull)
open P5J (AtMg AtMgA TS)

/-- **The one Bool at the written values.** No letter. -/
def k5WrittenB : Bool := fenceW && oneShapeW && (List.range 12).all fun g => seatsAllW g && shapesAllW g

/-- What its accept says, part by part. -/
theorem k5WrittenB_gives (h : k5WrittenB = true) :
    fenceW = true ∧ oneShapeW = true ∧ ∀ g, g < 12 → seatsAllW g = true ∧ shapesAllW g = true := by
  unfold k5WrittenB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨h.1.1, h.1.2, fun g hg => ?_⟩
  have e := List.all_eq_true.1 h.2 g (List.mem_range.2 hg)
  rwa [Bool.and_eq_true] at e

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **What is left with a letter**, in the condition's own texts. -/
structure K5CondRest : Prop where
  /-- on the seats' places and the pads -/
  pads : PadsAll h
  /-- two tests of the lookup argument's own ledger, at an inverse of the numbering -/
  cells : ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
    lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx
  /-- for each member of the caller's list some member of the composed meaning's h.𝔇.ms is alike -/
  someMem : ∀ g, g < 12 → ∀ x₁ : Look.Place, lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
    ∀ i, ∃ y ∈ h.𝔇.ms, Alike y (⟨⟨sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link, seatAll h x₁⟩, i⟩ : Mem)

/-- The field sent at a letter i for the link's number. -/
theorem sent_at (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ} {L : Laid}
    (hL : P5J.At.laid? Zp = some L) (hW : seatsAllW g = true) (i : ℕ) (e : i = 2 * g + 1)
    (j : Fin (sigListCalls h.𝔇.sent h.𝔇.l3.rad i).length) : h.𝔇.l3.seat i false j.1 ∈ h.𝔇.pubD.N.sent (2 * g + 1) 0 := by
  subst e
  have hA : seatsAtW g L = true := by
    unfold seatsAllW at hW
    rw [← laid_written hm, hL] at hW
    exact hW
  rw [← seatsAll_written h.toAtMg hm hc g (treesAt Zp.made.p.built.links) (P5J.At.rad3At Zp Z.lay) L] at hA
  exact sent_of_all (sigListCalls (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) (2 * g + 1))
    (fun j => P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) (2 * g + 1) j.1) hA j

/-- **The condition's field sent, from a Bool without a letter.** -/
theorem sent_of_written (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ}
    {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {L : Laid} (hL : P5J.At.laid? Zp = some L)
    (hW : seatsAllW g = true) : ∀ i, seatAll h x₁ i ∈ h.𝔇.pubD.N.sent (2 * g + 1) 0 :=
  fun i => sent_at h hm hc hL hW x₁.link (VerifiableInference.OnPublicFiles.lookAt_link hx) i

variable {h}

/-- **REST → CONDITION.** -/
theorem k5CondAt_of_written (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {L : Laid}
    (hL : P5J.At.laid? Zp = some L) (hW : k5WrittenB = true) (R : K5CondRest h) : K5CondAt h L where
  head :=
    { fence := (fence_written h.toAtMg hm hc).trans (k5WrittenB_gives hW).1
      pads := R.pads
      oneShape := (oneShape_written h.toAtMg hm Z.lay).trans (k5WrittenB_gives hW).2.1 }
  each := fun g hg a x₁ ea hx =>
    { cells := R.cells g hg a x₁ ea hx
      tests := k5Tests_of_written h hm hc hx hL ((k5WrittenB_gives hW).2.2 g hg).1 ((k5WrittenB_gives hW).2.2 g hg).2
        (sent_of_written h hm hc hx hL ((k5WrittenB_gives hW).2.2 g hg).1) (R.someMem g hg x₁ hx) }

end

end H2K5.Door

#print axioms H2K5.Door.k5WrittenB_gives
#print axioms H2K5.Door.sent_of_written
#print axioms H2K5.Door.k5CondAt_of_written
