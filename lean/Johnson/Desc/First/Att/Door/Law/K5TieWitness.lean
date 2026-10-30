-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TieWitness.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION: WHERE THE COMPARISON madeRow ACCEPTS, THE CONDITION's TEST tie, AT THE CLOSED INVERSE OF THE NUMBERING idxAt (Johnson/Desc/First/Look/K3IdxAt.lean), FOLLOWS FROM A BOOL
WHOSE ONLY LETTER IS THE GROUP's NUMBER.** It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean; K5CellsCond, Door/Law/K5RestCells.lean).
The condition asks for one inverse idx of the numbering for its two tests tie and one. The term idxAt D num l (Johnson/Desc/First/Look/K3IdxAt.lean) reads of what the planner sends the request's shape alone; so at the composed meaning's letters (P5J.At, Johnson/P5J/LettersAt.lean) it is the
term at the written values.
madeRow's accept IS A PREMISE HERE: the verifier's list of entry tests asks it: it stands in its prefix that Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean pins (asksAt2).

Main names:
  idxAt_shape: idxAt reads of D its field shape alone.
  **idx_written**: under the head AtMg and madeRow's accept, at every link l: idxAt (At.sentAt Zp) (At.num Zp) l = idxAt sentW (P5T.numOfPlan pseatsAllW) l.
  **tieWW g**: tieW g (Door/Law/K5TieWritten.lean) at that written inverse. No letter but g.
  **tie_of_writtenW | tie_of_writtenW'**: the head · madeRow's accept · g < 12 · the plan a · the place x₁ · tieWW g = true → the condition's field tie at idxAt (At.sentAt Zp) (At.num Zp) x₁.link | … (2 * g + 1).
IS IT EMPTY HERE? AN IMPLICATION. THAT tieWW g IS true IS NOT SHOWN IN THIS FILE: AT EVERY g BELOW 12 IT IS THE THEOREM tieWW_true (Door/Law/K5WrittenTrue.lean). A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5TieWritten
import Johnson.Desc.First.Look.K3IdxAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Sent msgIn bornAt idxAt candsAt lookAt)
open VerifiableInference.PlanWritten (madeRow)
open Meaning (linkTieB)
open P5J (AtMg AtMgA TS)

/-- The closed inverse of the numbering reads of what the planner sends the request's shape alone. -/
theorem idxAt_shape {D D' : Sent} (hs : D.shape = D'.shape) (num : ℕ → ℕ → ℕ) (l n : ℕ) : idxAt D num l n = idxAt D' num l n := by
  have e : ∀ b m, msgIn D l b m = msgIn D' l b m := msgIn_shape hs l
  unfold idxAt candsAt bornAt
  simp only [e, hs]

/-- **The test tie at the written values and the written inverse of the numbering.** Its only letter: the group's number. -/
def tieWW (g : ℕ) : Bool := tieW g (idxAt sentW (P5T.numOfPlan pseatsAllW) (2 * g + 1))

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The inverse of the numbering at P5J.At's letters is the one at the written values.** -/
theorem idx_written {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) (l : ℕ) :
    idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) l = idxAt sentW (P5T.numOfPlan pseatsAllW) l := by
  funext n
  rw [num_written h hm]
  exact idxAt_shape (sentAt_shape hm) _ l n

variable {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE CONDITION's FIELD tie AT THE CLOSED INVERSE, FROM A BOOL WHOSE ONLY LETTER IS g**: the inverse at the link's number 2 g + 1. -/
theorem tie_of_writtenW' (hm : madeRow Zp = true) {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (hW : tieWW g = true) :
    linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) (idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) (2 * g + 1)) x₁.link
      a.seam.tl = true := by
  rw [idx_written h.toAtMg hm]
  exact tie_of_written h hm hg ha hx hW

/-- The same with the place's own link in the inverse. -/
theorem tie_of_writtenW (hm : madeRow Zp = true) {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (hW : tieWW g = true) :
    linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) (idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) x₁.link) x₁.link
      a.seam.tl = true := by
  have t := tie_of_writtenW' h hm hg ha hx hW
  have e : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  rw [← e] at t
  exact t

end

end H2K5.Door

#print axioms H2K5.Door.idxAt_shape
#print axioms H2K5.Door.idx_written
#print axioms H2K5.Door.tie_of_writtenW'
#print axioms H2K5.Door.tie_of_writtenW
