-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/ProofAsksForms.lean: THE TWO PINS' ROWS OF THE ENTRY TESTS' SECOND PART
(ProofAsks.lean), IN THE FORM IN WHICH THEIR FILES' LAWS TAKE
THEM. A law file.

  atFull_some     a row of the full size alone, at a plan that is made: «not at the full size's key,
                  or the
                  test accepts», written out with the key test itself: by rfl
  asks_made_at    where every entry test accepts, at the maker's own public plan Z:
                  (!decide (keyOfScan Z.p.X.P = fullKey) || madeRow Z) = true: the premise of
                  `pinnedAt_of_row` (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) to the letter:
                  at every key, with no word on the scope
  asks_cut_at     the like for `cutRow F Z`

Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofAsksLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference
open VerifiableInference.Desc (FileDescription)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **The row's form at a plan that is made.** -/
theorem atFull_some (Z : ProofFile.Pub) (t : ProofFile.Pub → Bool) :
    Desc.Door.atFull (some Z) t =
      (!decide (PlanWritten.keyOfScan Z.p.X.P = PlanWritten.fullKey) || t Z) := rfl

/-- **The first pin's row, at the maker's own public plan, in the form `pinnedAt_of_row` takes.** -/
theorem asks_made_at {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    (!decide (PlanWritten.keyOfScan Z.p.X.P = PlanWritten.fullKey) ||
      PlanWritten.madeRow Z) = true := by
  have h1 := asks_made h
  rw [Desc.Door.planOf_some.2 hZ] at h1
  exact h1

/-- **The second pin's row, the like.** -/
theorem asks_cut_at {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    (!decide (PlanWritten.keyOfScan Z.p.X.P = PlanWritten.fullKey) ||
      PlanWritten.cutRow F Z) = true := by
  have h1 := asks_cut h
  rw [Desc.Door.planOf_some.2 hZ] at h1
  exact h1

end LPFD

#print axioms LPFD.atFull_some
#print axioms LPFD.asks_made_at
#print axioms LPFD.asks_cut_at
