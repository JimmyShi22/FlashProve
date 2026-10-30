-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SlotsIn.lean: "the first n entries of a mask table lie inside the message's
ranges", as a test with code on four numbers. One definition, and theorems with their proofs.

Why. The law of the merge of the claims on the committed table (`merge_table_pinned`, Pin.lean)
asks of each of its two members that the positions of the entries that it reads lie inside the
member's ranges (`InMsg`, Johnson/Desc/Sound/World.lean): rows below its mask rows, places below the
length of a mask row's message. At the positions `posMask R` (MaskRow.lean) that is a fact on four
numbers, so it can be asked of the numbers that the planner gives.

Main names:
  `slotsInB n R rows ell`: for every j below n: j % 2 ^ R is below rows, and j / 2 ^ R below ell.
  `inMsg_iff_slots`: THE TEST SAYS NEITHER MORE NOR LESS THAN THE PREMISE: its yes at a shape's mask
    rows and at the length of its mask code's messages is "for every j below n the position
    `posMask R j` lies inside the ranges of a message of that shape".
  `inMsg_of_slots`: the direction that pays the premise, at a member x of the list of oracle
    messages: in the form in which `merge_table_pinned` takes it for the mask row (there n is the
    number of slots) and for the index masks.
  `slots_quick`: a yes without the walk over all j: 2 ^ R is at most rows, and n at most
    2 ^ R * ell.
  `slots_can_fail`: four inputs at which the test says no, each altered in one number.

Limits. Which member bears the mask row, how many slots there are, and that R is the number of bits
that number the rows of that member's mask table, are not said here. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.MaskRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (Codes OracleShape)
open VerifiableInference.Desc.Sound (Mem InMsg)

/-- Every entry below n of a mask table whose rows R bits number stands in a row below rows, at a
place below ell. -/
def slotsInB (n R rows ell : Nat) : Bool :=
  (List.range n).all fun j => decide (j % 2 ^ R < rows) && decide (j / 2 ^ R < ell)

/-- **The test says neither more nor less than the premise.** -/
theorem inMsg_iff_slots (cs : Codes) (sh : OracleShape) (n R : ℕ) :
    slotsInB n R sh.maskRows (cs.mask.getD sh.maskCode default).ell = true ↔
      ∀ j, j < n → InMsg cs sh (posMask R j).1 (posMask R j).2.1 (posMask R j).2.2 := by
  unfold slotsInB InMsg posMask
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, if_true]
  exact Iff.rfl

/-- **A yes of the test pays the law's premise at a member.** -/
theorem inMsg_of_slots (cs : Codes) (x : Mem) (n R : ℕ)
    (h : slotsInB n R (x.1.l.get x.2).1.maskRows
      (cs.mask.getD (x.1.l.get x.2).1.maskCode default).ell = true) :
    ∀ j, j < n → InMsg cs (x.1.l.get x.2).1 (posMask R j).1 (posMask R j).2.1 (posMask R j).2.2 :=
  (inMsg_iff_slots cs _ n R).1 h

/-- A yes without the walk over all j. -/
theorem slots_quick {n R rows ell : ℕ} (hr : 2 ^ R ≤ rows) (hn : n ≤ 2 ^ R * ell) :
    slotsInB n R rows ell = true := by
  unfold slotsInB
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro j hj
  exact ⟨lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos R)) hr,
    Nat.div_lt_of_lt_mul (lt_of_lt_of_le hj hn)⟩

/-- **The test can say no**: one entry more than the table has; three rows under two bits; one bit
too few for the places; no place at all. The first input, unaltered, passes. -/
theorem slots_can_fail :
    slotsInB 8 1 2 4 = true ∧ slotsInB 9 1 2 4 = false ∧ slotsInB 8 2 3 4 = false ∧
      slotsInB 8 0 2 4 = false ∧ slotsInB 8 1 2 0 = false := by
  decide

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.inMsg_iff_slots
#print axioms VerifiableInference.Desc.First.MergeLaw.inMsg_of_slots
#print axioms VerifiableInference.Desc.First.MergeLaw.slots_quick
#print axioms VerifiableInference.Desc.First.MergeLaw.slots_can_fail
