-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RidesSortsK9.lean: WHICH ITEMS PASS OVER THE BATCHING AND OVER "THE ONE EQUATION". By Lean's kernel, at each of the 25 segments: every
item that is open at the member and that its row neither shuts nor owes is: unmarked, pinW, pile, pinI, the claim on the weights of that
segment, a class of rows of that segment other than "equation", or a part of `parts4` of a later segment; at "the one equation" also a
pin of that segment.

  `batSort`, `eqSort`        the tests on one item at one segment
  `k9RowTest`              an item passes a test, or the member's row shuts or owes it
  **`bat_open_sorts`**, **`eq_open_sorts`**   the kernel's answers at the 25 segments
  `bat_rows_bite`, `bat_wo_bites`, `eq_pins_bite`, `eq_rows_bite`   controls: with the rows, the claim on the weights or the pins struck from the test, the
                          answer turns
  **`bat_open_cases`**, **`eq_open_cases`**   the same at one segment and one item
  **`eq_open_in`**           what is open in front of "the one equation" by the thread's count (`fwdOpen`) is open there by the table's (`P5J.oAt`)

Limits. Closed facts on the written lists. Nothing on what any item says.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows
import Johnson.P5J.MeansQ
import Johnson.P5J.LettersAt
import Johnson.P5J.K10Open
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc.First (Item RowClass)
open ProofFile.Honest

/-- True of the sorts of item that pass over the batching of segment l. -/
def batSort (l : Nat) : Item → Bool
  | .unmarked | .pinW | .pile | .pinI => true
  | .row m c => m == l && c != .equation
  | .wo m => m == l
  | .constr m q => decide (l < m) && P5J.parts4.contains q
  | _ => false

/-- True of the sorts of item that pass over "the one equation" of segment l. -/
def eqSort (l : Nat) : Item → Bool
  | .pin m _ => m == l
  | i => batSort l i

/-- An item that passes a test t at member 14 l + nAt l + d, or that its row shuts or owes. -/
def k9RowTest (t : Nat → Item → Bool) (d l : Nat) : Bool :=
  (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
    (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + d)).all fun i =>
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + d)).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + d)).owes.contains i || t l i

set_option maxRecDepth 1000000 in
/-- **At each batching every open item that the row neither shuts nor owes is of these sorts.** -/
theorem bat_open_sorts : ((List.range 25).all fun l => k9RowTest batSort 2 l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The like at each "one equation".** -/
theorem eq_open_sorts : ((List.range 25).all fun l => k9RowTest eqSort 4 l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the rows struck from the test the answer turns. -/
theorem bat_rows_bite :
    ((List.range 25).all fun l =>
      k9RowTest (fun l i => batSort l i && !(match i with | .row _ _ => true | _ => false)) 2 l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the claim on the weights struck from the test the answer turns. -/
theorem bat_wo_bites :
    ((List.range 25).all fun l =>
      k9RowTest (fun l i => batSort l i && !(match i with | .wo _ => true | _ => false)) 2 l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the batching's test does not do at "the one equation": the pins are open there. -/
theorem eq_pins_bite : ((List.range 25).all fun l => k9RowTest batSort 4 l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the rows struck from the test the answer turns. -/
theorem eq_rows_bite :
    ((List.range 25).all fun l =>
      k9RowTest (fun l i => eqSort l i && !(match i with | .row _ _ => true | _ => false)) 4 l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem eq_open_in_B :
    ((List.range 25).all fun l =>
      (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
        (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 4)).all fun i =>
        (P5J.oAt (14 * l + IM.nAt l + 4)).contains i) = true := by
  decide +kernel

/-- **What is open in front of "the one equation" by the thread's count is open there by the table's.** -/
theorem eq_open_in {l : Nat} (hl : l < 25) {i : Item}
    (h1 : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 4)) :
    i ∈ P5J.oAt (14 * l + IM.nAt l + 4) :=
  List.contains_iff_mem.1 (List.all_eq_true.1 (List.all_eq_true.1 eq_open_in_B l (List.mem_range.2 hl)) i h1)

/-- What the batching's test says of one item. -/
theorem batSort_cases {l : Nat} {i : Item} (t : batSort l i = true) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ c, c ≠ RowClass.equation ∧ i = .row l c) ∨ i = .wo l ∨
      (∃ m q, q ∈ P5J.parts4 ∧ i = .constr m q) := by
  cases i with
  | unmarked => exact Or.inl rfl
  | pinW => exact Or.inr (Or.inl rfl)
  | pile => exact Or.inr (Or.inr (Or.inl rfl))
  | pinI => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | row m c =>
    have t' : (m == l && c != .equation) = true := t
    rw [Bool.and_eq_true] at t'
    have e : m = l := beq_iff_eq.1 t'.1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, bne_iff_ne.1 t'.2, by rw [e]⟩))))
  | wo m =>
    have e : m = l := beq_iff_eq.1 t
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]))))))
  | constr m q =>
    have t' : (decide (l < m) && P5J.parts4.contains q) = true := t
    rw [Bool.and_eq_true] at t'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, List.contains_iff_mem.1 t'.2, rfl⟩)))))
  | _ => simp [batSort] at t

/-- **At one batching and one item.** -/
theorem bat_open_cases {l : Nat} (hl : l < 25) {i : Item}
    (h1 : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 2))
    (h2 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 2)).shuts)
    (h3 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 2)).owes) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ c, c ≠ RowClass.equation ∧ i = .row l c) ∨ i = .wo l ∨
      (∃ m q, q ∈ P5J.parts4 ∧ i = .constr m q) := by
  have t := List.all_eq_true.1 (List.all_eq_true.1 bat_open_sorts l (List.mem_range.2 hl)) i h1
  rw [Bool.or_eq_true, Bool.or_eq_true] at t
  rcases t with (t | t) | t
  · exact absurd (List.contains_iff_mem.1 t) h2
  · exact absurd (List.contains_iff_mem.1 t) h3
  · exact batSort_cases t

/-- **At one "one equation" and one item.** -/
theorem eq_open_cases {l : Nat} (hl : l < 25) {i : Item}
    (h1 : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 4))
    (h2 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 4)).shuts)
    (h3 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 4)).owes) :
    (∃ t, i = .pin l t) ∨ i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨
      (∃ c, c ≠ RowClass.equation ∧ i = .row l c) ∨ i = .wo l ∨ (∃ m q, q ∈ P5J.parts4 ∧ i = .constr m q) := by
  have t := List.all_eq_true.1 (List.all_eq_true.1 eq_open_sorts l (List.mem_range.2 hl)) i h1
  rw [Bool.or_eq_true, Bool.or_eq_true] at t
  rcases t with (t | t) | t
  · exact absurd (List.contains_iff_mem.1 t) h2
  · exact absurd (List.contains_iff_mem.1 t) h3
  · by_cases hp : ∃ m k, i = .pin m k
    · obtain ⟨m, k, rfl⟩ := hp
      have e : m = l := beq_iff_eq.1 t
      exact Or.inl ⟨k, by rw [e]⟩
    · refine Or.inr (batSort_cases ?_)
      cases i with
      | pin m k => exact absurd ⟨m, k, rfl⟩ hp
      | _ => exact t

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.bat_open_sorts
#print axioms ProofFile.Honest.K9.eq_open_sorts
#print axioms ProofFile.Honest.K9.bat_rows_bite
#print axioms ProofFile.Honest.K9.bat_wo_bites
#print axioms ProofFile.Honest.K9.eq_pins_bite
#print axioms ProofFile.Honest.K9.eq_rows_bite
#print axioms ProofFile.Honest.K9.eq_open_in_B
#print axioms ProofFile.Honest.K9.eq_open_in
#print axioms ProofFile.Honest.K9.batSort_cases
#print axioms ProofFile.Honest.K9.bat_open_cases
#print axioms ProofFile.Honest.K9.eq_open_cases
