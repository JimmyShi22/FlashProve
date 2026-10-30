-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean: what an accept and a reject of the test of
CutTest.lean say; how a sub-protocol's place, its number of rounds and what it tells are read off
its row; closed facts on the written lists, by Lean's kernel; negative tests. Statements and proofs,
and one small definition on rows.

General, at every list of sub-protocols.
  `sparse_flat`, `toldRounds_flat`: nothing told is left out: the trees in `toldRounds b`, in a row,
                      are those of `b.oracles`, in a row
  `toldOfRow r`, `toldBy_row`: how many oracle messages a row tells: `toldBy b` (ToldTest.lean) at
                      b's row
  `toldBefore_cut`    so the messages told in front of number k are a sum over the first k rows
  `row_at`            the row number k is the sub-protocol number k's
The test.
  `sameRow_iff`, `sameRows_iff`: the comparison leaves no field out: it is equality
  `cutIs_eq`          an accept: the three equations
  `cutIs_no`          WHAT A REJECT SAYS: one chain's cut is not the written one
  `cut_of_row`        the same of the row for the proof file's entry tests
Closed facts on the written lists.
  `cut_lengths`       358, 12 and 4 rows
  `cut_rounds`        the rounds that the rows declare, summed, chain by chain
  `cut_switches`      at the 25 numbers of `switchCuts` (ToldTest.lean) stands a row of the kind K2
  `cut_told`          in front of each of these the rows tell the written number of messages
  `told_of_cut`       SO THE TEST OF ToldTest.lean FOLLOWS: a list with the written cut passes
                      `toldPinned`: that test need not be asked beside this one
Negative tests, on the written first list with one thing turned: a name, a place's kind, a number of
rounds, what a switch tells, a message in `before`, a row left out, two chains' lists exchanged:
each rejected (`plant_name`, `plant_kind`, `plant_rounds`, `plant_told`, `plant_before`,
`plant_short`, `plant_swapped`); the written lists themselves are accepted (`same_self`).
Limits. Those of CutTest.lean. That a verifier asks the test is not said here. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.CutTest
import Johnson.Desc.Ok.PlanWritten.ToldTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open VerifiableInference.Desc

variable {S Cl : Type}

/-! ### General -/

theorem sparse_flat {α : Type} : ∀ (l : List (List α)) (k : Nat),
    (((l.zipIdx k).filter fun x => !x.1.isEmpty).map fun x => (x.2, x.1)).flatMap (·.2) = l.flatten
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.flatten_cons]
    cases a with
    | nil =>
      rw [List.filter_cons_of_neg (by simp), sparse_flat l (k + 1)]
      rfl
    | cons x a =>
      rw [List.filter_cons_of_pos (by simp), List.map_cons, List.flatMap_cons,
        sparse_flat l (k + 1)]

/-- **Nothing told is left out.** -/
theorem toldRounds_flat (b : Block S Cl) : (toldRounds b).flatMap (·.2) = b.oracles.flatten :=
  sparse_flat b.oracles 0

/-- How many oracle messages a row tells. -/
def toldOfRow (r : String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) :
    Nat :=
  ((r.2.2.2.2.1.flatMap (·.2)).map fun o => o.tenants.length).sum

theorem toldBy_row (b : Block S Cl) :
    toldOfRow (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) =
      toldBy b := by
  unfold toldOfRow toldBy
  rw [toldRounds_flat]

/-- **The messages told in front of number k, off the rows.** -/
theorem toldBefore_cut (bs : List (Block S Cl)) (k : Nat) :
    toldBefore bs k = (((cutOf bs).take k).map toldOfRow).sum := by
  unfold toldBefore cutOf
  rw [← List.map_take, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => (toldBy_row b).symm

/-- The row number k is the sub-protocol number k's. -/
theorem row_at (bs : List (Block S Cl)) (k : Nat) :
    (cutOf bs)[k]? = (bs[k]?).map fun b =>
      (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) := by
  unfold cutOf
  rw [List.getElem?_map]

/-! ### The test -/

/-- The comparison of two rows leaves no field out. -/
theorem sameRow_iff
    (x y : String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) :
    sameRow x y = true ↔ x = y := by
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := x
  obtain ⟨y1, y2, y3, y4, y5, y6⟩ := y
  unfold sameRow
  simp only [Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

/-- **The comparison of two lists is equality.** -/
theorem sameRows_iff : ∀ (a b :
    List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat))),
    sameRows a b = true ↔ a = b
  | [], [] => by simp [sameRows]
  | [], _ :: _ => by simp [sameRows]
  | _ :: _, [] => by simp [sameRows]
  | x :: a, y :: b => by
    rw [sameRows, Bool.and_eq_true, sameRow_iff, sameRows_iff a b, List.cons.injEq]

/-- **An accept.** -/
theorem cutIs_eq {Xi : Type} {F : FileDescription Xi} (h : cutIs F = true) :
    cutOf F.first.blocksInOrder = cutFirstFull ∧ cutOf F.shared.blocksInOrder = cutSharedFull ∧
      cutOf F.second.blocksInOrder = cutSecondFull := by
  unfold cutIs cutSame at h
  simp only [Bool.and_eq_true, sameRows_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **What a reject says.** -/
theorem cutIs_no {Xi : Type} {F : FileDescription Xi} (h : cutIs F = false) :
    cutOf F.first.blocksInOrder ≠ cutFirstFull ∨ cutOf F.shared.blocksInOrder ≠ cutSharedFull ∨
      cutOf F.second.blocksInOrder ≠ cutSecondFull := by
  by_cases h1 : cutOf F.first.blocksInOrder = cutFirstFull
  · by_cases h2 : cutOf F.shared.blocksInOrder = cutSharedFull
    · by_cases h3 : cutOf F.second.blocksInOrder = cutSecondFull
      · exfalso
        have e : cutIs F = true := by
          unfold cutIs cutSame
          simp only [Bool.and_eq_true, sameRows_iff]
          exact ⟨⟨h1, h2⟩, h3⟩
        rw [e] at h
        cases h
      · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

/-- **The row's accept.** -/
theorem cut_of_row {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} (h : cutRow F Z = true) :
    cutOf F.first.blocksInOrder = cutFirstFull ∧ cutOf F.shared.blocksInOrder = cutSharedFull ∧
      cutOf F.second.blocksInOrder = cutSecondFull :=
  cutIs_eq h

/-! ### Closed facts on the written lists -/

set_option maxRecDepth 1000000 in
theorem cut_lengths : cutFirstFull.length = 358 ∧ cutSharedFull.length = 12 ∧
    cutSecondFull.length = 4 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem cut_rounds : (cutFirstFull.map (·.2.2.1)).sum = 48293 ∧
    (cutSharedFull.map (·.2.2.1)).sum = 68 ∧ (cutSecondFull.map (·.2.2.1)).sum = 30 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem cut_switches :
    (switchCuts.all fun x => (cutFirstFull[x.1]?).map (·.2.1.kind) == some .K2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem cut_told :
    (switchCuts.all fun x => ((cutFirstFull.take x.1).map toldOfRow).sum == x.2) = true := by
  decide +kernel

/-- **The test of ToldTest.lean follows from this one.** -/
theorem told_of_cut {bs : List (Block S Cl)} (h : cutOf bs = cutFirstFull) :
    toldPinned fullKey bs = true := by
  unfold toldPinned
  rw [if_pos rfl]
  have H := cut_told
  rw [List.all_eq_true] at H ⊢
  intro x hx
  rw [toldBefore_cut, h]
  exact H x hx

/-! ### Negative tests -/

set_option maxRecDepth 1000000 in
theorem same_self : cutSame cutFirstFull cutSharedFull cutSecondFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A name turned. -/
theorem plant_name : cutSame (cutFirstFull.modify 16 fun r => ("X", r.2)) cutSharedFull
    cutSecondFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A place's kind turned. -/
theorem plant_kind : cutSame
    (cutFirstFull.modify 16 fun r => (r.1, { r.2.1 with kind := .K1 }, r.2.2)) cutSharedFull
    cutSecondFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One round more. -/
theorem plant_rounds : cutSame
    (cutFirstFull.modify 16 fun r => (r.1, r.2.1, r.2.2.1 + 1, r.2.2.2)) cutSharedFull
    cutSecondFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- What a switch tells struck out. -/
theorem plant_told : cutSame
    (cutFirstFull.modify 16 fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, [], r.2.2.2.2.2))
    cutSharedFull cutSecondFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One message more in `before`. -/
theorem plant_before : cutSame
    (cutFirstFull.modify 16 fun r =>
      (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, (9, 9) :: r.2.2.2.2.2))
    cutSharedFull cutSecondFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The last row left out. -/
theorem plant_short : cutSame cutFirstFull.dropLast cutSharedFull cutSecondFull = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Two chains' lists exchanged. -/
theorem plant_swapped : cutSame cutFirstFull cutSecondFull cutSharedFull = false := by
  decide +kernel

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.toldRounds_flat
#print axioms VerifiableInference.PlanWritten.toldBefore_cut
#print axioms VerifiableInference.PlanWritten.row_at
#print axioms VerifiableInference.PlanWritten.sameRows_iff
#print axioms VerifiableInference.PlanWritten.cutIs_eq
#print axioms VerifiableInference.PlanWritten.cutIs_no
#print axioms VerifiableInference.PlanWritten.cut_of_row
#print axioms VerifiableInference.PlanWritten.cut_lengths
#print axioms VerifiableInference.PlanWritten.cut_rounds
#print axioms VerifiableInference.PlanWritten.cut_switches
#print axioms VerifiableInference.PlanWritten.cut_told
#print axioms VerifiableInference.PlanWritten.told_of_cut
#print axioms VerifiableInference.PlanWritten.same_self
#print axioms VerifiableInference.PlanWritten.plant_name
#print axioms VerifiableInference.PlanWritten.plant_kind
#print axioms VerifiableInference.PlanWritten.plant_rounds
#print axioms VerifiableInference.PlanWritten.plant_told
#print axioms VerifiableInference.PlanWritten.plant_before
#print axioms VerifiableInference.PlanWritten.plant_short
#print axioms VerifiableInference.PlanWritten.plant_swapped
