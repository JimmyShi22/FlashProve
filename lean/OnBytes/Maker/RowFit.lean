-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RowFit.lean: what the comparison of a file's three stages in a row with the reduction
of the whole file (OnBytes/Maker/RowWhole.lean) asks of the data and of the
two lists of trees left, as a property and as a test.

  `RowFit D L₁ L₂`: the property: five clauses.
  `rowFitB`, `rowFitB_iff`: the same as a test: each clause a bounded search through the lists; the
    test says yes exactly where the property holds.
  `rowFitAt a W`, `rowFit_of_rowFitAt`: the test at the plain data of a file
    (OnBytes/Three/Data.lean) and the two lists of trees left that are computed from them
    (OnBytes/Maker/StageOf.lean, `leftAfter`).
  `rowFitAt_empty`: at the data of three empty lists the test says yes.

What is not claimed. That the test says yes at the data of any file.


-/
import OnBytes.Maker.StageOf

set_option autoImplicit false

namespace OnBytes.Maker

/-- What the comparison asks. `o₁`, `o₂`: the first chain opens its own trees alone, the second none
of the third's. `l₁`, `l₂`: a tree of an earlier chain that the second or the third chain opens
stands in the list of trees left, at the depth that the data give it. `l₂₁`: a tree of the first
chain that is left behind the second was left behind the first, at no smaller depth. -/
structure RowFit (D : WholeD) (L₁ L₂ : List LeftT) : Prop where
  o₁ : ∀ d ∈ D.ds₁, ∀ j ∈ d.opens, j < D.t₁
  o₂ : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, j < D.t₁ + D.t₂
  l₁ : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, j < D.t₁ →
    (L₁.find? (·.no == j)).map (·.a) = (treeShT D.ds₁ j).map (·.a)
  l₂ : ∀ d ∈ D.ds₃, ∀ j ∈ d.opens, j < D.t₁ + D.t₂ → (L₂.find? (·.no == j)).map (·.a) = D.depth j
  l₂₁ : ∀ l ∈ L₂, l.no < D.t₁ → ∃ l' ∈ L₁, l'.no = l.no ∧ l.a ≤ l'.a

/-- `RowFit` as a test: its five clauses, each a bounded search through the lists. -/
def rowFitB (D : WholeD) (L₁ L₂ : List LeftT) : Bool :=
  (D.ds₁.all fun d => d.opens.all fun j => decide (j < D.t₁)) &&
  (D.ds₂.all fun d => d.opens.all fun j => decide (j < D.t₁ + D.t₂)) &&
  (D.ds₂.all fun d => d.opens.all fun j => !decide (j < D.t₁) ||
    decide ((L₁.find? (·.no == j)).map (·.a) = (treeShT D.ds₁ j).map (·.a))) &&
  (D.ds₃.all fun d => d.opens.all fun j => !decide (j < D.t₁ + D.t₂) ||
    decide ((L₂.find? (·.no == j)).map (·.a) = D.depth j)) &&
  (L₂.all fun l => !decide (l.no < D.t₁) ||
    L₁.any fun l' => decide (l'.no = l.no) && decide (l.a ≤ l'.a))

/-- **The test says yes exactly where the conditions hold.** -/
theorem rowFitB_iff (D : WholeD) (L₁ L₂ : List LeftT) :
    rowFitB D L₁ L₂ = true ↔ RowFit D L₁ L₂ := by
  unfold rowFitB
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, fun d hd j hj hlt => (h3 d hd j hj).resolve_left (not_not_intro hlt),
      fun d hd j hj hlt => (h4 d hd j hj).resolve_left (not_not_intro hlt),
      fun l hl hlt => (h5 l hl).resolve_left (not_not_intro hlt)⟩
  · intro F
    refine ⟨⟨⟨⟨F.o₁, F.o₂⟩, fun d hd j hj => ?_⟩, fun d hd j hj => ?_⟩, fun l hl => ?_⟩
    · by_cases h : j < D.t₁
      · exact Or.inr (F.l₁ d hd j hj h)
      · exact Or.inl h
    · by_cases h : j < D.t₁ + D.t₂
      · exact Or.inr (F.l₂ d hd j hj h)
      · exact Or.inl h
    · by_cases h : l.no < D.t₁
      · exact Or.inr (F.l₂₁ l hl h)
      · exact Or.inl h

/-- The test at the plain data of a file and the two lists of trees left that are computed from
them. -/
def rowFitAt (a : ℕ) (W : Three.Whole) : Bool :=
  rowFitB (WholeD.of a W) (leftAfter W 0) (leftAfter W 1)

theorem rowFit_of_rowFitAt {a : ℕ} {W : Three.Whole} (h : rowFitAt a W = true) :
    RowFit (WholeD.of a W) (leftAfter W 0) (leftAfter W 1) := (rowFitB_iff _ _ _).1 h

/-- At the data of three empty lists the test says yes. -/
theorem rowFitAt_empty (a : ℕ) : rowFitAt a (Three.Whole.of [] [] []) = true := rfl

end OnBytes.Maker
