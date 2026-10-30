-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SpineListK1.lean: a copy, made by program, of Johnson/Desc/Sound/SpineList.lean, under another namespace (VerifiableInference.Desc.K1.SL): definitions, statements and proofs to the sign. It is meant to go once its users import the original.

Its one user is Johnson/Desc/K1/Law/GoAtLater.lean.
-/
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.SL
open VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start rowOf stepOpen openSets
  readsOpen)

/-- The open items at border k, as a list. -/
def openL {ι : Type} [DecidableEq ι] (ins outs : ℕ → List ι) (s : List ι) : ℕ → List ι
  | 0 => s
  | k + 1 => (openL ins outs s k).filter (fun i => decide (i ∉ ins k)) ++ outs k

/-- **The rule's open set is that list's members.** -/
def OpenIsList : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (ins outs : ℕ → List ι) (s : List ι) (k : ℕ) (i : ι),
    openAfter (fun k i => i ∈ ins k) (fun k i => i ∈ outs k) (· ∈ s) k i ↔ i ∈ openL ins outs s k

theorem openIsList : OpenIsList := by
  intro ι _ ins outs s k
  induction k with
  | zero => exact fun i => Iff.rfl
  | succ k ih =>
    intro i
    show (openAfter _ _ _ k i ∧ ¬ i ∈ ins k) ∨ i ∈ outs k ↔
      i ∈ (openL ins outs s k).filter (fun i => decide (i ∉ ins k)) ++ outs k
    rw [List.mem_append, List.mem_filter, ih i, decide_eq_true_iff]

/-- What block number k of the first chain's table closes, as a list. -/
def insL (links : List ModelPart) (ps : List Place) (k : ℕ) : List Item :=
  (rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [.unmarked]

/-- What it opens, as a list. -/
def outsL (links : List ModelPart) (ps : List Place) (k : ℕ) : List Item :=
  (rowQ links ps k).outs ++ (rowQ links ps k).ctx ++ [.unmarked]

/-- **At the first chain's table the relation at border k is "every member of the list holds".** -/
theorem relQ_iff {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (k : ℕ) (a : A × Fr.E.Str) (w : W) :
    relQ N Mg links ps get k a w ↔
      ∀ i ∈ openL (insL links ps) (outsL links ps) (start links) k, meansQ N Mg get i a w :=
  ⟨fun h i hi => h i ((openIsList Item (insL links ps) (outsL links ps) (start links) k i).2 hi),
    fun h i hi => h i ((openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 hi)⟩

/-! ## The list of the rule and the list of the table's tests -/

theorem openL_succ {ι : Type} [DecidableEq ι] (ins outs : ℕ → List ι) (s : List ι) (k : ℕ) :
    openL ins outs s (k + 1) =
      openL (fun j => ins (j + 1)) (fun j => outs (j + 1)) (openL ins outs s 1) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (openL ins outs s (k + 1)).filter (fun i => decide (i ∉ ins (k + 1))) ++ outs (k + 1) = _
    rw [ih]
    rfl

theorem openL_congr {ι : Type} [DecidableEq ι] (ins outs : ℕ → List ι) (s s' : List ι)
    (h : ∀ i, i ∈ s ↔ i ∈ s') (k : ℕ) (i : ι) :
    i ∈ openL ins outs s k ↔ i ∈ openL ins outs s' k := by
  induction k generalizing i with
  | zero => exact h i
  | succ k ih =>
    show i ∈ (openL ins outs s k).filter (fun i => decide (i ∉ ins k)) ++ outs k ↔
      i ∈ (openL ins outs s' k).filter (fun i => decide (i ∉ ins k)) ++ outs k
    rw [List.mem_append, List.mem_append, List.mem_filter, List.mem_filter, ih i]

/-- The test beneath, at any rows: so that a control can hand it other rows than the table's. -/
def rowsApartBy (rows : Place → First.BlockRow) (ps : List Place) : Bool :=
  ps.all fun p => ((rows p).ctx.all fun i => !(rows p).ins.contains i) &&
    !(rows p).ins.contains .unmarked

/-- A TEST ON THE TABLE: no row both closes and reads an item; no row closes "no mark". -/
def rowsApart (links : List ModelPart) (ps : List Place) : Bool := rowsApartBy (rowOf links) ps

/-- One block: the rule's step and the tests' step have the same members. -/
theorem step_iff (O : List Item) (r : First.BlockRow) (hc : ∀ i ∈ r.ctx, i ∈ O)
    (ha : ∀ i ∈ r.ctx, i ∉ r.ins) (hu : Item.unmarked ∈ O) (hn : Item.unmarked ∉ r.ins) (i : Item) :
    i ∈ O.filter (fun i => decide (i ∉ r.ins ++ r.ctx ++ [.unmarked])) ++
        (r.outs ++ r.ctx ++ [.unmarked]) ↔ i ∈ stepOpen O r := by
  unfold stepOpen
  simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_eq_true_iff,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, not_or, not_and, not_not]
  constructor
  · rintro (⟨h1, ⟨h2, _⟩, _⟩ | (h | h) | h)
    · exact Or.inl ⟨h1, h2⟩
    · by_cases hO : i ∈ O ∧ i ∉ r.ins
      · exact Or.inl hO
      · exact Or.inr ⟨h, fun h1 => by_contra fun h2 => hO ⟨h1, h2⟩⟩
    · exact Or.inl ⟨hc i h, ha i h⟩
    · subst h
      exact Or.inl ⟨hu, hn⟩
  · rintro (⟨h1, h2⟩ | ⟨h, _⟩)
    · by_cases h3 : i ∈ r.ctx
      · exact Or.inr (Or.inl (Or.inr h3))
      · by_cases h4 : i = .unmarked
        · exact Or.inr (Or.inr h4)
        · exact Or.inl ⟨h1, ⟨h2, h3⟩, h4⟩
    · exact Or.inr (Or.inl (Or.inl h))

/-- **WHERE THE TABLE's TESTS `readsOpen` AND `rowsApart` SAY YES, THE RULE's OPEN SET AT BORDER k
HAS JUST THE MEMBERS OF THE LIST ON WHICH THE TABLE's TESTS AND ITS PROMISE RUN** (`openSets`). -/
theorem openL_iff_openSets (links : List ModelPart) : ∀ (ps : List Place) (O : List Item),
    readsOpen links ps O = true → rowsApart links ps = true → Item.unmarked ∈ O →
    ∀ k, k ≤ ps.length → ∀ i,
      (i ∈ openL (insL links ps) (outsL links ps) O k ↔ i ∈ (openSets links ps O)[k]?.getD [])
  | [], O, _, _, _, k, hk, i => by
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact Iff.rfl
  | p :: ps, O, hr, ha, hu, 0, _, i => Iff.rfl
  | p :: ps, O, hr, ha, hu, k + 1, hk, i => by
    have hr' : ((rowOf links p).ins ++ (rowOf links p).ctx).all O.contains = true ∧
        readsOpen links ps (stepOpen O (rowOf links p)) = true := by
      simpa [readsOpen, Bool.and_eq_true] using hr
    have ha' : (((rowOf links p).ctx.all fun i => !(rowOf links p).ins.contains i) = true ∧
        (!(rowOf links p).ins.contains .unmarked) = true) ∧ rowsApart links ps = true := by
      simpa [rowsApart, rowsApartBy, List.all_cons, Bool.and_eq_true] using ha
    have hc : ∀ i ∈ (rowOf links p).ctx, i ∈ O := fun i hi => by
      have := List.all_eq_true.1 hr'.1 i (List.mem_append_right _ hi)
      simpa using this
    have hx : ∀ i ∈ (rowOf links p).ctx, i ∉ (rowOf links p).ins := fun i hi => by
      have := List.all_eq_true.1 ha'.1.1 i hi
      simpa using this
    have hn : Item.unmarked ∉ (rowOf links p).ins := by simpa using ha'.1.2
    have hs := step_iff O (rowOf links p) hc hx hu hn
    have hu' : Item.unmarked ∈ stepOpen O (rowOf links p) :=
      (hs .unmarked).1
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
    rw [openL_succ]
    have e := openL_iff_openSets links ps (stepOpen O (rowOf links p)) hr'.2 ha'.2 hu' k
      (Nat.le_of_succ_le_succ hk) i
    exact (openL_congr (insL links ps) (outsL links ps) _ _ hs k i).trans e

end VerifiableInference.Desc.K1.SL
