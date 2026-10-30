-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FixLowFits.lean: A FORM THAT FITS n VARIABLES (`Own.formFits`,
Johnson/Desc/Own/Shapes.lean), WITH ITS LOWEST VARIABLES FIXED AT A POINT (`Form.fixLow`,
OnBytes/Iop/Tensor.lean), FITS THE VARIABLES THAT ARE LEFT. No state, no plan, no statement: the
program's text on tensors and forms alone. Statements with their proofs: two recursions, unfoldings,
calls.

WHY. The claim that a closing carries to the next switch is the batched row's form with its lowest
variables fixed. The switch's law asks that it fits (`TablesFit.claimMain`, Returns/BehindAt.lean).
The library's `Form.fixLow_shape` (OnBytes/Iop/FixLaws.lean) has three of the clauses and names in
its docstring what it does not show: that each slice lies inside its vector, and that each single
entry's index is below 2 to the number of variables.

  `foldBit_size` a bit folded out of a stretch of size entries leaves size / 2
  `Room`, `sliceStep_room`, `sliceLoop_room` what holds of the state of `Tensor.foldedSlice`'s loop:
                    its size, and that the stretch lies inside its vector; one step; the loop. THE
                    LIBRARY's `SliceAt`, `sliceStep_at`, `sliceLoop_at` have the size and what the
                    entries read as, not the vector's bound; the lines on the size are theirs
  `foldedSlice_size` so the folded slice has 2 to the number of the written-out variables that are
                    left
  `Roomy v` the second clause of `Own.InOrder`
  `scale_first_values`, `roomy_scale`, `fixLowWith_room`, `fixLow_room` it passes to a multiple
                    (`scale_first_values` is `scale_slice` of Returns/MembersReached.lean, which
                    this light file does not import); to a tensor fixed with a slice of that size;
                    to `Tensor.fixLow`
  `mergeLoop_index`, `merge_index` each index of `mergeEntries l` is an index of l
  `formFits_fixLow` THE TOP

By, all the library's: `fold_push`, `Tensor.foldedSlice_eq`, `mergeEntries_eq`,
`Tensor.denseVars_scale`, `Form.fixLow_shape` (OnBytes/Iop/FixLaws.lean) · `Form.fixLow_eq_plain`
(OnBytes/Iop/FixExact.lean): `Form.fixLow`, which shares folded slices through a table, returns what
`Form.fixLowPlain` returns, which fixes each tensor by itself: so nothing is said of the table here
· `formFits_iff` (Johnson/Desc/Own/ShapesMean.lean).

Limits. The point has at most n coordinates: a premise. Nothing on what the result reads as: that is
the library's `Form.fixLow_val`. Nothing on any property.



-/
import Johnson.Desc.Own.ShapesMean
import OnBytes.Iop.FixExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes

/-! ## The folded slice's size -/

theorem foldBit_size (a : Array E) (start size i : Nat) (x : E) :
    (foldBit a start size i x).size = size / 2 := by
  unfold foldBit
  dsimp only
  rw [← Array.length_toList, fold_push]
  simp

/-- What holds of the state of `Tensor.foldedSlice`'s loop when the bits from i on have been looked
at: its size, and that the stretch lies inside its vector. -/
def Room (v : Tensor) (g : List E) (i : Nat) (s : Array E × Nat × Nat) : Prop :=
  s.2.2 = 2 ^ (i + (keptVars g.length (v.denseVars.drop i)).length) ∧ s.2.1 + s.2.2 ≤ s.1.size

theorem sliceStep_room (v : Tensor) (g : List E) (i : Nat) (hi : i < v.denseVars.length)
    (s : Array E × Nat × Nat) (h : Room v g (i + 1) s) : Room v g i (sliceStep v g s i) := by
  have hd : v.denseVars[i]? = some v.denseVars[i] := List.getElem?_eq_getElem hi
  have hdrop : v.denseVars.drop i = v.denseVars[i] :: v.denseVars.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  unfold sliceStep
  rw [hd]
  dsimp only
  by_cases hm : v.denseVars[i] < g.length
  · have hk : keptVars g.length (v.denseVars.drop i) =
        keptVars g.length (v.denseVars.drop (i + 1)) := by
      rw [hdrop]
      unfold keptVars
      rw [List.filter_cons_of_neg (by simpa using hm)]
    rw [if_pos hm]
    have hsz : s.2.2 / 2 = 2 ^ (i + (keptVars g.length (v.denseVars.drop (i + 1))).length) := by
      rw [h.1, show i + 1 + (keptVars g.length (v.denseVars.drop (i + 1))).length =
        i + (keptVars g.length (v.denseVars.drop (i + 1))).length + 1 by omega, Nat.pow_succ,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
    refine ⟨by rw [hk]; exact hsz, ?_⟩
    show 0 + s.2.2 / 2 ≤ (foldBit s.1 s.2.1 s.2.2 i (g.getD v.denseVars[i] zeroE)).size
    rw [foldBit_size]
    omega
  · have hk : (keptVars g.length (v.denseVars.drop i)).length =
        (keptVars g.length (v.denseVars.drop (i + 1))).length + 1 := by
      rw [hdrop]
      unfold keptVars
      rw [List.filter_cons_of_pos (by simpa using Nat.le_of_not_lt hm)]
      simp
    rw [if_neg hm]
    refine ⟨?_, h.2⟩
    rw [h.1, hk]
    congr 1
    omega

theorem sliceLoop_room (v : Tensor) (g : List E) :
    ∀ (i : Nat), i ≤ v.denseVars.length → ∀ s, Room v g i s →
    Room v g 0 ((List.range i).reverse.foldl (sliceStep v g) s)
  | 0, _, s, h => h
  | i + 1, hi, s, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    exact sliceLoop_room v g i (by omega) _ (sliceStep_room v g i (by omega) s h)

/-- **The folded slice of a tensor whose slice lies inside its vector has 2 to the number of the
written-out variables that are left.** -/
theorem foldedSlice_size (v : Tensor) (g : List E)
    (h : v.first + 2 ^ v.denseVars.length ≤ v.values.size) :
    (v.foldedSlice g).size = 2 ^ (keptVars g.length v.denseVars).length := by
  have H := sliceLoop_room v g v.denseVars.length (Nat.le_refl _)
    (v.values, v.first, 2 ^ v.denseVars.length)
    ⟨by rw [List.drop_length]; rfl, h⟩
  rw [Tensor.foldedSlice_eq]
  dsimp only
  generalize (List.range v.denseVars.length).reverse.foldl (sliceStep v g)
    (v.values, v.first, 2 ^ v.denseVars.length) = s at H ⊢
  obtain ⟨h1, h2⟩ := H
  rw [List.drop_zero, Nat.zero_add] at h1
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.2, h1]
  · rw [Array.size_extract, ← h1]
    omega

/-! ## The room of a tensor with its lowest variables fixed -/

/-- The second clause of `Own.InOrder` (Johnson/Desc/Own/ShapesMean.lean; as a test: of
`tensorInOrder`, Johnson/Desc/Own/Shapes.lean): the slice lies inside its vector. -/
def Roomy (v : Tensor) : Prop :=
  v.denseVars = [] ∨ v.first + 2 ^ v.denseVars.length ≤ v.values.size

theorem scale_first_values (v : Tensor) (x : E) :
    (v.scale x).first = v.first ∧ (v.scale x).values = v.values := by
  unfold Tensor.scale
  exact ⟨rfl, rfl⟩

theorem roomy_scale {v : Tensor} (h : Roomy v) (x : E) : Roomy (v.scale x) := by
  unfold Roomy at h ⊢
  rw [Tensor.denseVars_scale, (scale_first_values v x).1, (scale_first_values v x).2]
  exact h

theorem fixLowWith_room (v : Tensor) (g : List E) (slice : Array E)
    (hs : slice.size = 2 ^ (keptVars g.length v.denseVars).length) :
    Roomy (v.fixLowWith g slice) := by
  unfold Tensor.fixLowWith
  dsimp only
  split
  · exact Or.inl rfl
  · refine Or.inr ?_
    show 0 + 2 ^ ((v.denseVars.filter (g.length ≤ ·)).map (· - g.length)).length ≤ slice.size
    rw [hs]
    unfold keptVars
    omega

theorem fixLow_room {v : Tensor} (h : Roomy v) (g : List E) : Roomy (v.fixLow g) := by
  unfold Tensor.fixLow
  split
  · rename_i hc
    refine fixLowWith_room v g _ (foldedSlice_size v g (h.resolve_left fun e => ?_))
    unfold Tensor.sliceIsCut at hc
    rw [e] at hc
    cases hc
  · rcases h with e | e
    · refine Or.inl ?_
      show v.denseVars.map (· - g.length) = []
      rw [e]
      rfl
    · refine Or.inr ?_
      show v.first + 2 ^ (v.denseVars.map (· - g.length)).length ≤ v.values.size
      rw [List.length_map]
      exact e

/-! ## The single entries' indexes -/

theorem mergeLoop_index : ∀ (l acc : List (Nat × E)), ∀ e ∈ l.foldl mergeStep acc,
    (∃ a ∈ acc, a.1 = e.1) ∨ ∃ a ∈ l, a.1 = e.1
  | [], _, e, he => Or.inl ⟨e, he, rfl⟩
  | a :: l, acc, e, he => by
    rw [List.foldl_cons] at he
    rcases mergeLoop_index l _ e he with ⟨b, hb, eb⟩ | ⟨b, hb, eb⟩
    · cases acc with
      | nil =>
        have : b = a := by simpa [mergeStep] using hb
        exact Or.inr ⟨a, by simp, by rw [← this]; exact eb⟩
      | cons c r =>
        by_cases h : a.1 = c.1
        · have hb' : b = (c.1, addE c.2 a.2) ∨ b ∈ r := by
            simpa [mergeStep, h] using hb
          rcases hb' with rfl | hb'
          · exact Or.inl ⟨c, by simp, eb⟩
          · exact Or.inl ⟨b, by simp [hb'], eb⟩
        · have hn : (a.1 == c.1) = false := by simpa using h
          have hb' : b = a ∨ b = c ∨ b ∈ r := by
            simpa [mergeStep, hn] using hb
          rcases hb' with rfl | rfl | hb'
          · exact Or.inr ⟨b, by simp, eb⟩
          · exact Or.inl ⟨b, by simp, eb⟩
          · exact Or.inl ⟨b, by simp [hb'], eb⟩
    · exact Or.inr ⟨b, by simp [hb], eb⟩

/-- Each index of `mergeEntries l` is an index of l. -/
theorem merge_index (l : List (Nat × E)) : ∀ e ∈ mergeEntries l, ∃ a ∈ l, a.1 = e.1 := by
  intro e he
  rw [mergeEntries_eq, List.mem_reverse] at he
  rcases mergeLoop_index _ [] e he with ⟨b, hb, -⟩ | ⟨b, hb, eb⟩
  · cases hb
  · exact ⟨b, (List.mergeSort_perm _ _).mem_iff.1 hb, eb⟩

/-! ## The form -/

/-- **A form that fits n variables, with its lowest variables fixed at a point of at most n
coordinates, fits what is left.** THE LIBRARY's `Form.fixLow_shape` has the number of variables,
"no double" and the pairs (1, 1); its docstring names as not shown what is added here: the slice
inside its vector, and the single entries' indexes. -/
theorem formFits_fixLow {f : Form} {n : Nat} (h : Own.formFits f n = true) (g : List E)
    (times : E) (hg : g.length ≤ n) : Own.formFits (f.fixLow g times) (n - g.length) = true := by
  obtain ⟨h1, h2⟩ := (Own.formFits_iff f n).1 h
  have hsh := Form.fixLow_shape f g times n fun v hv =>
    ⟨(h1 v hv).1, (h1 v hv).2.2.2.2, (h1 v hv).2.2.2.1⟩
  refine (Own.formFits_iff _ _).2 ⟨fun t ht => ?_, fun e he => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := hsh t ht
    have a1' : t.pairs.length = n - g.length := a1
    rw [Form.fixLow_eq_plain] at ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (show t ∈ f.tensors.map fun v =>
      (v.scale times).fixLow g from ht)
    obtain ⟨b1, b2, b3, -⟩ := h1 v hv
    exact ⟨a1', by omega, fixLow_room (roomy_scale b3 times) g, a3, a2⟩
  · have he' : e ∈ mergeEntries (f.entries.map fun e =>
        (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times)) := he
    obtain ⟨a, ha, ea⟩ := merge_index _ e he'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rw [← ea]
    show b.1 / 2 ^ g.length < 2 ^ (n - g.length)
    have hb' := h2 b hb
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hg]
    exact hb'

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.foldBit_size
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sliceStep_room
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sliceLoop_room
#print axioms VerifiableInference.Desc.K2.Honest.Returns.foldedSlice_size
#print axioms VerifiableInference.Desc.K2.Honest.Returns.scale_first_values
#print axioms VerifiableInference.Desc.K2.Honest.Returns.roomy_scale
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fixLowWith_room
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fixLow_room
#print axioms VerifiableInference.Desc.K2.Honest.Returns.mergeLoop_index
#print axioms VerifiableInference.Desc.K2.Honest.Returns.merge_index
#print axioms VerifiableInference.Desc.K2.Honest.Returns.formFits_fixLow
