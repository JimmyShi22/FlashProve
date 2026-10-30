-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFCellKit.lean: a family of conditions of degree two in cells, from its parts.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). Used for `jnFam` (Cm/SegFFCellIdn.lean) and `quadKeyFam`
(Cm/SegFFCellKeys.lean).

Main names:
  `QSpec`: the parts of a family (`Fam`, Cb/Req/ReqSpec.lean) whose value at the vertex b is the
    sum of
      ∑_{j < 2^w} ∑_{n < nS} κ_n(x, b · 2^w + j) · p_n(b · 2^w + j) · q_n(b · 2^w + j)
        (one sum atom, that is a sum over w further variables of products of two affine forms in
        cells under public coefficient tables);
      a(b) (an affine form in cells);
      ∑_{n < nQ} f_n(b) · g_n(b) (products of two affine forms in cells).
  `fam_val`: the value of `QSpec.fam`, for all matrices. `fam_wf`: it is well formed. `fam_places`:
    a property that all places of all forms have holds of all places that the family reads.

Limits: a tool; nothing here knows a segment.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegAlg

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Seg
open Cb Finset

theorem sum_map_range {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- a sum over the first n of N numbers, written with an indicator -/
theorem sum_range_ind {M : Type} [AddCommMonoid M] {n N : ℕ} (h : n ≤ N) (f : ℕ → M) :
    ∑ j ∈ range N, (if j < n then f j else 0) = ∑ j ∈ range n, f j := by
  rw [← sum_subset (range_subset_range.mpr h)]
  · exact sum_congr rfl fun j hj => if_pos (mem_range.mp hj)
  · intro j _ hj
    exact if_neg fun h' => hj (mem_range.mpr h')

/-- The parts of a family of degree two in cells. -/
structure QSpec (X E : Type) where
  v  : ℕ
  w  : ℕ
  nS : ℕ
  nQ : ℕ
  κ  : ℕ → X → ℕ → E
  p  : ℕ → ℕ → CForm E
  q  : ℕ → ℕ → CForm E
  a  : ℕ → CForm E
  f  : ℕ → ℕ → CForm E
  g  : ℕ → ℕ → CForm E

namespace QSpec
variable {X F E : Type} [Field F] [Field E] [Algebra F E] (S : QSpec X E)

/-- what is summed over the w further variables -/
def inner : Poly0 X E where
  v := S.v + S.w
  na := 2 * S.nS
  atom := fun j => .cell (if j % 2 = 0 then S.p (j / 2) else S.q (j / 2))
  terms := (List.range S.nS).map fun n => ⟨S.κ n, [2 * n, 2 * n + 1]⟩

/-- The family. -/
def fam : Fam X E where
  v := S.v
  na := 2 + 2 * S.nQ
  atom := fun j =>
    if j = 0 then .sum S.w S.inner
    else if j = 1 then .base (.cell S.a)
    else .base (.cell (if j % 2 = 0 then S.f ((j - 2) / 2) else S.g ((j - 2) / 2)))
  terms := ⟨fun _ _ => 1, [0]⟩ :: ⟨fun _ _ => 1, [1]⟩ ::
    (List.range S.nQ).map fun n => ⟨fun _ _ => 1, [2 * n + 2, 2 * n + 3]⟩

variable (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem inner_val (b : ℕ) :
    S.inner.val Φ x W A b = ∑ n ∈ range S.nS, S.κ n x b * ((S.p n b).val A * (S.q n b).val A) := by
  unfold Poly0.val inner
  rw [List.map_map, sum_map_range]
  refine sum_congr rfl fun n _ => ?_
  have e1 : (2 * n) % 2 = 0 := by omega
  have e2 : (2 * n) / 2 = n := by omega
  have e4 : (2 * n + 1) / 2 = n := by omega
  simp [Term.val, Atom0.val, e1, e2, e4]

theorem fam_val (b : ℕ) :
    S.fam.val Φ x W A b =
      (∑ j ∈ range (2 ^ S.w), ∑ n ∈ range S.nS, S.κ n x (b * 2 ^ S.w + j) *
          ((S.p n (b * 2 ^ S.w + j)).val A * (S.q n (b * 2 ^ S.w + j)).val A)) +
        (S.a b).val A + ∑ n ∈ range S.nQ, (S.f n b).val A * (S.g n b).val A := by
  unfold Fam.val fam
  rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.map_map,
    sum_map_range, ← add_assoc]
  congr 1
  · congr 1
    · simp only [Term.val, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        one_mul, if_pos, Atom.val]
      exact sum_congr rfl fun j _ => S.inner_val Φ x W A _
    · simp [Term.val, Atom.val, Atom0.val]
  · refine sum_congr rfl fun n _ => ?_
    have e0' : ¬ 2 * n + 2 = 1 := by omega
    have e1 : (2 * n + 2) % 2 = 0 := by omega
    have e3' : ¬ 2 * n + 3 = 1 := by omega
    have e5 : (2 * n + 1) / 2 = n := by omega
    simp [Term.val, Atom.val, Atom0.val, e0', e1, e3', e5]

theorem fam_wf : S.fam.WF Φ := by
  refine ⟨fun t ht j hj => ?_, fun j _ => ?_⟩
  · show j < 2 + 2 * S.nQ
    rcases List.mem_cons.1 ht with rfl | ht
    · obtain rfl : j = 0 := by simpa using hj
      omega
    rcases List.mem_cons.1 ht with rfl | ht
    · obtain rfl : j = 1 := by simpa using hj
      omega
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ht
    have hn' := List.mem_range.1 hn
    have : j = 2 * n + 2 ∨ j = 2 * n + 3 := by simpa using hj
    omega
  · show (if j = 0 then Atom.sum S.w S.inner
        else if j = 1 then .base (.cell S.a)
        else
          .base (.cell (if j % 2 = 0 then S.f ((j - 2) / 2) else S.g ((j - 2) / 2))) : Atom X E).WF
      Φ S.v
    split_ifs
    · refine ⟨rfl, fun t ht i hi => ?_, fun _ _ => trivial⟩
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ht
      have hn' := List.mem_range.1 hn
      have : i = 2 * n ∨ i = 2 * n + 1 := by simpa using hi
      show i < 2 * S.nS
      omega
    all_goals exact trivial

theorem fam_places {P : Cb.Place → Prop}
    (hp : ∀ n < S.nS, ∀ b < 2 ^ (S.v + S.w), AllPl P (S.p n b) ∧ AllPl P (S.q n b))
    (ha : ∀ b < 2 ^ S.v, AllPl P (S.a b))
    (hf : ∀ n < S.nQ, ∀ b < 2 ^ S.v, AllPl P (S.f n b) ∧ AllPl P (S.g n b)) :
    ∀ pl ∈ S.fam.places, P pl := by
  rintro pl ⟨j, hj, hpl⟩
  have hj : j < 2 + 2 * S.nQ := hj
  have hpl : pl ∈
      (if j = 0 then Atom.sum S.w S.inner
        else if j = 1 then .base (.cell S.a)
        else
          .base (.cell (if j % 2 = 0 then S.f ((j - 2) / 2)
                  else S.g ((j - 2) / 2))) : Atom X E).places S.v := hpl
  split_ifs at hpl with h0 h1 h2
  · obtain ⟨i, hi, hpl⟩ := hpl
    have hi : i < 2 * S.nS := hi
    have hpl : pl ∈
        (Atom0.cell (if i % 2 = 0 then S.p (i / 2) else S.q (i / 2)) : Atom0 E).places
          (S.v + S.w) := hpl
    obtain ⟨b, hb, t, ht, rfl⟩ := hpl
    split_ifs at ht
    · exact (hp (i / 2) (by omega) b hb).1 _ (List.mem_map_of_mem ht)
    · exact (hp (i / 2) (by omega) b hb).2 _ (List.mem_map_of_mem ht)
  · obtain ⟨b, hb, t, ht, rfl⟩ := hpl
    exact ha b hb _ (List.mem_map_of_mem ht)
  · obtain ⟨b, hb, t, ht, rfl⟩ := hpl
    exact (hf ((j - 2) / 2) (by omega) b hb).1 _ (List.mem_map_of_mem ht)
  · obtain ⟨b, hb, t, ht, rfl⟩ := hpl
    exact (hf ((j - 2) / 2) (by omega) b hb).2 _ (List.mem_map_of_mem ht)

end QSpec
end Cm.Seg
