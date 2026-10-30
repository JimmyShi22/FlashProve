--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesRec.lean: the constraint (rec_gamma) of the linear claim's shared rounds
can be made, and the group of the folded row takes it.

(rec_gamma) says that the answers of the committed table's rows to the table's own out-of-domain
(OOD) sample fold as the rows do (Johnson/Desc/K14/Text.lean: recGamma). It is a row on the message
o_u alone: the equality vector at the seed's point, cut below a row's message length, and single
entries on the places of the rows' own pads, which lie inside that length.

Main names:
  foldlM_madd_makes   the loop that adds up products of two vectors' entries returns where the
                      entries are there
  recGamma_makes      **(rec_gamma) can be made**: the seed's point has the planned number of
                      coordinates, the weights and the key's answers have the planned lengths,
                      and the seed's number is below the number of answers
  padPlace_lt         a place of a row's pad lies inside the row's message
  recRow_far          (rec_gamma) reads as 0 on every entry of o_u's main table whose number is at
                      least the message length, on o_u's mask table, and on every other message
  recGamma_fits       **the group takes it** (Fits), where o_u sits in the group with its own pad
                      at entries numbered at least a row's message length

What is not claimed. That o_u sits so at any statement. Nothing on what the constraint means, on
soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesCut
import Johnson.Desc.Key.Laid.RowsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Fits)
open OnBytes.Slice (index_entryAt entryAt_lt)
open VerifiableInference.Desc.Key.LaidW (laid_kind)
open Desc.K14.Law (padList recCoeff recRow recGamma_inv coefficient_foldl_units coefficient_addLaid
  coefficient_empty le_two_pow_ceilLog2 index_lt tensorBelow_mem sum_map_zero)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The loop that adds up products of two vectors' entries returns where the entries are there. -/
theorem foldlM_madd_makes (w y : Array E) (g : Nat → Nat) : ∀ (l : List Nat) (a : E),
    (∀ r ∈ l, r < w.size ∧ g r < y.size) →
    ∃ b, l.foldlM (fun t r => do pure (maddE t (← w[r]?) (← y[g r]?))) a = some b := by
  intro l
  induction l with
  | nil =>
    intro a _
    exact ⟨a, rfl⟩
  | cons r l ih =>
    intro a h
    obtain ⟨h1, h2⟩ := h r List.mem_cons_self
    obtain ⟨b, hb⟩ := ih (maddE a w[r] y[g r]) fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨b, ?_⟩
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    exact ⟨_, ⟨w[r], Array.getElem?_eq_getElem h1, y[g r], Array.getElem?_eq_getElem h2, rfl⟩, hb⟩

/-- The equality vector at a point has one variable for each coordinate. -/
theorem vars_eq (z : List E) (s : E) : (Tensor.eq z s).vars = z.length := by
  simp only [Tensor.eq, Tensor.vars, List.length_map]

/-- **(rec_gamma) can be made.** -/
theorem recGamma_makes (s : IndexShape) (seed : SampleSeed) (i : Nat) (w y : Array E)
    (u : FoldedRow) (hz : seed.z.length = s.cubeBits) (hw : w.size = s.rows)
    (hy : y.size = s.rows * s.answers) (hi : i < s.answers) :
    ∃ row, recGamma s seed i w y u = some row := by
  obtain ⟨L, hL⟩ := tensorBelow_makes (Tensor.eq seed.z) rfl 0 s.cubeBits s.code.ell
    (by rw [vars_eq, hz]; omega) (le_two_pow_ceilLog2 _)
  obtain ⟨sum, hs⟩ := foldlM_madd_makes w y (fun r => r * s.answers + i) (List.range s.rows) zeroE
    (by
      intro r hr
      have hr' := List.mem_range.1 hr
      refine ⟨by rw [hw]; exact hr', ?_⟩
      rw [hy]
      calc r * s.answers + i < r * s.answers + s.answers := by omega
        _ = (r + 1) * s.answers := by rw [Nat.succ_mul]
        _ ≤ s.rows * s.answers := Nat.mul_le_mul_right _ hr')
  refine ⟨{ recRow s seed i u L with target := sum }, ?_⟩
  unfold recGamma
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
  exact ⟨L, hL, sum, hs, rfl⟩

/-- A place of a row's pad lies inside the row's message. -/
theorem padPlace_lt (s : IndexShape) (hok : s.ok = true) (x : Nat × Nat) (hx : x ∈ padList s) :
    s.padPlace x.1 x.2 < s.code.ell := by
  simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hp0 : s.pads < s.code.ell := by tauto
  simp only [padList, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨a, ha, t, ht, rfl⟩ := hx
  show s.padPlace a t < s.code.ell
  unfold IndexShape.padPlace IndexShape.plain
  unfold IndexShape.pads at hp0 ⊢
  omega

/-- (rec_gamma)'s coefficient on an entry. -/
theorem recRow_coefficient (s : IndexShape) (seed : SampleSeed) (i : Nat) (u : FoldedRow)
    (L : List Tensor) (sum : E) (o : Nat) (pt : Part) (idx : Nat) :
    ρ.val (({ recRow s seed i u L with target := sum } : Row).coefficient o pt idx) =
      if u.oracle = o ∧ Part.main = pt then
        (L.map fun t => ρ.val ((u.lay.onTable t).entry idx)).sum +
        ((padList s).map fun x =>
          if u.lay.index (s.padPlace x.1 x.2) = idx then ρ.val (recCoeff s seed i x)
          else 0).sum else 0 := by
  show ρ.val ((recRow s seed i u L).coefficient o pt idx) = _
  unfold recRow FoldedRow.addAll
  rw [coefficient_foldl_units, coefficient_addLaid, coefficient_empty, zero_add]
  split_ifs <;> simp

/-- (rec_gamma) reads as 0 on every entry of o_u's main table whose number is at least a row's
message length, and on every other table. -/
theorem recRow_far (s : IndexShape) (seed : SampleSeed) (i : Nat) (u : FoldedRow)
    (L : List Tensor) (sum : E) (hok : s.ok = true) (hz : seed.z.length = s.cubeBits)
    (hL : tensorBelow (Tensor.eq seed.z) 0 s.cubeBits s.code.ell = some L)
    (hroom : s.cubeBits ≤ u.lay.bits) (o : Nat) (pt : Part) (idx : Nat)
    (hfar : u.oracle = o → Part.main = pt →
      idx < 2 ^ u.lay.bits ∧ s.code.ell ≤ u.lay.entryAt idx) :
    ρ.val (({ recRow s seed i u L with target := sum } : Row).coefficient o pt idx) = 0 := by
  rw [recRow_coefficient]
  by_cases h : u.oracle = o ∧ Part.main = pt
  · rw [if_pos h]
    obtain ⟨hi, hk⟩ := hfar h.1 h.2
    have e := index_entryAt u.lay idx hi
    have hkl := entryAt_lt u.lay idx hi
    have hv : (Tensor.eq seed.z).vars = s.cubeBits := by rw [vars_eq, hz]
    have z1 := laid_cut_zero ρ u.lay (Tensor.eq seed.z) rfl 0 s.cubeBits s.code.ell L hL
      (by rw [hv]; exact hroom) (u.lay.entryAt idx) hkl (by
        intro hlt
        rw [hv] at hlt
        rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt]
        exact hk)
    rw [e] at z1
    have hell : s.code.ell ≤ 2 ^ u.lay.bits :=
      Nat.le_trans (le_two_pow_ceilLog2 _) (Nat.pow_le_pow_right (by decide) hroom)
    have z2 : ((padList s).map fun x =>
        if u.lay.index (s.padPlace x.1 x.2) = idx then ρ.val (recCoeff s seed i x)
        else 0).sum = 0 := by
      refine sum_map_zero _ _ fun x hx => if_neg fun e2 => ?_
      have hp := padPlace_lt s hok x hx
      have h3 := VerifiableInference.Desc.Own.entryAt_index u.lay (s.padPlace x.1 x.2) (by
        rw [← Nat.pow_add]
        exact Nat.lt_of_lt_of_le hp hell)
      rw [e2] at h3
      omega
    rw [z1, z2, add_zero]
  · rw [if_neg h]

/-- **The group takes (rec_gamma).** n: the number from which on o_u's entries may mask its own
answers: at least a row's message length. -/
theorem recGamma_fits (T : Statement) (G : Group) (s : IndexShape) (seed : SampleSeed) (i : Nat)
    (w y : Array E) (u : FoldedRow) (row : Row) (n : Nat) (hok : s.ok = true)
    (hz : seed.z.length = s.cubeBits) (h : recGamma s seed i w y u = some row)
    (hS : Sits T G u.oracle u.lay n) (hroom : s.cubeBits ≤ u.lay.bits) (hn : s.code.ell ≤ n) :
    Fits T G row := by
  obtain ⟨L, sum, hL, _, rfl⟩ := recGamma_inv s seed i w y u row h
  have hv : (Tensor.eq seed.z).vars = s.cubeBits := by rw [vars_eq, hz]
  have hell : s.code.ell ≤ 2 ^ u.lay.bits :=
    Nat.le_trans (le_two_pow_ceilLog2 _) (Nat.pow_le_pow_right (by decide) hroom)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (recRow s seed i u L).kind ≠ .sample
    unfold recRow FoldedRow.addAll
    rw [kind_units, laid_kind]
    intro e
    cases e
  · intro t ht
    have ht' : t ∈ (recRow s seed i u L).terms := ht
    unfold recRow FoldedRow.addAll at ht'
    rw [terms_units] at ht'
    rcases mem_addLaid _ _ _ _ _ ht' with h1 | ⟨v, hvL, rfl⟩
    · simp at h1
    · obtain ⟨d1, d2⟩ := tensorBelow_mem _ rfl _ _ _ _ hL v hvL
      exact laid_term_fits hS v d1 (by rw [d2, hv]; exact hroom)
  · intro x hx
    have hx' : x ∈ (recRow s seed i u L).units := hx
    unfold recRow FoldedRow.addAll at hx'
    rcases mem_units _ _ _ _ _ _ hx' with h1 | ⟨a, ha, rfl⟩
    · rw [units_addLaid] at h1
      simp at h1
    · exact entry_fits hS _ (index_lt _ _ (Nat.lt_of_lt_of_le (padPlace_lt s hok a ha) hell))
  · show (recRow s seed i u L).runs = #[]
    unfold recRow FoldedRow.addAll
    rw [runs_units, runs_addLaid]
  · show (recRow s seed i u L).forms = #[]
    unfold recRow FoldedRow.addAll
    rw [forms_units, forms_addLaid]
  · intro o _ x hx q hq
    refine recRow_far Model.Reading.gl s seed i u L sum hok hz hL hroom o q.1 q.2 ?_
    intro e1 e2
    subst e1
    obtain ⟨p1, p2⟩ := hS.pad x hx q hq e2.symm
    exact ⟨p1, Nat.le_trans hn p2⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.foldlM_madd_makes
#print axioms Desc.K14.Honest.vars_eq
#print axioms Desc.K14.Honest.recGamma_makes
#print axioms Desc.K14.Honest.padPlace_lt
#print axioms Desc.K14.Honest.recRow_coefficient
#print axioms Desc.K14.Honest.recRow_far
#print axioms Desc.K14.Honest.recGamma_fits
