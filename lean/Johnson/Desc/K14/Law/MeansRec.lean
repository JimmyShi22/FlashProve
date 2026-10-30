-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/MeansRec.lean: what the constraint (rec_gamma) says of words.

Main names: value_one (a constraint on one main table, applied to words), sum_units, cut0_sum,
foldlM_madd, recRow, recGamma_inv, recMeansW.

What is not claimed. Nothing on the record's seeds or answers being those of the encoded index.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Means
import Johnson.Desc.K14.Law.LawRL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Sums -/

/-- A sum over a list of the first numbers. -/
theorem list_range_sum (f : Nat → K) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- A sum over the pairs (a, t), a below n, t below k. -/
theorem sum_pairs (n k : Nat) (F : Nat × Nat → K) :
    (((List.range n).flatMap fun a => (List.range k).map fun t => (a, t)).map F).sum =
      ∑ a ∈ Finset.range n, ∑ t ∈ Finset.range k, F (a, t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    exact list_range_sum (fun t => F (n, t)) k

/-- Single coefficients applied to a table. -/
theorem sum_units {α : Type} (P : List α) (idx : α → Nat) (c : α → K) (N : Nat)
    (hP : ∀ x ∈ P, idx x < N) (w : Nat → K) :
    ∑ i ∈ Finset.range N, (P.map fun x => if idx x = i then c x else 0).sum * w i =
      (P.map fun x => c x * w (idx x)).sum := by
  induction P with
  | nil => simp
  | cons x P ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [ih fun y hy => hP y (List.mem_cons_of_mem _ hy)]
    congr 1
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (hP x List.mem_cons_self))]

/-- A sum over the first 2 ^ n indices in which only those below len count. -/
theorem cut0_sum (n len : Nat) (hlen : len ≤ 2 ^ n) (f g : Nat → K) :
    ∑ j ∈ Finset.range (2 ^ n), (if j / 2 ^ 0 % 2 ^ n < len then f j else 0) * g j =
      ∑ j ∈ Finset.range len, f j * g j := by
  refine Eq.trans ?_ (sum_below_len (2 ^ n) len hlen fun j => f j * g j)
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : j / 2 ^ 0 % 2 ^ n = j := by
    rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]
  rw [e]
  split_ifs <;> simp

/-- The loop that adds up products of two vectors' entries. -/
theorem foldlM_madd (w y : Array E) (g : Nat → Nat) : ∀ (l : List Nat) (a b : E),
    l.foldlM (fun t r => do pure (maddE t (← w[r]?) (← y[g r]?))) a = some b →
    ρ.val b = ρ.val a +
      (l.map fun r => ρ.val (w.getD r zeroE) * ρ.val (y.getD (g r) zeroE)).sum := by
  intro l
  induction l with
  | nil =>
    intro a b h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons r l ih =>
    intro a b h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, ⟨x, hx, z, hz, rfl⟩, h2⟩ := h
    rw [ih _ b h2, maddE_val]
    simp only [List.map_cons, List.sum_cons, Array.getD_eq_getD_getElem?, hx, hz, Option.getD_some]
    ring

/-! ## A constraint on one main table -/

/-- A constraint that has coefficients on one main table alone, applied to words. -/
theorem value_one (T : Statement) (row : Row) (o0 bits : Nat) (c : Nat → K)
    (hc : ∀ o pt i, ρ.val (row.coefficient o pt i) =
      if o0 = o ∧ Part.main = pt then c i else 0)
    (hh : T.has o0 .main = true) (hb : T.tableBits o0 .main = bits) (m : Words K) :
    Means.value ρ T row m = ∑ i ∈ Finset.range (2 ^ bits), c i * m o0 .main i := by
  have ts : Means.tableSize T o0 .main = 2 ^ bits := by
    unfold Means.tableSize; rw [if_pos hh, hb]
  have hmask : ∀ o, Means.onTable ρ T row m o .mask = 0 := by
    intro o
    unfold Means.onTable
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hc]; simp
  have hmain : ∀ o, Means.onTable ρ T row m o .main =
      if o0 = o then ∑ i ∈ Finset.range (2 ^ bits), c i * m o0 .main i else 0 := by
    intro o
    unfold Means.onTable
    by_cases h1 : o0 = o
    · subst h1
      rw [if_pos rfl, ts]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc]; simp
    · rw [if_neg h1]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hc]; simp [h1]
  unfold Means.value
  simp only [hmask, hmain, add_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (lt_of_has T _ _ hh))]

/-- Single coefficients added one by one on a main table. -/
theorem coefficient_foldl_units {α : Type} (o' : Nat) (idx : α → Nat) (c : α → E) (P : List α)
    (r0 : Row) (o : Nat) (pt : Part) (i : Nat) :
    ρ.val ((P.foldl (fun r x => r.addUnit o' .main (idx x) (c x)) r0).coefficient o pt i) =
      ρ.val (r0.coefficient o pt i) + if o' = o ∧ Part.main = pt then
        (P.map fun x => if idx x = i then ρ.val (c x) else 0).sum else 0 := by
  induction P generalizing r0 with
  | nil => simp
  | cons x P ih =>
    rw [List.foldl_cons, ih, coefficient_addUnit]
    by_cases h1 : o' = o <;> by_cases h2 : Part.main = pt <;> by_cases h3 : idx x = i <;>
      simp [h1, h2, h3] <;> ring

/-- The index of an entry of a vector that is within the table is within the table. -/
theorem index_lt (lay : VectorLay) (j : Nat) (hj : j < 2 ^ lay.bits) :
    lay.index j < 2 ^ lay.bits := by
  cases h : lay.rowsHigh with
  | false => simpa [VectorLay.index, h] using hj
  | true =>
    have e : 2 ^ lay.bits = 2 ^ lay.rowBits * 2 ^ lay.placeBits := by
      rw [VectorLay.bits, Nat.pow_add]
    rw [index_eq lay h, e, Nat.mul_comm]
    exact swap_lt _ _ _ (by rwa [e] at hj)

/-! ## (rec_gamma) -/

/-- The pads: answer and coordinate. -/
def padList (s : IndexShape) : List (Nat × Nat) :=
  (List.range s.answers).flatMap fun a => (List.range 3).map fun t => (a, t)

/-- The single coefficient of (rec_gamma) on a pad. -/
def recCoeff (s : IndexShape) (seed : SampleSeed) (i : Nat) (x : Nat × Nat) : E :=
  subE (if x.1 == i then mulE seed.beta (thetaE x.2) else zeroE)
    ((Tensor.eq seed.z).entry (s.padPlace x.1 x.2))

/-- (rec_gamma) without its target. L: the equality vector at the seed's point, cut. -/
def recRow (s : IndexShape) (seed : SampleSeed) (i : Nat) (u : FoldedRow) (L : List Tensor) : Row :=
  (padList s).foldl (fun r x =>
    r.addUnit u.oracle .main (u.lay.index (s.padPlace x.1 x.2)) (recCoeff s seed i x))
    (u.addAll {} L)

/-- What (rec_gamma) is made of. -/
theorem recGamma_inv (s : IndexShape) (seed : SampleSeed) (i : Nat) (w y : Array E)
    (u : FoldedRow) (row : Row) (h : recGamma s seed i w y u = some row) :
    ∃ (L : List Tensor) (sum : E),
      tensorBelow (Tensor.eq seed.z) 0 s.cubeBits s.code.ell = some L ∧
      (List.range s.rows).foldlM
        (fun t r => do pure (maddE t (← w[r]?) (← y[r * s.answers + i]?))) zeroE = some sum ∧
      row = { recRow s seed i u L with target := sum } := by
  unfold recGamma at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨L, hL, sum, hs, hrow⟩ := h
  exact ⟨L, sum, hL, hs, hrow.symm⟩

/-- **MEANS**, for (rec_gamma). -/
theorem recMeansW : RecMeansW ρ := by
  intro T S seed i w y u row hok hi hz h hP m
  obtain ⟨L, sum, hL, hs, rfl⟩ := recGamma_inv S.index seed i w y u row h
  simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hp0 : S.index.pads < S.index.code.ell := by tauto
  have hpads : S.index.plain + 3 * S.index.answers = S.index.code.ell := by
    unfold IndexShape.plain
    unfold IndexShape.pads at hp0 ⊢
    omega
  have hell : S.index.code.ell ≤ 2 ^ S.index.cubeBits := le_two_pow_ceilLog2 _
  have hv : (Tensor.eq seed.z).vars = S.index.cubeBits := by
    simp only [Tensor.eq, Tensor.vars, List.length_map, hz]
  have hroom : S.index.cubeBits ≤ u.lay.bits := hP.room
  have hc : ∀ o pt idx,
      ρ.val (({ recRow S.index seed i u L with target := sum } : Row).coefficient o pt idx) =
      if u.oracle = o ∧ Part.main = pt then
        (L.map fun t => ρ.val ((u.lay.onTable t).entry idx)).sum +
        ((padList S.index).map fun x =>
          if u.lay.index (S.index.padPlace x.1 x.2) = idx then ρ.val (recCoeff S.index seed i x)
          else 0).sum else 0 := by
    intro o pt idx
    show ρ.val ((recRow S.index seed i u L).coefficient o pt idx) = _
    unfold recRow FoldedRow.addAll
    rw [coefficient_foldl_units, coefficient_addLaid, coefficient_empty, zero_add]
    split_ifs <;> simp
  have hpl : ∀ x ∈ padList S.index,
      u.lay.index (S.index.padPlace x.1 x.2) < 2 ^ u.lay.bits := by
    intro x hx
    simp only [padList, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    refine index_lt _ _ (lt_of_lt_of_le ?_ (Nat.le_trans hell
      (Nat.pow_le_pow_right (by decide) hroom)))
    unfold IndexShape.padPlace
    omega
  have hco : ∀ x : Nat × Nat, ρ.val (recCoeff S.index seed i x) =
      (if x.1 = i then ρ.val seed.beta * ρ.val (thetaE x.2) else 0) -
        eqK (seed.z.map ρ.val) (S.index.padPlace x.1 x.2) := by
    intro x
    unfold recCoeff
    rw [ρ.sub, entry_eq, ρ.one, one_mul]
    by_cases hx : x.1 = i <;> simp [hx, ρ.mul, ρ.zero]
  have hsum := foldlM_madd ρ w y (fun r => r * S.index.answers + i) _ _ _ hs
  rw [ρ.zero, zero_add, list_range_sum] at hsum
  unfold Means.Says RecEq
  rw [value_one ρ T _ u.oracle u.lay.bits _ hc hP.has hP.bits m]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [cut_laid_sum ρ u.lay _ rfl 0 S.index.cubeBits S.index.code.ell L hL (by rw [hv]; exact hroom),
    hv, cut0_sum _ _ hell, sum_units _ _ _ _ hpl, padList, sum_pairs]
  show _ = ρ.val sum ↔ _
  rw [hsum, ← hpads, Finset.sum_range_add, sum_blocks]
  have key : (∑ a ∈ Finset.range S.index.answers, ∑ t ∈ Finset.range 3,
        ρ.val ((Tensor.eq seed.z).entry (S.index.plain + (t + 3 * a))) *
          m u.oracle .main (u.lay.index (S.index.plain + (t + 3 * a)))) +
      (∑ a ∈ Finset.range S.index.answers, ∑ t ∈ Finset.range 3,
        ρ.val (recCoeff S.index seed i (a, t)) *
          m u.oracle .main (u.lay.index (S.index.padPlace a t))) =
      ∑ t ∈ Finset.range 3, ρ.val seed.beta * ρ.val (thetaE t) *
        m u.oracle .main (u.lay.index (S.index.padPlace i t)) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ a ∈ Finset.range S.index.answers,
        (∑ t ∈ Finset.range 3,
          ρ.val ((Tensor.eq seed.z).entry (S.index.plain + (t + 3 * a))) *
            m u.oracle .main (u.lay.index (S.index.plain + (t + 3 * a)))) +
        (∑ t ∈ Finset.range 3, ρ.val (recCoeff S.index seed i (a, t)) *
          m u.oracle .main (u.lay.index (S.index.padPlace a t))) =
        if i = a then ∑ t ∈ Finset.range 3, ρ.val seed.beta * ρ.val (thetaE t) *
          m u.oracle .main (u.lay.index (S.index.padPlace a t)) else 0 := by
      intro a _
      rw [← Finset.sum_add_distrib]
      by_cases hia : i = a
      · rw [if_pos hia]
        refine Finset.sum_congr rfl fun t _ => ?_
        have e : S.index.plain + (t + 3 * a) = S.index.padPlace a t := by
          unfold IndexShape.padPlace; omega
        rw [e, hco, entry_eq, ρ.one, one_mul]
        simp only [hia, if_true]
        ring
      · rw [if_neg hia]
        refine Finset.sum_eq_zero fun t _ => ?_
        have e : S.index.plain + (t + 3 * a) = S.index.padPlace a t := by
          unfold IndexShape.padPlace; omega
        rw [e, hco, entry_eq, ρ.one, one_mul]
        simp only [Ne.symm hia, if_false]
        ring
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hi)]
  rw [add_assoc, key]
  simp only [entry_eq, ρ.one, one_mul]

end Desc.K14.Law
