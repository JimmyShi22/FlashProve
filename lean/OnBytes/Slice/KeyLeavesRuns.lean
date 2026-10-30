-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLeavesRuns.lean: the sum of the equality vector times the keys of a part, by runs
and gaps.

The keys of a part (OnBytes/Slice/KeyLeaves.lean: `key`) are a public value at the places of padding
and, at a place that a run covers, a public constant plus a public combination of entries of the
matrix. This file adds them up under the equality vector at a point: the sum is the padding's value
times the equality vector's sum over the gaps between the runs, plus the offset times its sum over
the covered places, plus the value on the matrix of the weights that the pending row puts on the
matrix's rows.

Main definitions: `gaps` (the stretches of places between the runs), `RowsIn` (every row that a run
reads is a row of the matrix).
Main theorems.
 `sumSliceF_eq`, `coveredSumF_eq`   the program's two sums, as sums over numbers.
 `keyAt_pad`       before the first of rising runs a place holds the padding's value.
 `places_split`    a sum over the places, by gaps and runs.
 `rowsW_sum`       a sum over the matrix's rows under the weights of one run and digit.
 `run_rows`        one run's share, as a sum over the matrix's rows.
 `keys_sum`        the whole sum.

Not claimed. Nothing on the program's functions. Nothing on how the gaps are cut into cubes.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeavesEq

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ## The program's two sums -/

/-- The sum of a stretch of a list, as a sum over numbers. -/
theorem sumSliceF_eq : ∀ (n : ℕ) (e : List GE) (a : ℕ),
    sumSliceF e a n = ∑ i ∈ Finset.range n, e.getD (a + i) 0
  | 0, _, _ => by simp [sumSliceF]
  | n + 1, e, a => by
    have ih := sumSliceF_eq n e (a + 1)
    unfold sumSliceF at ih ⊢
    rw [Finset.sum_range_succ']
    by_cases h : a < e.length
    · have h0 : e.getD (a + 0) 0 = e[a] := by rw [Nat.add_zero, List.getD_eq_getElem _ _ h]
      rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.sum_cons, ih, h0, add_comm]
      refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
      rw [show a + 1 + i = a + (i + 1) by omega]
    · have hd : e.drop a = [] := List.drop_eq_nil_of_le (by omega)
      have h0 : e.getD (a + 0) 0 = 0 := List.getD_eq_default _ _ (by omega)
      rw [hd, List.take_nil, List.sum_nil, h0, add_zero]
      exact (Finset.sum_eq_zero fun i _ => List.getD_eq_default _ _ (by omega)).symm

/-- A running sum, from any value. -/
theorem foldl_add_map {α : Type} (f : α → GE) : ∀ (l : List α) (s : GE),
    l.foldl (fun s r => s + f r) s = s + (l.map f).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, foldl_add_map f l, List.map_cons, List.sum_cons, add_assoc]

/-- The sum over the covered places, run by run. -/
theorem coveredSumF_eq (runs : List WfRun) (e : List GE) :
    coveredSumF runs e =
      (runs.map fun r => ∑ i ∈ Finset.range r.places, e.getD (r.firstPlace + i) 0).sum := by
  unfold coveredSumF
  rw [foldl_add_map, zero_add]
  exact congrArg List.sum (List.map_congr_left fun r _ => sumSliceF_eq _ _ _)

/-! ## Runs and gaps -/

/-- The stretches of places from u on, below N, that lie between the runs: first place, and the
place behind the last. -/
def gaps (N : ℕ) : ℕ → List WfRun → List (ℕ × ℕ)
  | u, [] => [(u, N)]
  | u, r :: rs => (u, r.firstPlace) :: gaps N (r.firstPlace + r.places) rs

/-- What the program's test on rising runs says of the first run; the others pass it too. -/
theorem runsOk_cons {lp u : ℕ} {r : WfRun} {rs : List WfRun} (h : Wf.runsOk lp u (r :: rs) = true) :
    1 ≤ r.places ∧ u ≤ r.firstPlace ∧ r.firstPlace + r.places ≤ 2 ^ lp ∧
      Wf.runsOk lp (r.firstPlace + r.places) rs = true := by
  simp only [Wf.runsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, by omega, h5⟩

section
variable (L : LkF) (M : ℕ → ℕ → GE)

/-- Before the first of rising runs a place holds the padding's value. -/
theorem keyAt_pad (lp place col : ℕ) : ∀ (rs : List WfRun) (u : ℕ), Wf.runsOk lp u rs = true →
    place < u → keyAt L M rs place col = L.pad
  | [], _, _, _ => rfl
  | r :: rs, u, h, hp => by
    obtain ⟨_, h2, _, h5⟩ := runsOk_cons h
    unfold keyAt
    rw [if_neg (by omega)]
    exact keyAt_pad lp place col rs _ h5 (by omega)

/-- A sum over the places, by gaps and runs. ev: a weight for each place. eqc: weights on the
columns that add up to 1. -/
theorem places_split (lp nc : ℕ) (ev eqc : ℕ → GE) (hS : ∑ c ∈ Finset.range nc, eqc c = 1) :
    ∀ (rs : List WfRun) (u : ℕ), Wf.runsOk lp u rs = true → u ≤ 2 ^ lp →
      ∑ p ∈ Finset.Ico u (2 ^ lp), ev p * ∑ c ∈ Finset.range nc, eqc c * keyAt L M rs p c =
        L.pad * ((gaps (2 ^ lp) u rs).map fun g => ∑ p ∈ Finset.Ico g.1 g.2, ev p).sum +
          (rs.map fun r => ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places),
            ev p * ∑ c ∈ Finset.range nc, eqc c * runKey L M r p c).sum
  | [], u, _, _ => by
    simp only [keyAt, gaps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, hS, one_mul, mul_comm]
  | r :: rs, u, h, _ => by
    obtain ⟨_, h2, h3, h5⟩ := runsOk_cons h
    have ih := places_split lp nc ev eqc hS rs _ h5 h3
    rw [← Finset.sum_Ico_consecutive _ h2 (by omega : r.firstPlace ≤ 2 ^ lp),
      ← Finset.sum_Ico_consecutive _ (Nat.le_add_right r.firstPlace r.places) h3]
    have e1 : ∑ p ∈ Finset.Ico u r.firstPlace,
        ev p * ∑ c ∈ Finset.range nc, eqc c * keyAt L M (r :: rs) p c =
        L.pad * ∑ p ∈ Finset.Ico u r.firstPlace, ev p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_Ico.1 hp).2
      have hk : ∀ c, keyAt L M (r :: rs) p c = L.pad := fun c =>
        keyAt_pad L M lp p c (r :: rs) r.firstPlace (by
          simp only [Wf.runsOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
          obtain ⟨⟨⟨⟨a1, _⟩, a3⟩, a4⟩, a5⟩ := h
          exact ⟨⟨⟨⟨a1, le_refl _⟩, a3⟩, a4⟩, a5⟩) hp'
      rw [Finset.sum_congr rfl fun c _ => by rw [hk c], ← Finset.sum_mul, hS, one_mul, mul_comm]
    have e2 : ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places),
        ev p * ∑ c ∈ Finset.range nc, eqc c * keyAt L M (r :: rs) p c =
        ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places),
          ev p * ∑ c ∈ Finset.range nc, eqc c * runKey L M r p c := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.mem_Ico.1 hp
      refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
      unfold keyAt
      rw [if_pos hp']
    have e3 : ∑ p ∈ Finset.Ico (r.firstPlace + r.places) (2 ^ lp),
        ev p * ∑ c ∈ Finset.range nc, eqc c * keyAt L M (r :: rs) p c =
        ∑ p ∈ Finset.Ico (r.firstPlace + r.places) (2 ^ lp),
          ev p * ∑ c ∈ Finset.range nc, eqc c * keyAt L M rs p c := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_Ico.1 hp).1
      refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
      conv_lhs => unfold keyAt
      rw [if_neg (by omega)]
    rw [e1, e2, e3, ih]
    simp only [gaps, List.map_cons, List.sum_cons]
    ring

end

/-! ## The weights on the matrix's rows -/

/-- A sum over the matrix's rows under the weights of one run and digit. -/
theorem rowsW_sum (a : ℕ) (e : List GE) (f n : ℕ) (w : GE) (R : ℕ) (X : ℕ → GE) (h : a + n ≤ R) :
    ∑ row ∈ Finset.range R, rowsW a e f n w row * X row =
      ∑ i ∈ Finset.range n, w * e.getD (f + i) 0 * X (a + i) := by
  have hsub : Finset.Ico a (a + n) ⊆ Finset.range R := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 h)
  rw [← Finset.sum_subset hsub fun x _ hx => by
    unfold rowsW
    rw [if_neg fun hc => hx (Finset.mem_Ico.2 hc), zero_mul]]
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold rowsW
  rw [if_pos ⟨Nat.le_add_right a i, by omega⟩, Nat.add_sub_cancel_left]

/-- The shares of a list of digits of one run, as a sum over the matrix's rows. -/
theorem digits_rows (M : ℕ → ℕ → GE) (r : WfRun) (e : List GE) (eqc : ℕ → GE) (nc R : ℕ) :
    ∀ ws : List (GE × ℕ), (∀ w ∈ ws, r.firstRow + w.2 * r.stride + r.places ≤ R) →
      ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places),
          e.getD p 0 * ∑ c ∈ Finset.range nc, eqc c * (ws.map fun w =>
            w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c).sum =
        ∑ row ∈ Finset.range R, ∑ c ∈ Finset.range nc, (ws.map fun w =>
          rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c * M row c
  | [], _ => by simp
  | w :: ws, h => by
    have ih := digits_rows M r e eqc nc R ws fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hw := h w List.mem_cons_self
    have one := rowsW_sum (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 R
      (fun row => ∑ c ∈ Finset.range nc, eqc c * M row c) hw
    simp only [List.map_cons, List.sum_cons]
    have eL : ∀ p, e.getD p 0 * ∑ c ∈ Finset.range nc, eqc c *
        (w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c + (ws.map fun w =>
            w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c).sum) =
        e.getD p 0 * ∑ c ∈ Finset.range nc, eqc c *
          (w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c) +
        e.getD p 0 * ∑ c ∈ Finset.range nc, eqc c * (ws.map fun w =>
            w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c).sum := by
      intro p
      rw [← mul_add, ← Finset.sum_add_distrib]
      exact congrArg _ (Finset.sum_congr rfl fun c _ => by ring)
    rw [Finset.sum_congr rfl fun p _ => eL p, Finset.sum_add_distrib, ih]
    have eR : ∀ row, ∑ c ∈ Finset.range nc,
        (rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row + (ws.map fun w =>
          rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum) * eqc c *
            M row c =
        rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row *
            ∑ c ∈ Finset.range nc, eqc c * M row c +
          ∑ c ∈ Finset.range nc, (ws.map fun w =>
            rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c *
              M row c := by
      intro row
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun row _ => eR row, Finset.sum_add_distrib, one]
    refine congrArg (· + _) ?_
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum,
      show r.firstRow + i + w.2 * r.stride = r.firstRow + w.2 * r.stride + i by omega]
    exact Finset.sum_congr rfl fun c _ => by ring

/-- One run's share: the offset times the weights of its places, and a sum over the matrix's
rows. -/
theorem run_rows (L : LkF) (M : ℕ → ℕ → GE) (r : WfRun) (e : List GE) (eqc : ℕ → GE) (nc R : ℕ)
    (hS : ∑ c ∈ Finset.range nc, eqc c = 1)
    (h : ∀ w ∈ L.dw.zipIdx, r.firstRow + w.2 * r.stride + r.places ≤ R) :
    ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places),
        e.getD p 0 * ∑ c ∈ Finset.range nc, eqc c * runKey L M r p c =
      L.off * ∑ i ∈ Finset.range r.places, e.getD (r.firstPlace + i) 0 +
        ∑ row ∈ Finset.range R, ∑ c ∈ Finset.range nc, (L.dw.zipIdx.map fun w =>
          rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c *
            M row c := by
  have hoff : ∑ i ∈ Finset.range r.places, L.off * e.getD (r.firstPlace + i) 0 =
      ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places), L.off * e.getD p 0 := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [← digits_rows M r e eqc nc R L.dw.zipIdx h, Finset.mul_sum, hoff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold runKey
  have : ∑ c ∈ Finset.range nc, eqc c * (L.off + (L.dw.zipIdx.map fun w =>
      w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c).sum) =
      L.off + ∑ c ∈ Finset.range nc, eqc c * (L.dw.zipIdx.map fun w =>
        w.1 * M (r.firstRow + (p - r.firstPlace) + w.2 * r.stride) c).sum := by
    rw [Finset.sum_congr rfl fun c _ => mul_add (eqc c) L.off _, Finset.sum_add_distrib,
      ← Finset.sum_mul, hS, one_mul]
  rw [this]
  ring

/-! ## The whole sum -/

/-- Every row that a run reads, for every digit, is one of the first R rows. -/
def RowsIn (L : LkF) (R : ℕ) (runs : List WfRun) : Prop :=
  ∀ r ∈ runs, ∀ w ∈ L.dw.zipIdx, r.firstRow + w.2 * r.stride + r.places ≤ R

/-- The gaps between rising runs end at or before the part's end. -/
theorem gaps_le (lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ), Wf.runsOk lp u rs = true →
    ∀ g ∈ gaps (2 ^ lp) u rs, g.2 ≤ 2 ^ lp
  | [], _, _, g, hg => by
    rw [gaps, List.mem_singleton] at hg
    rw [hg]
  | r :: rs, u, h, g, hg => by
    obtain ⟨_, _, h3, h5⟩ := runsOk_cons h
    rw [gaps] at hg
    rcases List.mem_cons.1 hg with hg | hg
    · rw [hg]
      show r.firstPlace ≤ 2 ^ lp
      omega
    · exact gaps_le lp rs _ h5 g hg

/-- All runs' shares. -/
theorem runs_rows (L : LkF) (M : ℕ → ℕ → GE) (e : List GE) (eqc : ℕ → GE) (nc R : ℕ)
    (hS : ∑ c ∈ Finset.range nc, eqc c = 1) : ∀ runs : List WfRun, RowsIn L R runs →
      (runs.map fun r => ∑ p ∈ Finset.Ico r.firstPlace (r.firstPlace + r.places),
          e.getD p 0 * ∑ c ∈ Finset.range nc, eqc c * runKey L M r p c).sum =
        coveredSumF runs e * L.off +
          ∑ row ∈ Finset.range R, ∑ c ∈ Finset.range nc, (runs.flatMap fun r =>
            L.dw.zipIdx.map fun w =>
              rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c *
                M row c
  | [], _ => by simp [coveredSumF]
  | r :: rs, h => by
    have ih := runs_rows L M e eqc nc R hS rs fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [coveredSumF_eq] at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, run_rows L M r e eqc nc R hS (h r List.mem_cons_self),
      List.map_cons, List.sum_cons]
    have eR : ∀ row, ∑ c ∈ Finset.range nc, ((r :: rs).flatMap fun r =>
          L.dw.zipIdx.map fun w =>
            rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c *
              M row c =
        ∑ c ∈ Finset.range nc, (L.dw.zipIdx.map fun w =>
            rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c *
              M row c +
          ∑ c ∈ Finset.range nc, (rs.flatMap fun r =>
            L.dw.zipIdx.map fun w =>
              rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum * eqc c *
                M row c := by
      intro row
      rw [List.flatMap_cons, List.sum_append, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun row _ => eR row, Finset.sum_add_distrib]
    ring

/-- The sum of the equality vector times the keys of a part: the padding's value times the
equality vector's sum over the gaps, the offset times its sum over the covered places, and the value
on the matrix of the pending row's weights. -/
theorem keys_sum (L : LkF) (M : ℕ → ℕ → GE) (kCol lp R : ℕ) (runs : List WfRun) (z : List GE)
    (hz : z.length = kCol + lp) (hr : Wf.runsOk lp 0 runs = true) (hR : RowsIn L R runs)
    (claim : KeysF) :
    ∑ i ∈ Finset.range (2 ^ (kCol + lp)), eqW z i * key L M kCol runs i =
      L.pad * ((gaps (2 ^ lp) 0 runs).map fun g =>
          ∑ p ∈ Finset.Ico g.1 g.2, eqW (z.drop kCol) p).sum +
        coveredSumF runs (eqPlacesF kCol z) * L.off +
        ∑ row ∈ Finset.range R, ∑ c ∈ Finset.range (2 ^ kCol),
          (pendingRowF kCol L runs claim (eqPlacesF kCol z)).g row * eqW (z.take kCol) c *
            M row c := by
  have hk : (z.take kCol).length = kCol := by rw [List.length_take, hz]; omega
  have hd : (z.drop kCol).length = lp := by rw [List.length_drop, hz]; omega
  have hS : ∑ c ∈ Finset.range (2 ^ kCol), eqW (z.take kCol) c = 1 := by
    have := eqW_sum (z.take kCol)
    rwa [hk] at this
  have he : ∀ p, p < 2 ^ lp → (eqPlacesF kCol z).getD p 0 = eqW (z.drop kCol) p := fun p hp =>
    eqTableF_getD (z.drop kCol) p (by rw [hd]; exact hp)
  -- by place and column
  have e1 : ∑ i ∈ Finset.range (2 ^ (kCol + lp)), eqW z i * key L M kCol runs i =
      ∑ p ∈ Finset.Ico 0 (2 ^ lp), (eqPlacesF kCol z).getD p 0 *
        ∑ c ∈ Finset.range (2 ^ kCol), eqW (z.take kCol) c * keyAt L M runs p c := by
    rw [pow_add, sum_range_mul, ← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [he p (Finset.mem_range.1 hp), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' := Finset.mem_range.1 hc
    have ea := eqW_append (z.take kCol) (z.drop kCol) c p (by rw [hk]; exact hc')
    rw [List.take_append_drop, hk] at ea
    have h1 : (c + 2 ^ kCol * p) / 2 ^ kCol = p := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos kCol), Nat.div_eq_of_lt hc', Nat.zero_add]
    have h2 : (c + 2 ^ kCol * p) % 2 ^ kCol = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc']
    unfold key
    rw [ea, h1, h2]
    ring
  rw [e1, places_split L M lp (2 ^ kCol) _ _ hS runs 0 hr (Nat.zero_le _),
    runs_rows L M _ _ (2 ^ kCol) R hS runs hR, ← add_assoc]
  refine congrArg (· + _) (congrArg (· + _) (congrArg _ (congrArg List.sum
    (List.map_congr_left fun g hg => Finset.sum_congr rfl fun p hp => ?_))))
  exact he p (lt_of_lt_of_le (Finset.mem_Ico.1 hp).2 (gaps_le lp runs 0 hr g hg))

end OnBytes.Slice.Leaves
