-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/KeyPort.lean: the keys of a lookup of a key file, from the public runs of rows
themselves; when they cover a forest of the library.

Definitions, statements and proofs. In the verifier that is written after the programs a lookup of
the item "ranges" (`WfLookup`, OnBytes/Params/Items.lean; OnBytes/Key/Ranges.lean) has parts; a part
has places; runs cover places; for digit q the place firstPlace + p of a run reads the row firstRow
+ p + q stride of the matrix; a place in no run is padding and holds a public key. This file writes
the offsets and the row factors of a part from these records, in the form of
Johnson/Pack/KeyRuns.lean, and shows when the parts cover a forest (`Covers`).
Main names:
  `hasPl`, `runIn`, `rowOf`: a run covers a place; the first run of a list that does; the matrix's
    row of a digit at a place.
  `runsOk_ge`, `runIn_eq`, `runIn_some`: runs that pass the verifier's test `Wf.runsOk` rise without
    overlap and stay inside the part; so the run that covers a place is the one that is found.
  `noGap_mem`, `covers_rows`: the verifier's test `Wf.coversAllRows` gives: one digit of weight 1,
    and every row of the matrix is read by a run of a part.
  `oP`, `coP`, `partAt`: the offset and the row factors at a place of a part; part number f.
  `covers_first`: a lookup of one digit of weight 1, whose runs pass `Wf.runsOk`, stay inside the
    matrix and reach every row, covers a forest that has one row of keys for each row of the matrix.
  `covers_gen`: for any number of digits: the parts cover a forest with m live rows of keys, of
    which row v reads the row Y v q for digit q, if (P1) every covered place reads the rows of some
    live row of keys and (P2) every live row of keys is read at some covered place.
Limits: what is asked of the forest (`live`, `idle`) and, in `covers_gen`, (P1) and (P2) are
hypotheses; no lookup of any key file is given here. A row number of the programs' matrix is taken
as the same row number of the matrix over which the row factors stand; that the two matrices hold
the same entries at the same rows is not said. Nothing on multiplicities: a row that is read at two
places passes, and padding that a lookup does not count is not spoken of.
-/
import Johnson.Pack.KeyRuns
import OnBytes.Key.Ranges
import OnBytes.Slice.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Blocks Cb.Lkp OnBytes.Slice
open OnBytes.Params (WfRun WfPart WfLookup)

/-- The run covers the place. -/
def hasPl (r : WfRun) (u : ℕ) : Prop := r.firstPlace ≤ u ∧ u < r.firstPlace + r.places

instance (r : WfRun) (u : ℕ) : Decidable (hasPl r u) := by unfold hasPl; infer_instance

/-- The first run of a list that covers the place. -/
def runIn (rs : List WfRun) (u : ℕ) : Option WfRun := rs.find? fun r => decide (hasPl r u)

/-- The matrix's row of digit q at the place u of the run r. -/
def rowOf (r : WfRun) (u q : ℕ) : ℕ := r.firstRow + (u - r.firstPlace) + q * r.stride

/-- Runs that pass the verifier's test rise without overlap and stay inside the part. -/
theorem runsOk_ge (lp : ℕ) : ∀ (rs : List WfRun) (upto : ℕ), OnBytes.Wf.runsOk lp upto rs = true →
    ∀ r ∈ rs, upto ≤ r.firstPlace ∧ r.firstPlace + r.places ≤ 2 ^ lp
  | [], _, _, _, hr => absurd hr (List.not_mem_nil)
  | a :: rs, upto, h, r, hr => by
    unfold OnBytes.Wf.runsOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨h2, by omega⟩
    · have := runsOk_ge lp rs _ h5 r hr
      exact ⟨by omega, this.2⟩

/-- Among such runs the one that covers a place is found. -/
theorem runIn_eq (lp : ℕ) : ∀ (rs : List WfRun) (upto : ℕ), OnBytes.Wf.runsOk lp upto rs = true →
    ∀ r ∈ rs, ∀ u, hasPl r u → runIn rs u = some r
  | [], _, _, _, hr, _, _ => absurd hr (List.not_mem_nil)
  | a :: rs, upto, h, r, hr, u, hu => by
    have h' := h
    unfold OnBytes.Wf.runsOk at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨_, h5⟩ := h'
    unfold runIn
    by_cases ha : hasPl a u
    · rw [List.find?_cons_of_pos (by simpa using ha)]
      rcases List.mem_cons.1 hr with rfl | hr
      · rfl
      · exfalso
        have := (runsOk_ge lp rs _ h5 r hr).1
        have h1 := hu.1
        have h2 := ha.2
        omega
    · rw [List.find?_cons_of_neg (by simpa using ha)]
      rcases List.mem_cons.1 hr with rfl | hr
      · exact absurd hu ha
      · exact runIn_eq lp rs _ h5 r hr u hu

/-- What is found covers the place and is of the list. -/
theorem runIn_some (rs : List WfRun) (u : ℕ) (r : WfRun) (h : runIn rs u = some r) :
    r ∈ rs ∧ hasPl r u :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- Stretches without a gap from `upto` to `goal` reach every number between. -/
theorem noGap_mem (goal : ℕ) : ∀ (ss : List (ℕ × ℕ)) (upto : ℕ),
    OnBytes.Wf.noGap goal upto ss = true → ∀ y, upto ≤ y → y < goal → ∃ s ∈ ss, s.1 ≤ y ∧ y < s.2
  | [], upto, h, y, h1, h2 => by
    unfold OnBytes.Wf.noGap at h
    simp only [decide_eq_true_eq] at h
    omega
  | s :: ss, upto, h, y, h1, h2 => by
    unfold OnBytes.Wf.noGap at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hy : y < s.2
    · exact ⟨s, List.mem_cons_self, by omega, hy⟩
    · obtain ⟨t, ht, e⟩ := noGap_mem goal ss _ h.2 y (by omega) h2
      exact ⟨t, List.mem_cons_of_mem _ ht, e⟩

/-- The verifier's test that a lookup reaches every row of the matrix gives: one digit of weight 1,
and every row is read by a run of a part. -/
theorem covers_rows (m : OnBytes.Wf.Matrix) (l : WfLookup)
    (h : OnBytes.Wf.coversAllRows m l = true) :
    l.digitWeight = [1] ∧ ∀ y < m.rows, ∃ p ∈ l.parts, ∃ r ∈ p.runs,
      r.firstRow ≤ y ∧ y < r.firstRow + r.places := by
  unfold OnBytes.Wf.coversAllRows at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun y hy => ?_⟩
  obtain ⟨s, hs, e1, e2⟩ := noGap_mem m.rows _ 0 h.2 y (Nat.zero_le _) hy
  rw [List.mem_mergeSort] at hs
  obtain ⟨p, hp, hs⟩ := List.mem_flatMap.1 hs
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
  exact ⟨p, hp, r, hr, e1, e2⟩

/-! ### Offsets and row factors of a part -/

/-- The offset at a place of a part: the lookup's offset where a run covers the place, else the key
of padding. -/
def oP (l : WfLookup) (p : WfPart) (u : ℕ) : GE :=
  algebraMap GF GE (toF (if (runIn p.runs u).isSome then l.offset else l.paddingKey))

/-- The row factors at a place of a part, over a matrix of h rows: each digit's weight at its
row. -/
def coP (h : ℕ) (l : WfLookup) (p : WfPart) (u : ℕ) (r : Fin h) : GE :=
  match runIn p.runs u with
  | none => 0
  | some ρ => ∑ q ∈ Finset.range l.digitWeight.length,
      algebraMap GF GE (toF (l.digitWeight.getD q 0)) * if r.val = rowOf ρ u q then 1 else 0

/-- Part number f of a lookup. -/
def partAt (l : WfLookup) (f : ℕ) : WfPart := l.parts.getD f default

theorem partAt_mem (l : WfLookup) (f : ℕ) (hf : f < l.parts.length) : partAt l f ∈ l.parts := by
  unfold partAt
  rw [List.getD_eq_getElem _ _ hf]
  exact List.getElem_mem hf

theorem cast_toF (a : UInt64) : algebraMap GF GE (toF a) = ((a.toNat : ℕ) : GE) := by
  unfold toF
  exact map_natCast _ _

/-- A lookup of one digit of weight 1 whose runs reach every row covers a forest that has one row of
keys for each row of the matrix. h: the rows of the matrix. oA, coA: the forest's rows of keys. -/
theorem covers_first (h d R : ℕ) (l : WfLookup) (oA : ℕ → GE) (coA : ℕ → Fin h → GE)
    (hw : l.digitWeight = [1])
    (hruns : ∀ p ∈ l.parts, OnBytes.Wf.runsOk p.logPlaces 0 p.runs = true)
    (hfit : ∀ p ∈ l.parts, ∀ r ∈ p.runs, r.firstRow + r.places ≤ h)
    (hcov : ∀ y < h, ∃ p ∈ l.parts, ∃ r ∈ p.runs, r.firstRow ≤ y ∧ y < r.firstRow + r.places)
    (hpad : l.paddingKey.toNat < 2 ^ d) (hR : h ≤ 2 ^ R)
    (live : ∀ v < h, oA v = algebraMap GF GE (toF l.offset) ∧
      coA v = fun r : Fin h => if r.val = v then 1 else 0)
    (idle : ∀ v, h ≤ v → coA v = (fun _ => 0) ∧ ∃ t < 2 ^ d, oA v = ((t : ℕ) : GE)) :
    Covers d (fun u => ((u : ℕ) : GE)) R l.parts.length (fun f => (partAt l f).logPlaces) oA coA
      (fun f => oP l (partAt l f)) (fun f => coP h l (partAt l f)) := by
  have one : ∀ (ρ : WfRun) (u : ℕ), (fun r : Fin h => ∑ q ∈ Finset.range l.digitWeight.length,
      algebraMap GF GE (toF (l.digitWeight.getD q 0)) * if r.val = rowOf ρ u q then 1 else 0) =
      fun r : Fin h => if r.val = rowOf ρ u 0 then (1 : GE) else 0 := by
    intro ρ u
    funext r
    rw [hw]
    show ∑ q ∈ Finset.range 1, _ = _
    rw [Finset.sum_range_one]
    show algebraMap GF GE (toF 1) * _ = _
    rw [toF_one, map_one, one_mul]
  refine ⟨fun f hf u hu => ?_, fun v hv => ?_⟩
  · have hp := partAt_mem l f hf
    cases hr : runIn (partAt l f).runs u with
    | none =>
      left
      refine ⟨?_, l.paddingKey.toNat, hpad, ?_⟩
      · funext r
        show coP h l (partAt l f) u r = 0
        unfold coP
        rw [hr]
      · show oP l (partAt l f) u = _
        unfold oP
        rw [hr]
        exact cast_toF _
    | some ρ =>
      right
      obtain ⟨hm, hh⟩ := runIn_some _ _ _ hr
      have hlt : rowOf ρ u 0 < h := by
        have := hfit _ hp ρ hm
        have h1 := hh.1
        have h2 := hh.2
        unfold rowOf
        omega
      refine ⟨rowOf ρ u 0, lt_of_lt_of_le hlt hR, ?_, ?_⟩
      · show oP l (partAt l f) u = _
        unfold oP
        rw [hr, (live _ hlt).1]
        rfl
      · rw [(live _ hlt).2, ← one ρ u]
        funext r
        show coP h l (partAt l f) u r = _
        unfold coP
        rw [hr]
  · by_cases hlt : v < h
    · right
      obtain ⟨p, hp, ρ, hρ, e1, e2⟩ := hcov v hlt
      obtain ⟨f, hf, rfl⟩ := List.getElem_of_mem hp
      have hpa : partAt l f = l.parts[f] := by
        unfold partAt
        exact List.getD_eq_getElem _ _ hf
      have hh : hasPl ρ (ρ.firstPlace + (v - ρ.firstRow)) := ⟨Nat.le_add_right _ _, by omega⟩
      have hr := runIn_eq _ _ 0 (hruns _ hp) ρ hρ _ hh
      have hb := (runsOk_ge _ _ 0 (hruns _ hp) ρ hρ).2
      have hrow : rowOf ρ (ρ.firstPlace + (v - ρ.firstRow)) 0 = v := by
        unfold rowOf
        omega
      refine ⟨f, hf, ρ.firstPlace + (v - ρ.firstRow), ?_, ?_, ?_⟩
      · show _ < 2 ^ (partAt l f).logPlaces
        rw [hpa]
        have := hh.2
        omega
      · show oP l (partAt l f) _ = _
        unfold oP
        rw [hpa, hr, (live _ hlt).1]
        rfl
      · rw [(live _ hlt).2, ← hrow, ← one ρ _, hrow]
        funext r
        show coP h l (partAt l f) _ r = _
        unfold coP
        rw [hpa, hr]
    · left
      exact idle v (Nat.le_of_not_lt hlt)

/-- The same for any number of digits. The forest has m live rows of keys; row v reads, for digit q,
the matrix's row Y v q, with the lookup's weights and offset. (P1) every covered place reads the
rows of some live row of keys; (P2) every live row of keys is read at some covered place. -/
theorem covers_gen (h d R m : ℕ) (l : WfLookup) (oA : ℕ → GE) (coA : ℕ → Fin h → GE)
    (Y : ℕ → ℕ → ℕ)
    (hruns : ∀ p ∈ l.parts, OnBytes.Wf.runsOk p.logPlaces 0 p.runs = true)
    (hpad : l.paddingKey.toNat < 2 ^ d) (hR : m ≤ 2 ^ R)
    (live : ∀ v < m, oA v = algebraMap GF GE (toF l.offset) ∧
      coA v = fun r : Fin h => ∑ q ∈ Finset.range l.digitWeight.length,
        algebraMap GF GE (toF (l.digitWeight.getD q 0)) * if r.val = Y v q then 1 else 0)
    (idle : ∀ v, m ≤ v → coA v = (fun _ => 0) ∧ ∃ t < 2 ^ d, oA v = ((t : ℕ) : GE))
    (P1 : ∀ p ∈ l.parts, ∀ ρ ∈ p.runs, ∀ u, hasPl ρ u →
      ∃ v < m, ∀ q < l.digitWeight.length, Y v q = rowOf ρ u q)
    (P2 : ∀ v < m, ∃ p ∈ l.parts, ∃ ρ ∈ p.runs, ∃ u, hasPl ρ u ∧
      ∀ q < l.digitWeight.length, Y v q = rowOf ρ u q) :
    Covers d (fun u => ((u : ℕ) : GE)) R l.parts.length (fun f => (partAt l f).logPlaces) oA coA
      (fun f => oP l (partAt l f)) (fun f => coP h l (partAt l f)) := by
  have same : ∀ (ρ : WfRun) (u v : ℕ), (∀ q < l.digitWeight.length, Y v q = rowOf ρ u q) →
      (fun r : Fin h => ∑ q ∈ Finset.range l.digitWeight.length,
        algebraMap GF GE (toF (l.digitWeight.getD q 0)) * if r.val = rowOf ρ u q then 1 else 0) =
      fun r : Fin h => ∑ q ∈ Finset.range l.digitWeight.length,
        algebraMap GF GE (toF (l.digitWeight.getD q 0)) *
          if r.val = Y v q then (1 : GE) else 0 := by
    intro ρ u v e
    funext r
    exact Finset.sum_congr rfl fun q hq => by rw [e q (Finset.mem_range.1 hq)]
  refine ⟨fun f hf u hu => ?_, fun v hv => ?_⟩
  · have hp := partAt_mem l f hf
    cases hr : runIn (partAt l f).runs u with
    | none =>
      left
      refine ⟨?_, l.paddingKey.toNat, hpad, ?_⟩
      · funext r
        show coP h l (partAt l f) u r = 0
        unfold coP
        rw [hr]
      · show oP l (partAt l f) u = _
        unfold oP
        rw [hr]
        exact cast_toF _
    | some ρ =>
      right
      obtain ⟨hm, hh⟩ := runIn_some _ _ _ hr
      obtain ⟨v, hv, e⟩ := P1 _ hp ρ hm u hh
      refine ⟨v, lt_of_lt_of_le hv hR, ?_, ?_⟩
      · show oP l (partAt l f) u = _
        unfold oP
        rw [hr, (live _ hv).1]
        rfl
      · rw [(live _ hv).2, ← same ρ u v e]
        funext r
        show coP h l (partAt l f) u r = _
        unfold coP
        rw [hr]
  · by_cases hlt : v < m
    · right
      obtain ⟨p, hp, ρ, hρ, u, hh, e⟩ := P2 v hlt
      obtain ⟨f, hf, rfl⟩ := List.getElem_of_mem hp
      have hpa : partAt l f = l.parts[f] := by
        unfold partAt
        exact List.getD_eq_getElem _ _ hf
      have hr := runIn_eq _ _ 0 (hruns _ hp) ρ hρ _ hh
      have hb := (runsOk_ge _ _ 0 (hruns _ hp) ρ hρ).2
      refine ⟨f, hf, u, ?_, ?_, ?_⟩
      · show _ < 2 ^ (partAt l f).logPlaces
        rw [hpa]
        have := hh.2
        omega
      · show oP l (partAt l f) _ = _
        unfold oP
        rw [hpa, hr, (live _ hlt).1]
        rfl
      · rw [(live _ hlt).2, ← same ρ u v e]
        funext r
        show coP h l (partAt l f) _ r = _
        unfold coP
        rw [hpa, hr]
    · left
      exact idle v (Nat.le_of_not_lt hlt)

end Johnson.Pack

#print axioms Johnson.Pack.covers_gen
#print axioms Johnson.Pack.covers_first
#print axioms Johnson.Pack.runIn_eq
#print axioms Johnson.Pack.covers_rows
