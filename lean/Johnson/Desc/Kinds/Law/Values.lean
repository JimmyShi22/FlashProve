-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Values.lean: THE HEAD's FORMS AT A CORNER (L3 of the road), AND LEMMA 1.
At the corner of entry x and position t the weights are 1 at x, t and 0 elsewhere, so each closed form
of Closed.lean is one integer of Ints.lean. So `CellRel` gives `CastRel` (`castRel_of_cellRel`), and
with NoWrap.lean and Ints.lean: `lemma1 : Lemma1Statement`.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE)
open Norm (lt ls d lPd T S2)

/-- A double sum under two deltas is one term. -/
theorem dsum_delta {n m x t : Nat} (hx : x < n) (ht : t < m) (Z : Nat → Nat → K) :
    ((Finset.range n).sum fun x' => (Finset.range m).sum fun t' =>
      (if x' = x then (1 : K) else 0) * (if t' = t then 1 else 0) * Z x' t') = Z x t := by
  rw [Finset.sum_eq_single x, Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr ht) h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr hx) h

variable [Sizes] [Policy] [Request] [Token]

section AtCorner
variable [FinalNorm.In] [In] [Heard] [Reads] {c : Cells} {x t : Nat}

theorem sum_Ph_delta (hW : ∀ t', Wt t' = if t' = t then 1 else 0) (ht : t < T) (Z : Nat → K) :
    ((Finset.range T).sum fun t' => Ph t' * Z t') = if costed t = true then Z t else 0 := by
  rw [Finset.sum_eq_single t]
  · unfold Ph; rw [hW]; split <;> simp
  · intro b _ hb; unfold Ph; rw [hW, if_neg hb]; simp
  · intro h; exact absurd (Finset.mem_range.mpr ht) h

variable (P : PlanFacts) (hF : Filled c) (hW : ∀ t', Wt t' = if t' = t then 1 else 0)
  (hU : ∀ k x', Ut k x' = if x' = x then 1 else 0)
include P hF hW hU

theorem mid_corner (k : Key) (v0 : Nat) (hv : first k = v0) (hv0 : S2 ∣ v0) (hx : x < len k)
    (ht : t < T) : cv (mid k v0) = ((midZ c (v0 + x) t : Int) : K) := by
  rw [cv_mid P hF k v0 hv hv0]
  simp only [hW, hU]
  exact dsum_delta hx ht fun x' t' => ((midZ c (v0 + x') t' : Int) : K)

theorem low_corner (k : Key) (hv : first k = 0) (hx : x < len k) (ht : t < T) :
    cv (low k) = ((lowZ c x t : Int) : K) := by
  rw [cv_low P hF k hv]
  simp only [hW, hU]
  exact dsum_delta hx ht fun x' t' => ((lowZ c x' t' : Int) : K)

theorem tableValue_corner (hzt : (FinalNorm.zt).size = lt) (k : Key) (v0 : Nat) (hv0 : S2 ∣ v0)
    (hx : x < len k) (ht : t < T) : cv (tableValue k v0) = ((tvZ c (v0 + x) t : Int) : K) := by
  rw [cv_tableValue P hF hzt k v0 hv0]
  simp only [hW, hU]
  exact dsum_delta hx ht fun x' t' => ((tvZ c (v0 + x') t' : Int) : K)

theorem top_corner (hreq : Request.ok = true) (hy : y < V) (hx : x < JV) (ht : t < T) :
    cv top = ((2 : K) ^ (sh + 15))⁻¹ * ((topNum c x t : Int) : K) := by
  rw [cv_top P hF hreq hy]
  simp only [hW, hU]
  rw [dsum_delta hx ht fun x' t' => ((topNum c x' t' : Int) : K)]

end AtCorner

/-! ## The classes at the cells and a point -/

theorem filled_at (c : Cells) (p : Pt) :
    letI := p.normIn; letI := p.headIn; letI := heardAt c; letI := readsAt c
    Filled c :=
  letI := p.normIn; letI := p.headIn; letI := heardAt c; letI := readsAt c
  ⟨fun _ _ => rfl, rfl, ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩⟩

theorem Wt_corner (x : Nat) {t : Nat} (ht : t < T) (t' : Nat) :
    letI := (corner x t).normIn
    Wt t' = if t' = t then 1 else 0 :=
  rd_eq_bits (n := lt) ht t'

theorem Ut_corner (x t : Nat) (k : Key) (x' : Nat) :
    letI := (corner x t).headIn
    Ut k x' = if x' = x then 1 else 0 := by
  show rd ((if x' / S2 == x / S2 then (1 : E) else 0) * eq (bits ls (x % S2)) (x' % S2)) = _
  have hS : 0 < S2 := by unfold S2; positivity
  have hm2 : x % S2 < 2 ^ ls := Nat.mod_lt x hS
  rw [rd_mul, rd_eq_bits hm2]
  have h1 := Nat.div_add_mod x S2
  have h2 := Nat.div_add_mod x' S2
  by_cases he : x' = x
  · subst he; simp [rd_one]
  · rw [if_neg he]
    by_cases hq : x' / S2 = x / S2
    · have hm : ¬ x' % S2 = x % S2 := by
        intro hm; apply he; rw [← h2, ← h1, hq, hm]
      rw [if_neg hm, mul_zero]
    · have : (x' / S2 == x / S2) = false := by simpa using hq
      rw [this]; simp [rd_zero]

/-! ## The nine corner values -/

theorem two_pow_ne_zero (n : Nat) : ((2 : K) ^ n) ≠ 0 := by
  apply pow_ne_zero
  intro h
  have h2 : ((2 : Int) : K) = ((0 : Int) : K) := by push_cast; exact h
  have := int_eq_of_cast_eq h2 (by norm_num)
  omega

section Wrap
variable {c : Cells} {x t : Nat}

theorem rd_key_mid (P : PlanFacts) (hx : x < JV) (ht : t < T) :
    rd (keyAt c (corner x t) .marginMid) = ((midZ c x t : Int) : K) := by
  letI := (corner x t).normIn; letI := (corner x t).headIn; letI := heardAt c; letI := readsAt c
  show rd (mid Key.marginMid 0).const = _
  rw [← cv_const, mid_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
    .marginMid 0 rfl (dvd_zero _) hx ht, Nat.zero_add]

theorem rd_key_low (P : PlanFacts) (hx : x < JV) (ht : t < T) :
    rd (keyAt c (corner x t) .marginLow) = ((lowZ c x t : Int) : K) := by
  letI := (corner x t).normIn; letI := (corner x t).headIn; letI := heardAt c; letI := readsAt c
  show rd (low Key.marginLow).const = _
  rw [← cv_const, low_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
    .marginLow rfl hx ht]

theorem rd_key_top (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V) (hx : x < JV)
    (ht : t < T) : rd (keyAt c (corner x t) .marginTop)
      = ((2 : K) ^ (sh + 15))⁻¹ * ((topNum c x t : Int) : K) := by
  letI := (corner x t).normIn; letI := (corner x t).headIn; letI := heardAt c; letI := readsAt c
  show rd (top).const = _
  rw [← cv_const, top_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
    hreq hy hx ht]

theorem size_bits (n i : Nat) : (bits n i).size = n := by simp [bits]

theorem rd_key_tableA (P : PlanFacts) (hx : x < JVa) (ht : t < T) :
    rd (keyAt c (corner x t) .tableA) = ((midZ c x t + 2 ^ 16 * tvZ c x t : Int) : K) := by
  letI := (corner x t).normIn; letI := (corner x t).headIn; letI := heardAt c; letI := readsAt c
  show rd (mid Key.tableA 0 + (2 ^ 16 : Nat) • tableValue Key.tableA 0).const = _
  rw [← cv_const, cv_add, cv_smulN,
    mid_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
      .tableA 0 rfl (dvd_zero _) hx ht,
    tableValue_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
      (size_bits lt t) .tableA 0 (dvd_zero _) hx ht, Nat.zero_add]
  push_cast
  rfl

theorem rd_key_tableB (P : PlanFacts) (hx : x < JV - JVa) (ht : t < T) :
    rd (keyAt c (corner x t) .tableB)
      = ((midZ c (JVa + x) t + 2 ^ 16 * tvZ c (JVa + x) t : Int) : K) := by
  letI := (corner x t).normIn; letI := (corner x t).headIn; letI := heardAt c; letI := readsAt c
  have ha : S2 ∣ JVa := Nat.dvd_of_mod_eq_zero P.hJVa
  show rd (mid Key.tableB JVa + (2 ^ 16 : Nat) • tableValue Key.tableB JVa).const = _
  rw [← cv_const, cv_add, cv_smulN,
    mid_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
      .tableB JVa rfl ha hx ht,
    tableValue_corner P (filled_at c (corner x t)) (Wt_corner x ht) (Ut_corner x t)
      (size_bits lt t) .tableB JVa ha hx ht]
  push_cast
  rfl

theorem rd_clip (ht : t < T) : rd (clipAt c (corner 0 t)) = if costed t = true then
    ((numZ c .paid t + numZ c .slackClip t - (C : Int) : Int) : K) else 0 := by
  letI := (corner 0 t).normIn; letI := (corner 0 t).headIn; letI := heardAt c; letI := readsAt c
  show rd (clip).const = _
  rw [← cv_const, cv_clip (filled_at c (corner 0 t)), sum_Ph_delta (Wt_corner 0 ht) ht]

theorem rd_table (P : PlanFacts) (ht : t < T) : rd (tableAt c (corner 0 t)) =
    if costed t = true then ((numZ c .slackTable t + (Finset.range JV).sum (fun x => tvZ c x t)
      - ((JV - V + 1 : Nat) : Int) * 2 ^ F : Int) : K) else 0 := by
  letI := (corner 0 t).normIn; letI := (corner 0 t).headIn; letI := heardAt c; letI := readsAt c
  show rd (table).const = _
  rw [← cv_const, cv_table P (filled_at c (corner 0 t)), sum_Ph_delta (Wt_corner 0 ht) ht]

theorem rd_mean : rd (meanAt c) = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t
    else 0) - (theta : Int) * (RC : Int) : Int) : K) := by
  letI := (corner 0 0).normIn; letI := (corner 0 0).headIn; letI := heardAt c; letI := readsAt c
  show rd (mean).const = _
  rw [← cv_const, cv_mean (filled_at c (corner 0 0))]

theorem rd_count : rd (countAt c) = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .over t + numZ c .slackCap t else 0)
      - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) := by
  letI := (corner 0 0).normIn; letI := (corner 0 0).headIn; letI := heardAt c; letI := readsAt c
  show rd (count).const = _
  rw [← cv_const, cv_count (filled_at c (corner 0 0))]

end Wrap

/-- If a - b is read as 0 then a and b have one image. -/
theorem cast_eq_of_sub {a b : Int} (h : ((a - b : Int) : K) = 0) : (a : K) = (b : K) := by
  push_cast at h
  exact sub_eq_zero.mp h

/-- **FROM THE RELATION ON CELLS TO EQUALITIES OF CASTS.** -/
theorem castRel_of_cellRel (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V) {c : Cells}
    {tab : Nat → Nat} (h : CellRel c tab) : CastRel c tab where
  small := h.small
  bytes := h.bytes
  mid := fun t ht x hx => by
    obtain ⟨n, hn, he⟩ := h.mid t ht x hx
    refine ⟨n, hn, ?_⟩
    have h1 := congrArg rd he
    rw [rd_key_mid P hx ht, rd_natCast] at h1
    rw [h1, Int.cast_natCast]
  low := fun t ht x hx => by
    obtain ⟨n, hn, he⟩ := h.low t ht x hx
    refine ⟨n, hn, ?_⟩
    have h1 := congrArg rd he
    rw [rd_key_low P hx ht, rd_natCast] at h1
    rw [h1, Int.cast_natCast]
  top := fun t ht x hx => by
    obtain ⟨n, hn, he⟩ := h.top t ht x hx
    refine ⟨n, hn, ?_⟩
    have h1 := congrArg rd he
    rw [rd_key_top P hreq hy hx ht, rd_natCast, inv_mul_eq_iff_eq_mul₀ (two_pow_ne_zero _)] at h1
    rw [h1]
    push_cast
    rfl
  row := fun t ht x hx => by
    by_cases hxa : x < JVa
    · obtain ⟨u, hu, he⟩ := h.rowA t ht x hxa
      refine ⟨u, hu, ?_⟩
      have h1 := congrArg rd he
      rw [rd_key_tableA P hxa ht, rd_natCast] at h1
      rw [h1]
      push_cast
      rfl
    · have hxb : x - JVa < JV - JVa := by omega
      obtain ⟨u, hu, he⟩ := h.rowB t ht (x - JVa) hxb
      refine ⟨u, hu, ?_⟩
      have h1 := congrArg rd he
      have e : JVa + (x - JVa) = x := by omega
      rw [rd_key_tableB P hxb ht, rd_natCast, e] at h1
      rw [h1]
      push_cast
      rfl
  clip := fun t ht hc => by
    have h1 := congrArg rd (h.lines t ht).1
    rw [rd_clip ht, if_pos hc, rd_zero] at h1
    exact cast_eq_of_sub h1
  table := fun t ht hc => by
    have h1 := congrArg rd (h.lines t ht).2
    rw [rd_table P ht, if_pos hc, rd_zero] at h1
    exact cast_eq_of_sub h1
  mean := by
    have h1 := congrArg rd h.sums.1
    rw [rd_mean, rd_zero] at h1
    exact cast_eq_of_sub h1
  count := by
    have h1 := congrArg rd h.sums.2
    rw [rd_count, rd_zero] at h1
    exact cast_eq_of_sub h1

/-- LEMMA 1 WITH LESS ASKED: the bound on act at the positions below T and the features below d
alone: where the normalization's lemma gives it. -/
theorem lemma1_strong {sT : Nat} {tab : Nat → Nat} {c : Cells} (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : y < V) (htab : TableOk tab)
    (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (hA : ∀ t, t < T → ∀ k, k < d → (act c t k).natAbs ≤ 2047) (h : CellRel c tab) : Says c := by
  have P := planFacts hplan
  exact says_of_intRel P.hV2 hreq hy htab
    (intRel_of_castRel P htab hW hA (castRel_of_cellRel P hreq hy h))

/-- **LEMMA 1.** -/
theorem lemma1 : Lemma1Statement := by
  intro _ _ _ _ sT tab c hplan hreq hy htab hW hA h
  exact lemma1_strong hplan hreq hy htab hW (fun t _ k _ => hA t k) h

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.lemma1
#print axioms VerifiableInference.Desc.Kinds.Head.Law.lemma1_strong
