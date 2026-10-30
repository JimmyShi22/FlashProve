-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Lemma2a.lean: LEMMA 2a, PROVED: `Lemma2aStatement` of HeadLaw.lean: at every
point the two guests and the five keys are the sums of their corner values under the equality
weights. The statement's equalities are between elements of E: both sides are outputs of the field's
addition, hence written canonically, and the reading is one-to-one on such (`eq_of_rd`); read in the
field, both sides are the closed form of General.lean. The tests on the plan are not used.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.General

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE addE mulE okE)
open OnBytes.Model (Aff)
open Norm (lt ls d lPd T S2)

/-! ## Canonical elements -/

theorem okE_addE (a b : E) : okE (addE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.addE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.addE
  simp [Fmt.Fld.ok_add]

theorem okE_zero : okE (0 : E) = true := by decide

theorem okE_sumTo (n : Nat) (f : Nat → E) : okE (sumTo n f) = true := by
  unfold sumTo
  cases n with
  | zero => exact okE_zero
  | succ n =>
    rw [List.range_succ, List.foldl_append]
    exact okE_addE _ _

theorem okE_addMul (a b : Aff) (k : E) : okE (Aff.addMul a b k).const = true := okE_addE _ _

theorem eq_of_rd {a b : E} (ha : okE a = true) (hb : okE b = true) (h : rd a = rd b) : a = b :=
  OnBytes.Slice.readE_inj a b ha hb h

variable [Sizes] [Policy] [Request] [Token]

theorem okE_keyAt (c : Cells) (p : Pt) (k : Key) : okE (keyAt c p k) = true := by
  cases k <;> exact okE_addMul _ _ _

theorem okE_clipAt (c : Cells) (p : Pt) : okE (clipAt c p) = true := okE_addMul _ _ _
theorem okE_tableAt (c : Cells) (p : Pt) : okE (tableAt c p) = true := okE_addMul _ _ _

/-! ## The forms at a point and at a corner, read -/

section Read
variable (c : Cells)

theorem rd_keyAt (p : Pt) (hzt : p.zt.size = lt) (hreq : Request.ok = true) (hy : y < V) (k : Key) :
    rd (keyAt c p k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      rd (p.ew k x) * rd (eq p.zt t) * keyG c k x t := by
  letI := p.normIn; letI := p.headIn; letI := heardAt c; letI := readsAt c
  show rd (key k).const = _
  rw [← cv_const, cv_keyG (filled_at c p) hzt hreq hy k]
  rfl

theorem rd_keyAt_corner (hreq : Request.ok = true) (hy : y < V) (k : Key) {x t : Nat}
    (hx : x < len k) (ht : t < T) : rd (keyAt c (corner x t) k) = keyG c k x t := by
  rw [rd_keyAt c (corner x t) (size_bits lt t) hreq hy k]
  have hU : ∀ x', rd ((corner x t).ew k x') = if x' = x then 1 else 0 := Ut_corner x t k
  have hW : ∀ t', rd (eq (corner x t).zt t') = if t' = t then 1 else 0 := Wt_corner x ht
  simp only [hU, hW]
  exact dsum_delta hx ht (keyG c k)

theorem rd_clipAt (p : Pt) : rd (clipAt c p) = (Finset.range T).sum fun t =>
    (if costed t = true then rd (eq p.zt t) else 0) * clipG c t := by
  letI := p.normIn; letI := p.headIn; letI := heardAt c; letI := readsAt c
  show rd (clip).const = _
  rw [← cv_const, cv_clip (filled_at c p)]
  rfl

theorem rd_tableAt (p : Pt) : rd (tableAt c p) = (Finset.range T).sum fun t =>
    (if costed t = true then rd (eq p.zt t) else 0) * tableG c t := by
  letI := p.normIn; letI := p.headIn; letI := heardAt c; letI := readsAt c
  show rd (table).const = _
  rw [← cv_const, cv_tableG (filled_at c p)]
  rfl

theorem sum_costed_delta {t : Nat} (ht : t < T) (x : Nat) (Z : Nat → K) :
    ((Finset.range T).sum fun t' =>
      (if costed t' = true then rd (eq (corner x t).zt t') else 0) * Z t')
      = if costed t = true then Z t else 0 := by
  have hW : ∀ t', rd (eq (corner x t).zt t') = if t' = t then 1 else 0 := Wt_corner x ht
  simp only [hW]
  rw [Finset.sum_eq_single t]
  · split <;> simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr ht) h

end Read

/-- **LEMMA 2a.** -/
theorem lemma2a : Lemma2aStatement := by
  intro _ _ _ _ c p hreq hy hzt _
  refine ⟨?_, ?_, ?_⟩
  · apply eq_of_rd (okE_clipAt c p) (okE_sumTo _ _)
    rw [rd_clipAt, rd_sumTo]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [rd_mul, rd_clipAt, sum_costed_delta (Finset.mem_range.mp ht)]
    split <;> simp
  · apply eq_of_rd (okE_tableAt c p) (okE_sumTo _ _)
    rw [rd_tableAt, rd_sumTo]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [rd_mul, rd_tableAt, sum_costed_delta (Finset.mem_range.mp ht)]
    split <;> simp
  · intro k
    apply eq_of_rd (okE_keyAt c p k) (okE_sumTo _ _)
    rw [rd_keyAt c p hzt hreq hy k, rd_sumTo]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [rd_sumTo]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [rd_mul, rd_mul,
      rd_keyAt_corner c hreq hy k (Finset.mem_range.mp hx) (Finset.mem_range.mp ht)]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.lemma2a
