-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Ends.lean: THE TWO END VALUES OF THE HEAD's ONE SUMCHECK (bridge B6 of Lemma 2b).
`mle_at_r`: a table over positions and features, extended at the challenges r, is the double sum under
the equality weights of r's first lt and next lPd coordinates (HeadCells.lean's rH and rs).
`weights_eq`: the sum that the claim on the committed weights names is UH's table at the challenges.
`actForm_value`: the value of logitForms' second form in a world.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.LedgerAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)
open OnBytes.Desc.First.P1 (mle tot)

/-! ## The value of a form in any world -/

/-- The value of a form, at the reading in the field. -/
def vW (W : World K) (f : Form) : K := Aff.value Reading.gl W f

theorem vW_add (W : World K) (f g : Form) : vW W (f + g) = vW W f + vW W g := Aff.value_add _ _ f g
theorem vW_sub (W : World K) (f g : Form) : vW W (f - g) = vW W f - vW W g := Aff.value_sub _ _ f g
theorem vW_smulE (W : World K) (k : E) (f : Form) : vW W (k • f) = rd k * vW W f :=
  Aff.value_scale _ _ f k
theorem vW_smulN (W : World K) (n : Nat) (f : Form) : vW W (n • f) = (n : K) * vW W f := by
  show vW W (Aff.scale f (natE n)) = _
  unfold vW
  rw [Aff.value_scale]
  show rd (natE n) * _ = _
  rw [rd_natE]
theorem vW_coe (W : World K) (x : E) : vW W ((x : E) : Form) = rd x := Aff.value_ofConst _ _ x
theorem vW_slot (W : World K) (j : Nat) : vW W (Aff.slot j) = W.slot j := Aff.value_slot _ _ j

theorem vW_sumTo (W : World K) (n : Nat) (f : Nat → Form) :
    vW W (sumTo n f) = (Finset.range n).sum fun i => vW W (f i) := by
  unfold sumTo
  induction n with
  | zero =>
    show vW W (Aff.ofConst (natE 0)) = _
    unfold vW
    rw [Aff.value_ofConst]
    show rd (natE 0) = _
    rw [rd_natE]; simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    exact vW_add _ _ _

variable [Sizes] [Policy] [Request] [Token]

/-! ## A table at the challenges -/

theorem toList_two_parts (r : Point) (hr : r.size = lt + lPd) :
    r.toList = (r.extract 0 lt).toList ++ (r.extract lt (lt + lPd)).toList := by
  simp only [Array.toList_extract]
  have h1 : (r.toList.take (lt + lPd)) = r.toList := List.take_of_length_le (by simp [hr])
  simp only [List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero, Nat.add_sub_cancel_left]
  have h2 : (r.toList.drop lt).take lPd = r.toList.drop lt :=
    List.take_of_length_le (by simp [hr])
  rw [h2, List.take_append_drop]

theorem mle_at_r (f : Nat → Nat → K) (r : Point) (hr : r.size = lt + lPd) :
    mle (lt + lPd) (cut lPd d f) (r.toList.map rd) = (Finset.range T).sum fun t =>
      (Finset.range d).sum fun k =>
        rd (eq (r.extract 0 lt) t) * rd (eq (r.extract lt (lt + lPd)) k) * f t k := by
  have s1 : (r.extract 0 lt).size = lt := by simp [hr]
  have s2 : (r.extract lt (lt + lPd)).size = lPd := by simp [hr]
  have l1 : ((r.extract 0 lt).toList.map rd).length = lt := by simp [hr]
  have l2 : ((r.extract lt (lt + lPd)).toList.map rd).length = lPd := by simp [hr]
  have hd : d ≤ 2 ^ ((r.extract lt (lt + lPd)).toList.map rd).length := by
    rw [l2]; exact le_two_pow_clog2 d
  have h := mle_cut ((r.extract 0 lt).toList.map rd) ((r.extract lt (lt + lPd)).toList.map rd) d hd f
  rw [List.length_append, l1, l2, ← List.map_append, ← toList_two_parts r hr] at h
  rw [h]
  refine Finset.sum_congr rfl fun t ht => ?_
  refine Finset.sum_congr rfl fun k hk => ?_
  have ht' : t < 2 ^ (r.extract 0 lt).size := by rw [s1]; exact Finset.mem_range.mp ht
  have hk' : k < 2 ^ (r.extract lt (lt + lPd)).size := by
    rw [s2]; exact lt_of_lt_of_le (Finset.mem_range.mp hk) (le_two_pow_clog2 d)
  rw [wt_toList _ ht', wt_toList _ hk']

/-! ## The second end value: the claim on the weights -/

/-- The rearrangement, in the field alone. e, s: the weights of positions and features; X, u: the
weights of the top digit's key, summed and one by one; Wm: the weights' matrix. -/
theorem weights_alg (e s u : Nat → K) (X : K) (Wm : Nat → Nat → K) (hwin : ∀ t, win t < V) :
    ((Finset.range V).sum fun v => (Finset.range d).sum fun k =>
      (X * ((Finset.range T).sum fun t => if (checked t && win t == v) = true then e t else 0)
        - ((Finset.range T).sum fun t => if checked t = true then e t else 0) * u v) * s k * Wm k v)
    = (Finset.range T).sum fun t => (Finset.range d).sum fun k => e t * s k *
        (if checked t = true then X * Wm k (win t) - (Finset.range V).sum fun v => u v * Wm k v
         else 0) := by
  have hL : ∀ v k, (X * ((Finset.range T).sum fun t =>
        if (checked t && win t == v) = true then e t else 0)
        - ((Finset.range T).sum fun t => if checked t = true then e t else 0) * u v) * s k * Wm k v
      = (Finset.range T).sum fun t => (X * (if (checked t && win t == v) = true then e t else 0)
          - (if checked t = true then e t else 0) * u v) * s k * Wm k v := by
    intro v k
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  have hR : ∀ t k, e t * s k * (if checked t = true then
        X * Wm k (win t) - (Finset.range V).sum fun v => u v * Wm k v else 0)
      = (Finset.range V).sum fun v => (X * (if (checked t && win t == v) = true then e t else 0)
          - (if checked t = true then e t else 0) * u v) * s k * Wm k v := by
    intro t k
    by_cases hc : checked t = true
    · simp only [hc, if_true, Bool.true_and, beq_iff_eq]
      have h1 : X * Wm k (win t) = (Finset.range V).sum fun v =>
          if win t = v then X * Wm k v else 0 := by
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hwin t))]
      rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split <;> ring
    · simp [hc]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

section In
variable [FinalNorm.In] [In]

theorem rd_UH' (c : Cells) (k t : Nat) : rd (UH c k t) = if checked t = true then
    rd (wx .marginTop) * ((c.Wh k (win t) : Int) : K)
      - (Finset.range V).sum fun v => rd (ew .marginTop v) * ((c.Wh k v : Int) : K) else 0 := by
  unfold UH
  split
  · have hs : ((Finset.range V).sum fun v => rd (ew Key.marginTop v * ofInt (c.Wh k v)))
        = (Finset.range V).sum fun v => rd (ew .marginTop v) * ((c.Wh k v : Int) : K) :=
      Finset.sum_congr rfl fun v _ => by rw [rd_mul, rd_ofInt]
    rw [rd_sub, rd_mul, rd_ofInt, rd_sumTo, hs]
  · exact rd_zero

variable [Heard]

/-- **The sum that the claim on the weights names is UH's table at the challenges.** -/
theorem weights_eq (c : Cells) (hreq : Request.ok = true) (hy : y < V) :
    rd (sumTo V fun v => sumTo d fun k =>
      forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k * ofInt (c.Wh k v))
    = (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
        rd (eq rH t) * rd (eq rs k) * fU c t k := by
  rw [rd_sumTo]
  have h1 : ∀ v, rd (sumTo d fun k =>
      forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k * ofInt (c.Wh k v))
      = (Finset.range d).sum fun k =>
        (rd (wx .marginTop) * ((Finset.range T).sum fun t =>
            if (checked t && win t == v) = true then rd (eq rH t) else 0)
          - ((Finset.range T).sum fun t => if checked t = true then rd (eq rH t) else 0)
            * rd (ew .marginTop v)) * rd (eq rs k) * ((c.Wh k v : Int) : K) := by
    intro v
    rw [rd_sumTo]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rd_mul, rd_mul, rd_ofInt]
    show rd (wx Key.marginTop * (sumTo T fun t => if checked t && win t == v then eq rH t else 0)
      - (sumTo T fun t => if checked t then eq rH t else 0) * ew Key.marginTop v) * rd (eq rs k) * _
      = _
    rw [rd_sub, rd_mul, rd_mul, rd_sumTo, rd_sumTo]
    congr 3
    · congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      split
      · rfl
      · exact rd_zero
    · congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      split
      · rfl
      · exact rd_zero
  simp only [h1]
  rw [weights_alg (fun t => rd (eq rH t)) (fun k => rd (eq rs k)) (fun v => rd (ew .marginTop v))
    (rd (wx .marginTop)) (fun k v => ((c.Wh k v : Int) : K)) (win_lt hreq hy)]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold fU
  rw [rd_UH']

/-- **The value of logitForms' second form**, the reads filled from the cells. -/
theorem actForm_value (c : Cells) (W : World K) :
    letI := readsAt c
    vW W ((logits.end_ 0).var - sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k)
      = vW W (logits.end_ 0).var - (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
          rd (eq rH t) * rd (eq rs k) * fA c t k := by
  letI := readsAt c
  have hs : ((Finset.range d).sum fun k =>
      vW W (eq rs k • FinalNorm.actAt (entry .actAtLogits) k))
      = (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
          rd (eq rH t) * rd (eq rs k) * fA c t k := ?_
  · rw [vW_sub, vW_sumTo, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vW_smulE]
  unfold FinalNorm.actAt
  rw [vW_add, vW_smulN]
  show rd (eq rs k) * (vW W ((readAt c (.act, .short (eq rH)) k : E) : Form)
    + _ * vW W ((readAt c (.act, .short (eq rH)) (d + k) : E) : Form)) = _
  rw [vW_coe, vW_coe, rd_readAt_short, rd_readAt_short, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold fA act
  push_cast
  ring

end In

end VerifiableInference.Desc.Kinds.Head.Law
