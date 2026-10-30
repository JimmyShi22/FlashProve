-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/HeldKindsAny.lean: `held_round` for rounds that draw positions at any radius, and for
closeness rounds at any enclosed counts; so also within unique decoding.

OnBytes/Slice/HeldKinds.lean treats the planner's formulas within a third of the distance. The
statements here do not name a footing. For positions they ask of the radius e only that n - e - 1 ≤
a n, for a number a that the agreement encloses; `atDistance_third`
(OnBytes/Params/DistanceLaws.lean) gives such an e below a third.
For a fold's round and the last step's first
round they ask that the two counts enclose natural numbers KM and KZ, in a setting without the
factor of the rows. Two small cases are added: a count of 0, and a field error for an element other
than 0.

Main theorems: `meets_zero`, `held_fieldNonzero_alone`, `held_fieldNonzero`, `held_positions`,
`held_cs`, `held_fold`, `held_base`.
What is not claimed: all that OnBytes/Slice/HeldKinds.lean does not claim, but for its sentence on
the footings. In particular the equation on the round's error is a hypothesis, and nothing says that
a count of KM bounds anything.
At `.johnson` a count is as a rule no natural
number, so `held_fold` and `held_base` do not serve. Nothing on `sampleError`: of the round of a
sample's seed only the count 0 is treated, so nothing where a list has two members or more.
For proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.KindLaws
import OnBytes.Slice.HeldKinds

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob _root_.Run OnBytes.Params
open scoped ENNReal

/-- A count of 0 meets every bound, whatever the round's error. Such are the counts of the round of
a sample's seed where all lists have one member (`err1_one`, OnBytes/Slice/ChainErr.lean;
`errSend_one`, OnBytes/Slice/RatesToy.lean). -/
theorem meets_zero (s : Setting) (d : PQ.RD) : Meets s d 0 := by
  unfold Meets
  rw [Nat.zero_mul, Nat.cast_zero]
  exact zero_le _

/-- A round that is priced by the field error for an element other than 0 alone, degree / (q - 1).
Such an element has q - 1 typed values. -/
theorem held_fieldNonzero_alone {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d)
    (degree : ℕ) (hb : (fieldErrorNonzero s degree).bad = false)
    (hr : r.error = (fieldErrorNonzero s degree).error) (count : ℕ)
    (h : count * (s.cardE - 1) ≤ degree * nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  have hq : 0 < s.cardE - 1 := by
    unfold Setting.cardE
    rw [H.p, H.degree]
    decide
  exact held_of_encl H (encl_fieldErrorNonzero s degree) hb hr count
    (share_div count degree _ (s.cardE - 1) hq h)

/-- The same, times a list size. No routine of OnBytes/Params/Planner.lean prices a round so. -/
theorem held_fieldNonzero {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (L degree : ℕ)
    (hb : (Bound.ofNat L * fieldErrorNonzero s degree).bad = false)
    (hr : r.error = (Bound.ofNat L * fieldErrorNonzero s degree).error) (count : ℕ)
    (h : count * (s.cardE - 1) ≤ L * degree * nVals (Fmt.dsOf d.entry d.kind)) :
    Meets s d count := by
  have hq : 0 < s.cardE - 1 := by
    unfold Setting.cardE
    rw [H.p, H.degree]
    decide
  refine held_of_encl H (Bound.encl_mul (Bound.encl_ofNat L) (encl_fieldErrorNonzero s degree)) hb
    hr count ?_
  have := share_div count (L * degree) _ (s.cardE - 1) hq h
  rw [Nat.cast_mul, mul_div_assoc] at this
  exact this

/-- If 0 ≤ a and n - e - 1 ≤ a n, then (n - e - 1) ^ t ≤ a ^ t n ^ t; the left side in natural
numbers. -/
theorem agree_pow (n e t : ℕ) (a : ℚ) (ha : 0 ≤ a) (h : (n : ℚ) - (e : ℚ) - 1 ≤ a * (n : ℚ)) :
    (((n - e - 1) ^ t : ℕ) : ℚ) ≤ a ^ t * ((n ^ t : ℕ) : ℚ) := by
  have hb : ((n - e - 1 : ℕ) : ℚ) ≤ a * (n : ℚ) := by
    by_cases hle : e + 1 ≤ n
    · have : ((n - e - 1 : ℕ) : ℚ) = (n : ℚ) - (e : ℚ) - 1 := by
        rw [Nat.sub_sub, Nat.cast_sub hle]
        push_cast
        ring
      rw [this]
      exact h
    · have : n - e - 1 = 0 := by omega
      rw [this, Nat.cast_zero]
      exact mul_nonneg ha (Nat.cast_nonneg n)
  have := pow_le_pow_left₀ (Nat.cast_nonneg (n - e - 1)) hb t
  rw [mul_pow] at this
  rw [Nat.cast_pow, Nat.cast_pow]
  exact this

/-- A round that draws t positions among n and is priced by the agreement to the power t. e: a
radius with n - e - 1 ≤ a n, for a number a that the agreement encloses. -/
theorem held_positions {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) {agree : Bound}
    {a : ℚ} (ha : Encl agree a) (hg : agree.bad = false) (n e t : ℕ) (hn : 0 < n)
    (he : (n : ℚ) - (e : ℚ) - 1 ≤ a * (n : ℚ))
    (hb : (Bound.pow agree t).bad = false) (hr : r.error = (Bound.pow agree t).error) (count : ℕ)
    (h : count * n ^ t ≤ (n - e - 1) ^ t * nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (Bound.encl_pow ha t) hb hr count ?_
  have hp := agree_pow n e t a ((Binary.val_nonneg _).trans (ha hg).1) he
  generalize (n - e - 1) ^ t = A at h hp
  generalize nVals (Fmt.dsOf d.entry d.kind) = N at h
  have hnt : (0 : ℚ) < ((n ^ t : ℕ) : ℚ) := by
    have : 0 < n ^ t := Nat.pos_of_ne_zero (by positivity)
    exact_mod_cast this
  generalize n ^ t = M at h hp hnt
  have hq : (count : ℚ) * (M : ℚ) ≤ (A : ℚ) * (N : ℚ) := by exact_mod_cast h
  have hN : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
  have : (count : ℚ) * (M : ℚ) ≤ a ^ t * (N : ℚ) * (M : ℚ) := by
    calc (count : ℚ) * (M : ℚ) ≤ (A : ℚ) * (N : ℚ) := hq
      _ ≤ a ^ t * (M : ℚ) * (N : ℚ) := mul_le_mul_of_nonneg_right hp hN
      _ = a ^ t * (N : ℚ) * (M : ℚ) := by ring
  exact le_of_mul_le_mul_right this hnt

/-- A round that draws t positions among n and one batching element, and is priced by the agreement
to the power t and a list size times the error of a combination by powers. -/
theorem held_cs {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) {agree : Bound}
    {a : ℚ} (ha : Encl agree a) (hg : agree.bad = false) (n e t L rows : ℕ) (hn : 0 < n)
    (he : (n : ℚ) - (e : ℚ) - 1 ≤ a * (n : ℚ))
    (hb : (Bound.pow agree t + Bound.ofNat L * powersError s rows).bad = false)
    (hr : r.error = (Bound.pow agree t + Bound.ofNat L * powersError s rows).error) (count : ℕ)
    (h : count * (n ^ t * s.cardE) ≤ ((n - e - 1) ^ t * s.cardE + n ^ t * (L * (rows - 1))) *
      nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_cs s ha t L rows) hb hr count ?_
  have hp := agree_pow n e t a ((Binary.val_nonneg _).trans (ha hg).1) he
  generalize (n - e - 1) ^ t = A at h hp
  generalize nVals (Fmt.dsOf d.entry d.kind) = N at h
  have hnt : (0 : ℚ) < ((n ^ t : ℕ) : ℚ) := by
    have : 0 < n ^ t := Nat.pos_of_ne_zero (by positivity)
    exact_mod_cast this
  have hq0 : (0 : ℚ) < (s.cardE : ℚ) := by exact_mod_cast cardE_pos H
  generalize n ^ t = M at h hp hnt
  generalize s.cardE = q at h hq0
  generalize rows - 1 = R at h
  have hq : (count : ℚ) * ((M : ℚ) * (q : ℚ)) ≤
      ((A : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) := by exact_mod_cast h
  have hN : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
  have hMq : (0 : ℚ) < (M : ℚ) * (q : ℚ) := mul_pos hnt hq0
  have e1 : (a ^ t + (L : ℚ) * ((R : ℚ) / (q : ℚ))) * (N : ℚ) * ((M : ℚ) * (q : ℚ)) =
      (a ^ t * (M : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) := by
    field_simp
  have e2 : ((A : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) ≤
      (a ^ t * (M : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) := by
    refine mul_le_mul_of_nonneg_right ?_ hN
    have := mul_le_mul_of_nonneg_right hp hq0.le
    linarith
  refine le_of_mul_le_mul_right ?_ hMq
  rw [e1]
  exact hq.trans e2

/-- Round j of a fold, at counts that enclose KM and KZ, in a setting without the factor of the
rows. -/
theorem held_fold {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d)
    (hs : s.rowsFactor = false) (g : GroupSize) (a : Analysis) (j KM KZ : ℕ)
    (h1 : Encl a.mainAt.count (KM : ℚ)) (h2 : Encl a.maskAt.count (KZ : ℚ))
    (hb : (foldRoundError s g a j).bad = false) (hr : r.error = (foldRoundError s g a j).error)
    (count : ℕ)
    (h : count * s.cardE ≤ (KM + a.list * 2 +
      (if (g.hasMask && decide (j ≤ g.h)) = true then 2 * KZ else 0)) *
        nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_foldRoundError s hs g a j h1 h2) hb hr count ?_
  have := share_div count _ _ s.cardE (cardE_pos H) h
  refine this.trans (le_of_eq ?_)
  congr 1
  split <;> (push_cast; ring)

/-- The first round of the last step, at counts that enclose KM and KZ, in a setting without the
factor of the rows. -/
theorem held_base {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d)
    (hs : s.rowsFactor = false) (g : GroupSize) (a : Analysis) (KM KZ : ℕ)
    (h1 : Encl a.mainAt.count (KM : ℚ)) (h2 : Encl a.maskAt.count (KZ : ℚ))
    (hb : (baseError s g a).bad = false) (hr : r.error = (baseError s g a).error) (count : ℕ)
    (h : count * s.cardE ≤ (KM + a.list * 1 + (if g.hasMask = true then KZ else 0)) *
        nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_baseError s hs g a h1 h2) hb hr count ?_
  have := share_div count _ _ s.cardE (cardE_pos H) h
  refine this.trans (le_of_eq ?_)
  congr 1
  split <;> (push_cast; ring)

end OnBytes.Slice

#print axioms OnBytes.Slice.meets_zero
#print axioms OnBytes.Slice.held_fieldNonzero_alone
#print axioms OnBytes.Slice.held_fieldNonzero
#print axioms OnBytes.Slice.held_positions
#print axioms OnBytes.Slice.held_cs
#print axioms OnBytes.Slice.held_fold
#print axioms OnBytes.Slice.held_base
