-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/DistanceLaws.lean: what `atDistance` returns for a code where the footing of its
count is a third of the distance, and what three of the planner's errors enclose.

`atDistance` (OnBytes/Params/Distance.lean) takes a setting, a code and an agreement 1 - delta and
returns a count, a list size and the footing of the count. This file proves, for every setting and
code and every agreement that encloses a number a (`Encl`, OnBytes/Params/BoundLaws.lean): where the
footing is `.third`, three times the radius in whole positions (`radiusOf`)
is below n - k, with k the code's dimension less 1; the count
is `Bound.ofNat` of the radius and one; the list size is 1; and a is above (n - radius - 1) / n. It
also proves that `fieldError` and `powersError` enclose degree / |E| and (rows - 1) / |E|, and that
`mcaError` at a `.third` count encloses (radius + 1) / |E|: each unless it is marked bad.

Main theorems: `atDistance_third`, `pow_share`, `encl_fieldError`, `encl_powersError`,
`encl_mcaError_third`.
What is not claimed: nothing at the source `.johnson`. Nothing on whether a count of radius + 1
bounds anything. Nothing on
`sampleError` or `positions`. Nothing on `analysis` (OnBytes/Params/Group.lean): that it hands on
what `atDistance` returns. What `foldRoundError`, `baseError` and `fieldErrorNonzero` enclose is in
OnBytes/Params/KindLaws.lean. Nothing on a round of a plan: that its error is the upper end of one
of these bounds is not shown here. Nothing on
the C++ planner, of which OnBytes/Params/ is a rendering. For proofs only; the program, that is the
Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.BoundLaws
import OnBytes.Params.Distance

set_option autoImplicit false

namespace OnBytes.Params
open Binary Bound

/-- The upper end of delta * n, rounded down. Of a `Proximity` that `atDistance` made for a code of
length n, it is the radius in whole positions as that function counts it: the source is `.third`
if three times this number is below the code's distance. -/
def radiusOf (x : Proximity) (n : Nat) : Nat := (x.delta * Bound.ofNat n).hi.floor

/-- Where `atDistance` gives the footing `.third`, with e its radius (`radiusOf`): 3 e < n - k; the
count is `Bound.ofNat (e + 1)`; the list size is 1; the agreement is handed on and is not marked
bad; and (n - e - 1) / n < a. a: any number that the agreement encloses. -/
theorem atDistance_third {s : Setting} {c : Word} {agree : Bound} {a : ℚ} (ha : Encl agree a)
    (h : (atDistance s c agree).source = .third) :
    3 * radiusOf (atDistance s c agree) c.n < c.n - c.k ∧
      (atDistance s c agree).count = Bound.ofNat (radiusOf (atDistance s c agree) c.n + 1) ∧
      (atDistance s c agree).list = 1 ∧ (atDistance s c agree).agree = agree ∧
      agree.bad = false ∧
      ((c.n : ℚ) - (radiusOf (atDistance s c agree) c.n : ℚ) - 1) / (c.n : ℚ) < a := by
  unfold atDistance at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i h1
    rw [if_neg h1]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_le] at h1
    obtain ⟨hbad, hkn⟩ := h1
    split at h
    · cases h
    · rename_i h2
      rw [if_neg h2]
      have hd : (Bound.ofWord 1 - agree).bad = false := by simpa using h2
      split at h
      · rename_i h3
        rw [if_pos h3]
        refine ⟨h3, rfl, rfl, rfl, hbad, ?_⟩
        show ((c.n : ℚ) - (((Bound.ofWord 1 - agree) * Bound.ofNat c.n).hi.floor : ℚ) - 1) /
          (c.n : ℚ) < a
        have hn : (0 : ℚ) < (c.n : ℚ) := by
          have : 0 < c.n := Nat.pos_of_ne_zero (by unfold Word.n; positivity)
          exact_mod_cast this
        have e1 := (encl_sub (encl_ofWord 1) ha hd).2
        have e2 := (encl_ofNat c.n rfl).2
        have e3 := val_mul_up (Bound.ofWord 1 - agree).hi (Bound.ofNat c.n).hi
        have e4 := lt_floor (((Bound.ofWord 1 - agree) * Bound.ofNat c.n).hi)
        have e5 : ((Bound.ofWord 1 - agree) * Bound.ofNat c.n).hi =
            (Bound.ofWord 1 - agree).hi.mul (Bound.ofNat c.n).hi .up := rfl
        rw [e5] at e4 ⊢
        have d0 : 0 ≤ (Bound.ofWord 1 - agree).hi.val := val_nonneg _
        have e6 : (((1 : ℕ) : ℚ) - a) * (c.n : ℚ) ≤
            (Bound.ofWord 1 - agree).hi.val * (Bound.ofNat c.n).hi.val := by
          by_cases hs : 0 ≤ ((1 : ℕ) : ℚ) - a
          · exact mul_le_mul e1 e2 hn.le d0
          · have : (((1 : ℕ) : ℚ) - a) * (c.n : ℚ) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith) hn.le
            exact this.trans (mul_nonneg d0 (val_nonneg _))
        rw [div_lt_iff₀ hn]
        push_cast at e6
        nlinarith
      · repeat' split at h
        all_goals cases h

/-- Where the footing is `.third`: of the n ^ t lists of t positions, those that miss a set of
radius + 1 positions are a share of at most the planner's agreement to the power t, as `error`
returns it. a: a number that the agreement encloses. Asked: the power is not marked bad. -/
theorem pow_share {s : Setting} {c : Word} {agree : Bound} {a : ℚ} (ha : Encl agree a)
    (h : (atDistance s c agree).source = .third) (t : ℕ) (hb : (Bound.pow agree t).bad = false) :
    (((c.n - radiusOf (atDistance s c agree) c.n - 1) ^ t : ℕ) : ℚ) ≤
      (Bound.pow agree t).error.val * ((c.n ^ t : ℕ) : ℚ) := by
  obtain ⟨h3, _, _, _, _, hlt⟩ := atDistance_third ha h
  generalize radiusOf (atDistance s c agree) c.n = e at h3 hlt
  have hn : (0 : ℚ) < (c.n : ℚ) := by
    have : 0 < c.n := Nat.pos_of_ne_zero (by unfold Word.n; positivity)
    exact_mod_cast this
  have hle : e + 1 ≤ c.n := by omega
  have hcast : ((c.n - e - 1 : ℕ) : ℚ) = (c.n : ℚ) - (e : ℚ) - 1 := by
    rw [Nat.sub_sub, Nat.cast_sub hle]
    push_cast
    ring
  have h0 : 0 ≤ ((c.n : ℚ) - (e : ℚ) - 1) / (c.n : ℚ) := by
    rw [← hcast]
    positivity
  have hpow : (((c.n : ℚ) - (e : ℚ) - 1) / (c.n : ℚ)) ^ t ≤ (Bound.pow agree t).error.val :=
    (pow_le_pow_left₀ h0 hlt.le t).trans (le_error (encl_pow ha t) hb)
  rw [Nat.cast_pow, Nat.cast_pow, hcast]
  rw [div_pow, div_le_iff₀ (by positivity)] at hpow
  exact hpow

/-- `fieldError` encloses degree / |E|. -/
theorem encl_fieldError (s : Setting) (degree : ℕ) :
    Encl (fieldError s degree) ((degree : ℚ) / (s.cardE : ℚ)) := encl_ratio _ _

/-- `powersError` encloses (rows - 1) / |E|, the subtraction in natural numbers. -/
theorem encl_powersError (s : Setting) (rows : ℕ) :
    Encl (powersError s rows) (((rows - 1 : ℕ) : ℚ) / (s.cardE : ℚ)) := encl_ratio _ _

/-- The closeness error at a count of the footing `.third` that is the number e + 1. -/
theorem encl_mcaError_third (s : Setting) (x : Proximity) (rows e : ℕ) (hs : x.source = .third)
    (hc : x.count = Bound.ofNat (e + 1)) :
    Encl (mcaError s x rows) (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ)) := by
  unfold mcaError
  have hf : (s.rowsFactor && x.source != .third) = false := by
    rw [hs]
    simp
  rw [hf, hc]
  exact encl_div (encl_ofNat _) (encl_ofNat _)

end OnBytes.Params

#print axioms OnBytes.Params.atDistance_third
#print axioms OnBytes.Params.pow_share
#print axioms OnBytes.Params.encl_fieldError
#print axioms OnBytes.Params.encl_powersError
#print axioms OnBytes.Params.encl_mcaError_third
