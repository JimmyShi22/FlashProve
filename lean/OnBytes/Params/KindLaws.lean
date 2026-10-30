-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/KindLaws.lean: what the planner's formulas for a round's error enclose, kind by kind,
within a third of the distance.

A routine of the planner (OnBytes/Params/Planner.lean) prices a round by a formula on bounds. This
file says what some of these formulas enclose, in rational numbers, with q for the number of
elements of the extension field (`Setting.cardE`): a field error; the error of a combination by
powers; the closeness errors of a fold's round, of the last step's first round and of a fold of a
table, where the counts have the footing `.third`; and the error of a round that draws positions and
one batching element (positions alone: `Bound.encl_pow`, OnBytes/Params/BoundLaws.lean).
`share_of_encl` then turns "the formula encloses x" and "the count is at most x times the number of
values" into the hypothesis `hc` of `held_round` (OnBytes/Slice/HeldRound.lean).

Main theorems: `share_of_encl`, `encl_listField`, `encl_listPowers`, `encl_fieldErrorNonzero`,
`encl_foldRoundError_third`, `encl_baseError_third`, `encl_tableFoldError_third`, `encl_cs`.
What is not claimed: that a routine prices a round by one of these formulas: that is read off
OnBytes/Params/Planner.lean. Nothing on `sampleError`, on the error of the smallness test, or on the
larger of two bounds (OnBytes/Slice/HeldKindsLink.lean [not in this library] has that). Nothing at
the footing `.johnson`, but for the closeness errors of a fold's round and of the last step's first
round at any enclosed counts; that of a fold of a table beyond a third is in no file. Nothing on whether what a formula encloses bounds a prover's chance. Nothing on a
bound that is marked bad. Nothing on the C++ planner, of which OnBytes/Params/ is a rendering. For
proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.DistanceLaws
import OnBytes.Params.Group

set_option autoImplicit false

namespace OnBytes.Params
open Binary Bound

/-- If a bound that is not marked bad encloses x, and a count is at most x times N, then the count
is at most the bound's `error` times N. -/
theorem share_of_encl {E : Bound} {x : ℚ} (hE : Encl E x) (hb : E.bad = false) (count N : ℕ)
    (h : (count : ℚ) ≤ x * (N : ℚ)) : (count : ℚ) ≤ E.error.val * (N : ℚ) :=
  h.trans (mul_le_mul_of_nonneg_right (le_error hE hb) (Nat.cast_nonneg N))

/-- A list size times a field error: L * degree / q. -/
theorem encl_listField (s : Setting) (L degree : ℕ) :
    Encl (Bound.ofNat L * fieldError s degree) ((L : ℚ) * ((degree : ℚ) / (s.cardE : ℚ))) :=
  encl_mul (encl_ofNat L) (encl_fieldError s degree)

/-- A list size times the error of a combination by powers: L * (rows - 1) / q. -/
theorem encl_listPowers (s : Setting) (L rows : ℕ) :
    Encl (Bound.ofNat L * powersError s rows)
      ((L : ℚ) * (((rows - 1 : ℕ) : ℚ) / (s.cardE : ℚ))) :=
  encl_mul (encl_ofNat L) (encl_powersError s rows)

/-- degree / (q - 1), the subtraction in natural numbers: the field error for an element other than
0. -/
theorem encl_fieldErrorNonzero (s : Setting) (degree : ℕ) :
    Encl (fieldErrorNonzero s degree) ((degree : ℚ) / ((s.cardE - 1 : ℕ) : ℚ)) := encl_ratio _ _

/-- The error of round j of a fold, where the main code's count has the footing `.third` and is
e + 1: (e + 1) / q + L * 2 / q; and, while mask rows are folded, 2 (eZ + 1) / q more, where the mask
code's count then has that footing and is eZ + 1. -/
theorem encl_foldRoundError_third (s : Setting) (g : GroupSize) (a : Analysis) (j e eZ : ℕ)
    (h1 : a.mainAt.source = .third) (c1 : a.mainAt.count = Bound.ofNat (e + 1))
    (hz : (g.hasMask && decide (j ≤ g.h)) = true →
      a.maskAt.source = .third ∧ a.maskAt.count = Bound.ofNat (eZ + 1)) :
    Encl (foldRoundError s g a j)
      (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ) + (a.list : ℚ) * (((2 : ℕ) : ℚ) / (s.cardE : ℚ)) +
        (if (g.hasMask && decide (j ≤ g.h)) = true
          then ((2 : ℕ) : ℚ) * (((eZ + 1 : ℕ) : ℚ) / (s.cardE : ℚ)) else 0)) := by
  unfold foldRoundError
  dsimp only
  have m := encl_add (encl_mcaError_third s a.mainAt (2 ^ (g.k - j) * g.slots) e h1 c1)
    (encl_listField s a.list 2)
  split
  · rename_i hm
    exact encl_add m (encl_mul (encl_ofWord 2)
      (encl_mcaError_third s a.maskAt _ eZ (hz hm).1 (hz hm).2))
  · rw [add_zero]
    exact m

/-- The error of the first round of the last step, where the main code's count has the footing
`.third` and is e + 1: (e + 1) / q + L * 1 / q; and, if the group has a mask, (eZ + 1) / q more,
where the mask code's count then has that footing and is eZ + 1. -/
theorem encl_baseError_third (s : Setting) (g : GroupSize) (a : Analysis) (e eZ : ℕ)
    (h1 : a.mainAt.source = .third) (c1 : a.mainAt.count = Bound.ofNat (e + 1))
    (hz : g.hasMask = true → a.maskAt.source = .third ∧ a.maskAt.count = Bound.ofNat (eZ + 1)) :
    Encl (baseError s g a)
      (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ) + (a.list : ℚ) * (((1 : ℕ) : ℚ) / (s.cardE : ℚ)) +
        (if g.hasMask = true then ((eZ + 1 : ℕ) : ℚ) / (s.cardE : ℚ) else 0)) := by
  unfold baseError
  dsimp only
  have m := encl_add (encl_mcaError_third s a.mainAt g.slots e h1 c1) (encl_listField s a.list 1)
  split
  · rename_i hm
    exact encl_add m (encl_mcaError_third s a.maskAt 1 eZ (hz hm).1 (hz hm).2)
  · rw [add_zero]
    exact m

/-- The closeness terms of a fold of a table, added to a bound that encloses y: the sum encloses y
and (e + 1) / q for each unit of fuel. -/
theorem encl_tableFoldTerms_third (s : Setting) (v : ℕ) (x : Proximity) (e : ℕ)
    (h1 : x.source = .third) (c1 : x.count = Bound.ofNat (e + 1)) :
    ∀ (fuel j : ℕ) (E : Bound) (y : ℚ), Encl E y →
      Encl (tableFoldTerms s v x fuel j E)
        (y + (fuel : ℚ) * (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ)))
  | 0, _, E, y, hE => by
      unfold tableFoldTerms
      simpa using hE
  | fuel + 1, j, E, y, hE => by
      unfold tableFoldTerms
      have h := encl_tableFoldTerms_third s v x e h1 c1 fuel (j + 1) _ _
        (encl_add hE (encl_mcaError_third s x (2 ^ (v - j)) e h1 c1))
      have e2 : y + ((fuel + 1 : ℕ) : ℚ) * (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ)) =
          y + ((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ) +
            (fuel : ℚ) * (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ)) := by
        push_cast
        ring
      rw [e2]
      exact h

/-- The closeness term of a fold of all rows of a table in one message, at a count e + 1 of the
footing `.third`: v (e + 1) / q + L * v / q. -/
theorem encl_tableFoldError_third (s : Setting) (T : TableSize) (x : Proximity) (e : ℕ)
    (h1 : x.source = .third) (c1 : x.count = Bound.ofNat (e + 1)) :
    Encl (tableFoldError s T x)
      ((T.v : ℚ) * (((e + 1 : ℕ) : ℚ) / (s.cardE : ℚ)) +
        (x.list : ℚ) * ((T.v : ℚ) / (s.cardE : ℚ))) := by
  unfold tableFoldError
  have h := encl_tableFoldTerms_third s T.v x e h1 c1 T.v 1 (Bound.ofWord 0) _ (encl_ofWord 0)
  rw [Nat.cast_zero, zero_add] at h
  exact encl_add h (encl_listField s x.list T.v)

/-- The error of a round that draws t positions and one batching element: a ^ t + L (rows - 1) / q,
for every a that the agreement encloses. -/
theorem encl_cs (s : Setting) {agree : Bound} {a : ℚ} (ha : Encl agree a) (t L rows : ℕ) :
    Encl (Bound.pow agree t + Bound.ofNat L * powersError s rows)
      (a ^ t + (L : ℚ) * (((rows - 1 : ℕ) : ℚ) / (s.cardE : ℚ))) :=
  encl_add (encl_pow ha t) (encl_listPowers s L rows)

/-- The closeness error at a count that encloses cnt: cnt / q, or cnt * rows / q where the setting
has the factor of the rows and the footing is not `.third`. -/
theorem encl_mcaError (s : Setting) (x : Proximity) (rows : ℕ) {cnt : ℚ} (hx : Encl x.count cnt) :
    Encl (mcaError s x rows)
      ((if (s.rowsFactor && x.source != .third) = true then cnt * (rows : ℚ) else cnt) /
        (s.cardE : ℚ)) := by
  unfold mcaError
  dsimp only
  split
  · exact encl_div (encl_mul hx (encl_ofNat rows)) (encl_ofNat _)
  · exact encl_div hx (encl_ofNat _)

/-- The error of round j of a fold, at counts that enclose cM and cZ, in a setting without the
factor of the rows: cM / q + L * 2 / q, and 2 cZ / q more while mask rows are folded. -/
theorem encl_foldRoundError (s : Setting) (hs : s.rowsFactor = false) (g : GroupSize) (a : Analysis)
    (j : ℕ) {cM cZ : ℚ} (h1 : Encl a.mainAt.count cM) (h2 : Encl a.maskAt.count cZ) :
    Encl (foldRoundError s g a j)
      (cM / (s.cardE : ℚ) + (a.list : ℚ) * (((2 : ℕ) : ℚ) / (s.cardE : ℚ)) +
        (if (g.hasMask && decide (j ≤ g.h)) = true
          then ((2 : ℕ) : ℚ) * (cZ / (s.cardE : ℚ)) else 0)) := by
  have m1 := encl_mcaError s a.mainAt (2 ^ (g.k - j) * g.slots) h1
  have m2 := encl_mcaError s a.maskAt (2 ^ (g.h - j)) h2
  rw [hs] at m1 m2
  simp only [Bool.false_and, Bool.false_eq_true, if_false] at m1 m2
  unfold foldRoundError
  dsimp only
  have m := encl_add m1 (encl_listField s a.list 2)
  split
  · exact encl_add m (encl_mul (encl_ofWord 2) m2)
  · rw [add_zero]
    exact m

/-- The error of the first round of the last step, at counts that enclose cM and cZ, in a setting
without the factor of the rows: cM / q + L * 1 / q, and cZ / q more if the group has a mask. -/
theorem encl_baseError (s : Setting) (hs : s.rowsFactor = false) (g : GroupSize) (a : Analysis)
    {cM cZ : ℚ} (h1 : Encl a.mainAt.count cM) (h2 : Encl a.maskAt.count cZ) :
    Encl (baseError s g a)
      (cM / (s.cardE : ℚ) + (a.list : ℚ) * (((1 : ℕ) : ℚ) / (s.cardE : ℚ)) +
        (if g.hasMask = true then cZ / (s.cardE : ℚ) else 0)) := by
  have m1 := encl_mcaError s a.mainAt g.slots h1
  have m2 := encl_mcaError s a.maskAt 1 h2
  rw [hs] at m1 m2
  simp only [Bool.false_and, Bool.false_eq_true, if_false] at m1 m2
  unfold baseError
  dsimp only
  have m := encl_add m1 (encl_listField s a.list 1)
  split
  · exact encl_add m m2
  · rw [add_zero]
    exact m

end OnBytes.Params

#print axioms OnBytes.Params.share_of_encl
#print axioms OnBytes.Params.encl_foldRoundError_third
#print axioms OnBytes.Params.encl_baseError_third
#print axioms OnBytes.Params.encl_tableFoldError_third
#print axioms OnBytes.Params.encl_cs
#print axioms OnBytes.Params.encl_mcaError
#print axioms OnBytes.Params.encl_foldRoundError
#print axioms OnBytes.Params.encl_baseError
