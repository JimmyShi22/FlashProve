-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/LibraryJohnson.lean: the planner's numbers up to the Johnson radius against the proof
library's: its condition on the radius, its bound on a list, and the count of its assumed statement.

The proof library states, in whole positions n, k, e: the condition `Cb.InJohnson n d e` and the
bound on a list `Cb.listMax n d e` (Cb/Gen/JohnsonList.lean; d is the distance), and the numbers
`Cb.bchksM n k e` and `Cb.bchksBound n k e` of its assumed statement on Reed-Solomon codes
(Cb/Gen/CodeListRS.lean; polynomials of degree at most k). The planner has intervals, an integer m,
a count and a list size (OnBytes/Params/Distance.lean), at a `Word`: a length n and a number k. For
`wordOf c`, where c has a dimension of 1 or more, k is the dimension less 1, as in the library, and
the distance is n - k (`wordOf_distance`). For `repeated c logN`, k is that number times the number
of copies: the distance is again n - k, but the dimension is not k + 1. This file holds the one
against the other, for a radius e in whole positions that is at most 1 less the agreement, times the
length, with m as printed and k > 0. `countAtR` is the formula of `countAt`
(OnBytes/Params/JohnsonLaws.lean) at a real number in the place of m (`countAt_eq`); the library's
count is that formula at the rate k / n, the distance e / n and the library's m (`bchksBound_eq`);
for a rate above 0 the formula grows with the distance and with that number (`countAtR_mono`); the
library's m is at most the planner's, for 3 ≤ m (`bchksM_le`). So the library's count is at most the
planner's formula (`bchksBound_le_countAt`), and so at most the upper end of the planner's count,
where the source is `.johnson` and the count is not marked bad: for a code at its own m
(`bchksBound_le_johnson`), for a code that is read at a given agreement
(`bchksBound_le_atDistance`), for the main and the mask code in a group's analysis under the rule
`johnson`, the mask code's with its list size added (`bchksBound_le_main`, `bchksBound_le_mask`),
and for a table with integers at the one-time test's (`bchksBound_le_once`). Whoever goes on to a
price, which is made by the laws on intervals, takes `bchksBound_le_countAt`: `countAt` is a number
that the count encloses. The radius is below the library's Johnson radius and below the distance
(`inJohnson_lib`, `radius_lt_distance`), and the library's bound on the list is at most the
planner's list size of a code at its own m, where its count is not marked bad (`listMax_le_list`,
`listMax_le_once`).

Main definition: `countAtR`.
Main theorems: `countAt_eq`, `bchksBound_eq`, `countAtR_mono`, `bchksM_le`, `bchksBound_le_countAt`,
`inJohnson_lib`, `listMax_le_list`, `radius_lt_distance`, `wordOf_distance`,
`bchksBound_le_johnson`, `bchksBound_le_atDistance`, `bchksBound_le_main`, `bchksBound_le_mask`,
`bchksBound_le_once`, `listMax_le_once`.
What is not claimed: the library's assumed statement, or anything of a code: these are comparisons
of numbers. What else the library's statements ask: e > 0, distinct points, a finite field. Which
radius a proof is to take: e is an argument; `lowerRadius` (OnBytes/Params/JohnsonLaws.lean) meets
the hypothesis where its product is not marked bad; that it is large enough for the rounds that open
positions is no law (the head of that file, on one radius with both limits). Nothing where a code's
source is `.third`: the planner's count is then another formula, which can lie far
below the library's count. That a `Word` has the k of its code: at the dimension 0 `CodeSize.k` is 2
^ 64 - 1, and `repeated` takes its product modulo 2 ^ 64. That the mask code's repetition is a code
of which the library's statement speaks: the docstring of `analysisAt` gives the planner's footing;
nothing of it is proved. The list size of a code that is read at another's distance, and a group's
list size, against `Cb.listMax`: within unique decoding `atDistance` gives the list size 1, and
`Cb.listMax` can be larger there. Nothing on the rounds' prices that are made of count and list
size, but for the record's round (OnBytes/Params/RecordPrice.lean). Nothing in the other reading of
m: the library's m can then be twice the planner's. That k > 0. For proofs only; the program, that
is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.TableJohnson
import Cb.Gen.JohnsonList
import Cb.Gen.CodeListRS

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The formula of `countAt` at a real number in the place of m. -/
noncomputable def countAtR (n : ℕ) (rho delta M : ℝ) : ℝ :=
  (2 * (M + 1 / 2) ^ 5 + 3 * (M + 1 / 2) * delta * rho) / (3 * rho * Real.sqrt rho) * (n : ℝ) +
    (M + 1 / 2) / Real.sqrt rho

/-- `countAt` is that formula at m. -/
theorem countAt_eq (n : ℕ) (rho delta : ℝ) (m : ℕ) :
    countAt n rho delta m = countAtR n rho delta (m : ℝ) := by
  unfold countAt countAtR
  have e : (((2 * m + 1 : ℕ) : ℝ) / 2) = (m : ℝ) + 1 / 2 := by
    push_cast
    ring
  rw [e]

/-- The library's count is that formula at the rate k / n, the distance e / n and the library's
m. -/
theorem bchksBound_eq (n k e : ℕ) :
    Cb.bchksBound n k e = countAtR n ((k : ℝ) / n) ((e : ℝ) / n) (Cb.bchksM n k e) := by
  unfold Cb.bchksBound countAtR
  rw [mul_assoc 3 ((k : ℝ) / n) (Real.sqrt ((k : ℝ) / n))]

/-- The formula grows with the distance, from 0 on, and with the number in the place of m, from 0
on. -/
theorem countAtR_mono {n : ℕ} {rho d d' M M' : ℝ} (hr : 0 < rho) (hd0 : 0 ≤ d) (hd : d ≤ d')
    (hM0 : 0 ≤ M) (hM : M ≤ M') : countAtR n rho d M ≤ countAtR n rho d' M' := by
  unfold countAtR
  have hs : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hr
  have hA : M + 1 / 2 ≤ M' + 1 / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ M + 1 / 2 := by linarith
  have h5 := pow_le_pow_left₀ hA0 hA 5
  have hprod : 3 * (M + 1 / 2) * d * rho ≤ 3 * (M' + 1 / 2) * d' * rho := by
    have : (M + 1 / 2) * d ≤ (M' + 1 / 2) * d' := mul_le_mul hA hd hd0 (hA0.trans hA)
    nlinarith
  have hden : 0 < 3 * rho * Real.sqrt rho := by positivity
  have h1 := div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left h5
    (by norm_num : (0 : ℝ) ≤ 2)) hprod) hden.le
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
  have h3 := div_le_div_of_nonneg_right hA hs.le
  exact add_le_add h2 h3

/-- **The library's m is at most the planner's**: for 3 ≤ m, k > 0 and a radius e that is at most 1
less the agreement that belongs to m as printed, times the length. -/
theorem bchksM_le {c : Word} {m e : ℕ} (h3 : 3 ≤ m) (hk : 0 < c.k)
    (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) : Cb.bchksM c.n c.k e ≤ (m : ℝ) := by
  have hn : (0 : ℝ) < (c.n : ℝ) := by
    have : 0 < c.n := by unfold Word.n; positivity
    exact_mod_cast this
  have hk' : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hk
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hr0 : 0 < (c.k : ℝ) / (c.n : ℝ) := by positivity
  set s := Real.sqrt ((c.k : ℝ) / (c.n : ℝ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
  have ha : c.agreeAt m true = s + s / (m : ℝ) := by
    unfold Word.agreeAt Word.rho
    simp [hs]
  have hg : (e : ℝ) / (c.n : ℝ) ≤ 1 - (s + s / (m : ℝ)) := by
    rw [div_le_iff₀ hn, ← ha]
    exact he
  have hden : s / (m : ℝ) ≤ 1 - s - (e : ℝ) / (c.n : ℝ) := by linarith
  have hden0 : 0 < 1 - s - (e : ℝ) / (c.n : ℝ) := lt_of_lt_of_le (by positivity) hden
  have ht : s / (1 - s - (e : ℝ) / (c.n : ℝ)) ≤ (m : ℝ) := by
    rw [div_le_iff₀ hden0]
    have := mul_le_mul_of_nonneg_left hden hm.le
    have e1 : (m : ℝ) * (s / (m : ℝ)) = s := by field_simp
    linarith
  unfold Cb.bchksM
  refine max_le ?_ (by exact_mod_cast h3)
  have hc : ⌈s / (1 - s - (e : ℝ) / (c.n : ℝ))⌉ ≤ (m : ℤ) := Int.ceil_le.mpr (by exact_mod_cast ht)
  exact_mod_cast hc

/-- **The library's count is at most the planner's formula** at the code's rate, the distance 1 - a
and m: for 3 ≤ m, k > 0, a real agreement a that is at least the agreement which belongs to m as
printed, and a radius e that is at most (1 - a) n. -/
theorem bchksBound_le_countAt {c : Word} {m e : ℕ} {a : ℝ} (h3 : 3 ≤ m) (hk : 0 < c.k)
    (ha : c.agreeAt m true ≤ a) (he : (e : ℝ) ≤ (1 - a) * (c.n : ℝ)) :
    Cb.bchksBound c.n c.k e ≤ countAt c.n c.rho (1 - a) m := by
  have hn : (0 : ℝ) < (c.n : ℝ) := by
    have : 0 < c.n := by unfold Word.n; positivity
    exact_mod_cast this
  have hk' : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hk
  have he' : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ) :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith) hn.le)
  rw [bchksBound_eq, countAt_eq]
  refine countAtR_mono (by positivity) (by positivity) ?_ ?_ (bchksM_le h3 hk he')
  · rw [div_le_iff₀ hn]
    exact he
  · unfold Cb.bchksM
    exact le_trans (by norm_num) (le_max_right _ _)

/-- **Below the library's Johnson radius**, at the distance n - k: for m > 0, k > 0 and a radius e
that is at most 1 less the agreement that belongs to m as printed, times the length. -/
theorem inJohnson_lib {c : Word} {m e : ℕ} (hm : 0 < m) (hk : 0 < c.k)
    (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) : Cb.InJohnson c.n (c.n - c.k) e := by
  unfold Cb.InJohnson
  have h := radius_inJohnson hm hk he
  have hkn : c.k < c.n := by
    by_contra hc
    have h2 : (c.n - e) * (c.n - e) ≤ c.n * c.k :=
      Nat.mul_le_mul (Nat.sub_le _ _) ((Nat.sub_le _ _).trans (by omega))
    omega
  have e1 : c.n - (c.n - c.k) = c.k := by omega
  rw [e1, sq]
  exact h

/-- **The library's bound on the list is at most the planner's list size of a code at its own m**,
with m as printed, where the count is not marked bad and k > 0, at the distance n - k, for a radius
e that is at most 1 less the agreement that belongs to m, times the length. Nothing on a code that
is read at another code's distance. -/
theorem listMax_le_list {c : Word} {m e : ℕ} (g : (johnson c m true).count.bad = false)
    (hk : 0 < c.k) (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) :
    Cb.listMax c.n (c.n - c.k) e ≤ (johnson c m true).list := by
  obtain ⟨h3, hkn⟩ := johnson_count_good g
  obtain ⟨hen, _⟩ := radius_slack (by omega : 0 < m) he
  have hJ := radius_inJohnson (by omega : 0 < m) hk he
  have hw := johnson_list_whole g hk he
  unfold Cb.listMax
  have e1 : c.n - (c.n - c.k) = c.k := by omega
  rw [e1, sq]
  have hpos : 0 < (c.n - e) * (c.n - e) - c.n * c.k := by omega
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hpos]
  by_cases hle : c.n - c.k ≤ e
  · have z : c.n - c.k - e = 0 := by omega
    rw [z, Nat.mul_zero]
    positivity
  · have hlt : e < c.n - c.k := by omega
    have c1 : ((c.n - c.k - e : ℕ) : ℝ) = (c.n : ℝ) - (e : ℝ) - (c.k : ℝ) := by
      rw [Nat.cast_sub hlt.le, Nat.cast_sub hkn.le]
      ring
    have c2 : (((c.n - e) * (c.n - e) - c.n * c.k : ℕ) : ℝ) =
        ((c.n : ℝ) - (e : ℝ)) * ((c.n : ℝ) - (e : ℝ)) - (c.k : ℝ) * (c.n : ℝ) := by
      rw [Nat.cast_sub hJ.le]
      push_cast [Nat.cast_sub hen]
      ring
    have goalR : ((c.n * (c.n - c.k - e) : ℕ) : ℝ) <
        ((((johnson c m true).list).succ * ((c.n - e) * (c.n - e) - c.n * c.k) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, c1, c2, Nat.cast_succ]
      exact hw
    exact_mod_cast goalR

/-- Such a radius is below the distance n - k. -/
theorem radius_lt_distance {c : Word} {m e : ℕ} (hm : 0 < m) (hk : 0 < c.k)
    (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) : e < c.n - c.k := by
  have hJ := radius_inJohnson hm hk he
  by_contra hc
  have h1 : c.n - e ≤ c.k := by omega
  have h2 : (c.n - e) * (c.n - e) ≤ c.n * c.k := Nat.mul_le_mul (Nat.sub_le _ _) h1
  omega

/-- The distance n - k of a code's `Word`, by the dimension. -/
theorem wordOf_distance {c : CodeSize} (h0 : 0 < c.dim) (h1 : c.dim ≤ c.n) :
    (wordOf c).n - (wordOf c).k = 2 ^ c.logN - (c.r + c.ell) + 1 := by
  have hk : (wordOf c).k = c.dim - 1 := by
    simp [wordOf, CodeSize.k, Nat.pos_iff_ne_zero.mp h0]
  have hn : (wordOf c).n = 2 ^ c.logN := rfl
  unfold CodeSize.dim CodeSize.n at *
  omega

/-- **The library's count is at most the upper end of the planner's count at m**, with m as printed.
-/
theorem bchksBound_le_johnson {c : Word} {m e : ℕ} (g : (johnson c m true).count.bad = false)
    (hk : 0 < c.k) (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) :
    Cb.bchksBound c.n c.k e ≤ (((johnson c m true).count.hi.val : ℚ) : ℝ) :=
  (bchksBound_le_countAt (johnson_count_good g).1 hk le_rfl he).trans
    (enclR_johnson_count c m true g).2

/-- **The like for a code that is read at a given agreement**, where the source is `.johnson`, the
count is not marked bad, m is as printed and k > 0: a is what the agreement encloses, and e is at
most (1 - a) n. -/
theorem bchksBound_le_atDistance {s : Setting} {c : Word} {agree : Bound} {a : ℝ} {e : ℕ}
    (ha : EnclR agree a) (hs : (atDistance s c agree).source = .johnson)
    (hg : (atDistance s c agree).count.bad = false) (hp : s.printed = true) (hk : 0 < c.k)
    (he : (e : ℝ) ≤ (1 - a) * (c.n : ℝ)) :
    Cb.bchksBound c.n c.k e ≤ (((atDistance s c agree).count.hi.val : ℚ) : ℝ) := by
  obtain ⟨_, h2, h3, h4⟩ := atDistance_johnson ha hs hg
  exact (bchksBound_le_countAt h3 hk (h4 hp) he).trans (h2 hg).2

/-- **The like for the main code in a group's analysis under the rule `johnson`**, where its source
is `.johnson`, its count is not marked bad, m is as printed and k > 0, for a radius e that is at
most 1 less the group's agreement, times the length. -/
theorem bchksBound_le_main {s : Setting} {g : GroupSize} {e : ℕ}
    (hs : (analysisOfM s g).mainAt.source = .johnson)
    (hg : (analysisOfM s g).mainAt.count.bad = false) (hp : s.printed = true)
    (hk : 0 < (wordOf g.main).k)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ)) :
    Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e ≤
      (((analysisOfM s g).mainAt.count.hi.val : ℚ) : ℝ) := by
  obtain ⟨_, _, h2, h3, h4⟩ := analysisOfM_main hs hg
  exact (bchksBound_le_countAt h3 hk (h4 hp) he).trans (h2 hg).2

/-- **The like for the mask code**, as its repetition to the main code's length, under the same
conditions on it: the library's count and the mask code's list size more. -/
theorem bchksBound_le_mask {s : Setting} {g : GroupSize} {e : ℕ} (hh : g.hasMask = true)
    (hs : (analysisOfM s g).maskAt.source = .johnson)
    (hg : (analysisOfM s g).maskAt.count.bad = false) (hp : s.printed = true)
    (hk : 0 < (repeated g.mask g.main.logN).k)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ)) :
    Cb.bchksBound (repeated g.mask g.main.logN).n (repeated g.mask g.main.logN).k e +
        ((analysisOfM s g).maskAt.list : ℝ) ≤
      (((analysisOfM s g).maskAt.count.hi.val : ℚ) : ℝ) := by
  obtain ⟨_, _, h2, h3, h4⟩ := analysisOfM_mask hh hs hg
  exact (add_le_add (bchksBound_le_countAt h3 hk (h4 hp) he) le_rfl).trans (h2 hg).2

/-- **The like for a table whose distances are given by integers, at the one-time test's**: the
library's count against the upper end of the planner's count. -/
theorem bchksBound_le_once {s : Setting} {T : TableSize} {e : ℕ} (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (g : (tableAnalysis s T).once.count.bad = false)
    (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mOnce true) * ((wordOf T.code).n : ℝ)) :
    Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e ≤
      (((tableAnalysis s T).once.count.hi.val : ℚ) : ℝ) := by
  have e1 := (tableAnalysis_fromM (s := s) hM).1
  rw [hp] at e1
  rw [e1] at g ⊢
  exact bchksBound_le_johnson g hk he

/-- **And the library's bound on the list against the list size of the one-time test.** -/
theorem listMax_le_once {s : Setting} {T : TableSize} {e : ℕ} (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (g : (tableAnalysis s T).once.count.bad = false)
    (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mOnce true) * ((wordOf T.code).n : ℝ)) :
    Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e ≤
      (tableAnalysis s T).once.list := by
  have e1 := (tableAnalysis_fromM (s := s) hM).1
  rw [hp] at e1
  rw [e1] at g ⊢
  exact listMax_le_list g hk he

end OnBytes.Params

#print axioms OnBytes.Params.radius_lt_distance
#print axioms OnBytes.Params.wordOf_distance
#print axioms OnBytes.Params.bchksBound_le_once
#print axioms OnBytes.Params.listMax_le_once
#print axioms OnBytes.Params.bchksBound_le_johnson
#print axioms OnBytes.Params.bchksBound_le_atDistance
#print axioms OnBytes.Params.bchksBound_le_main
#print axioms OnBytes.Params.bchksBound_le_mask
#print axioms OnBytes.Params.countAt_eq
#print axioms OnBytes.Params.bchksBound_eq
#print axioms OnBytes.Params.countAtR_mono
#print axioms OnBytes.Params.bchksM_le
#print axioms OnBytes.Params.bchksBound_le_countAt
#print axioms OnBytes.Params.inJohnson_lib
#print axioms OnBytes.Params.listMax_le_list
