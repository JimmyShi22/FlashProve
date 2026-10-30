-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/MorePrices.lean: that the planner's prices of the rounds which draw positions, batch
rows or sample a message cover counts in whole positions and lists.

OnBytes/Params/GroupPrices.lean treats the closeness rounds of a proximity test. This file treats
the other rounds whose price leans on a code, by an agreement or a list size. A list size times
`fieldError` covers L degree / q, and a list size times `powersError` covers L (rows - 1) / q, for L
at most the list size (`list_field_covers`, `list_powers_covers`; q is the number of elements of the
extension field). For a distance that encloses 1 - a, and a radius e from the upper radius on
(OnBytes/Params/JohnsonLaws.lean), n - e - 1 is at most a n (`agree_of_upperRadius`); then the price
of a draw of t positions, the agreement to the power t, covers ((n - e - 1) / n) ^ t
(`positions_cover`), and the price of the second round of a code switch covers that and L (rows - 1)
/ q more, for L at most the next stage's list size (`switch_covers`). `sampleError` covers (L choose
2) times, for each answer, the share of the clashing seeds of OnBytes/Params/RecordPrice.lean
(`sample_covers`); so does the price of a sending of one message, the planner's sum from 0
(`send_one_covers`), and the price of a link's round of seeds, twice `sampleError`, covers twice
that (`send_two_covers`). For a group under the conditions `JohnsonGroup s g e`: the price of a draw
of positions at the main code's agreement covers ((n - e - 1) / n) ^ t, if e is also at least the
upper radius (`group_positions_cover`; `upperRadiusTest`, `upperRadius_of_test`); the price of the
round before a fold's rounds covers the proof library's `Cb.listMax` at the main code, over q
(`fold_epsilon_covers`); and the price of the second round of a code switch to a group g' under the
conditions at a radius e' covers the positions' share at g and e, and the library's `Cb.listMax` at
g' and e' times (rows - 1) / q (`group_switch_covers`).

Main definition: `upperRadiusTest`.
Main theorems: `enclR_powersError`, `list_field_covers`, `list_powers_covers`,
`agree_of_upperRadius`, `positions_cover`, `switch_covers`, `sample_covers`, `send_one_covers`,
`send_two_covers`, `agreeAt_nonneg`, `group_positions_cover`, `fold_epsilon_covers`,
`group_switch_covers`, `upperRadius_of_test`.
What is not claimed: that the numbers on the left bound a prover's chance. Their forms are meant to
be those of the library's lemmas on the blocks; no such lemma is imported or compared here.
OnBytes/Slice/PricedRound.lean makes the comparison for these rounds (`send_share`, `bat_share_joh`,
`eps_share`, `seed_share`, `cs_share`, `base_share`), with the numbers on the left as
OnBytes/Params/EntryCovered.lean writes them: at the format's field, for a stage whose distance is
that of its main rows, each round's count, as a share of the round's typed values, is at most its
number. The second round of a code switch was held by eye against `err2` of the library's
Cb/Ld/LdSwitchWords.lean, which is not imported: the two agree if the batching there is by the
powers of one element of the extension field, with at most rows - 1 bad elements for a list's
member. OnBytes/Slice/CsErr.lean writes that `err2` out at the sizes of two stages (`cs_err2`), and
`cs_share` (OnBytes/Slice/PricedRound.lean) proves that, at the next stage's list, it is at most the
number on the left of `group_switch_covers` times the number of the round's typed values, where rows
- 1 = 1 + 3 t. There the positions are the old group's, at its radius; the list is the next group's,
at the next group's radius. One radius for all rounds of a group: the closeness rounds ask a radius
up to the lower radius, the draws of positions one from the upper radius on; that one number serves
both is tested at given groups, no law. That the list size in a planner's call is a group's
(`listOfGroups` takes the largest of several, and at least 1). A sending of more messages than one.
The rounds of the test on a table and of a link (OnBytes/Params/LinkPrices.lean). That a price is
not marked bad is a hypothesis. For proofs only; the program, that is the Lean port built from
OnBytes/, does not import this file.

-/
import OnBytes.Params.GroupPrices
import OnBytes.Params.RecordPrice

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- `powersError` encloses (rows - 1) / q, the subtraction in natural numbers; over the real
numbers. -/
theorem enclR_powersError (s : Setting) (rows : ℕ) :
    EnclR (powersError s rows) (((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ)) := enclR_ratio _ _

/-- **A list size times `fieldError` covers L degree / q**, for L at most the list size. -/
theorem list_field_covers (s : Setting) {L list : ℕ} (degree : ℕ) (hL : L ≤ list)
    (g : (Bound.ofNat list * fieldError s degree).bad = false) :
    (L : ℝ) * (degree : ℝ) / (s.cardE : ℝ) ≤
      (((Bound.ofNat list * fieldError s degree).error.val : ℚ) : ℝ) := by
  refine le_trans ?_ (le_errorR (enclR_mul (enclR_ofNat list) (enclR_fieldError s degree)) g)
  have hL' : (L : ℝ) ≤ (list : ℝ) := by exact_mod_cast hL
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hL' (by positivity)

/-- **A list size times `powersError` covers L (rows - 1) / q**, for L at most the list size. -/
theorem list_powers_covers (s : Setting) {L list : ℕ} (rows : ℕ) (hL : L ≤ list)
    (g : (Bound.ofNat list * powersError s rows).bad = false) :
    (L : ℝ) * ((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ) ≤
      (((Bound.ofNat list * powersError s rows).error.val : ℚ) : ℝ) := by
  refine le_trans ?_ (le_errorR (enclR_mul (enclR_ofNat list) (enclR_powersError s rows)) g)
  have hL' : (L : ℝ) ≤ (list : ℝ) := by exact_mod_cast hL
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hL' (by positivity)

/-- **From the upper radius on, n - e - 1 positions are at most the agreement times the length.**
The distance encloses 1 - a. -/
theorem agree_of_upperRadius {delta : Bound} {a : ℝ} {n e : ℕ} (hd : EnclR delta (1 - a))
    (g : (delta * Bound.ofNat n).bad = false) (he : upperRadius delta n ≤ e) (ha : 0 ≤ a) :
    ((n - e - 1 : ℕ) : ℝ) ≤ a * (n : ℝ) := by
  have h := lt_upperRadius hd g
  have he' : (upperRadius delta n : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  by_cases hlt : e + 1 ≤ n
  · have c : ((n - e - 1 : ℕ) : ℝ) = (n : ℝ) - (e : ℝ) - 1 := by
      have : n - e - 1 = n - (e + 1) := by omega
      rw [this, Nat.cast_sub hlt]
      push_cast
      ring
    rw [c]
    linarith
  · have z : n - e - 1 = 0 := by omega
    rw [z]
    push_cast
    positivity

/-- **The price of a draw of t positions covers ((n - e - 1) / n) ^ t**, where n - e - 1 is at most
what the agreement encloses, times n. -/
theorem positions_cover {agree : Bound} {a : ℝ} {n e : ℕ} (t : ℕ) (ha : EnclR agree a)
    (hn : 0 < n) (h : ((n - e - 1 : ℕ) : ℝ) ≤ a * (n : ℝ)) (g : (Bound.pow agree t).bad = false) :
    (((n - e - 1 : ℕ) : ℝ) / (n : ℝ)) ^ t ≤ (((Bound.pow agree t).error.val : ℚ) : ℝ) := by
  refine le_trans ?_ (le_errorR (enclR_pow ha t) g)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hn').mpr h) t

/-- **The price of the second round of a code switch covers ((n - e - 1) / n) ^ t +
L (rows - 1) / q**, for L at most the next stage's list size. -/
theorem switch_covers (s : Setting) {agree : Bound} {a : ℝ} {n e L list : ℕ} (t rows : ℕ)
    (ha : EnclR agree a) (hn : 0 < n) (h : ((n - e - 1 : ℕ) : ℝ) ≤ a * (n : ℝ)) (hL : L ≤ list)
    (g : (Bound.pow agree t + Bound.ofNat list * powersError s rows).bad = false) :
    (((n - e - 1 : ℕ) : ℝ) / (n : ℝ)) ^ t + (L : ℝ) * ((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ) ≤
      (((Bound.pow agree t + Bound.ofNat list * powersError s rows).error.val : ℚ) : ℝ) := by
  refine le_trans ?_ (le_errorR (enclR_add (enclR_pow ha t)
    (enclR_mul (enclR_ofNat list) (enclR_powersError s rows))) g)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (((n - e - 1 : ℕ) : ℝ) / (n : ℝ)) ^ t ≤ a ^ t :=
    pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hn').mpr h) t
  have hL' : (L : ℝ) ≤ (list : ℝ) := by exact_mod_cast hL
  have h2 : (L : ℝ) * ((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ) ≤
      (list : ℝ) * (((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hL' (by positivity)
  exact add_le_add h1 h2

/-- **The price of one message's sample covers (L choose 2) times the share of the clashing seeds**,
without a bias, for L at most the list size. -/
theorem sample_covers (s : Setting) {L list lg a : ℕ} (hq : 2 ≤ s.cardE) (hL : L ≤ list)
    (h1 : 1 ≤ list) (g : (sampleError s list lg a).bad = false) :
    ((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) / ((allSeeds s.cardE lg ^ a : ℕ) : ℝ) ≤
      (((sampleError s list lg a).error.val : ℚ) : ℝ) := by
  have h := record_price_covers s (L := L) (list := list) (lg := lg) (a := a) (b := 0) (x := 0) hq
    hL le_rfl (by simp) h1 g
  simpa using h

/-- **The price of a sending of one message**, the planner's sum from 0, covers the same. -/
theorem send_one_covers (s : Setting) {L list lg a : ℕ} (hq : 2 ≤ s.cardE) (hL : L ≤ list)
    (h1 : 1 ≤ list) (g : (Bound.ofWord 0 + sampleError s list lg a).bad = false) :
    ((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) / ((allSeeds s.cardE lg ^ a : ℕ) : ℝ) ≤
      (((Bound.ofWord 0 + sampleError s list lg a).error.val : ℚ) : ℝ) := by
  have h := record_share_le s (L := L) (list := list) (lg := lg) (a := a) (b := 0) (x := 0) hq hL
    le_rfl (by simp) h1
  refine le_trans ?_ (le_errorR (enclR_add (enclR_ofWord 0)
    (enclR_of_encl (encl_sampleError s list lg a))) g)
  simpa using h

/-- **The price of a link's round of seeds**, twice `sampleError`, covers the count of two
messages. -/
theorem send_two_covers (s : Setting) {L list lg a : ℕ} (hq : 2 ≤ s.cardE) (hL : L ≤ list)
    (h1 : 1 ≤ list) (g : (Bound.ofWord 2 * sampleError s list lg a).bad = false) :
    2 * (((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) /
        ((allSeeds s.cardE lg ^ a : ℕ) : ℝ)) ≤
      (((Bound.ofWord 2 * sampleError s list lg a).error.val : ℚ) : ℝ) := by
  have h := record_share_le s (L := L) (list := list) (lg := lg) (a := a) (b := 0) (x := 0) hq hL
    le_rfl (by simp) h1
  have h' : ((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) /
      ((allSeeds s.cardE lg ^ a : ℕ) : ℝ) ≤ ((sampleShare s list lg a : ℚ) : ℝ) := by
    simpa using h
  refine le_trans ?_ (le_errorR (enclR_mul (enclR_ofWord 2)
    (enclR_of_encl (encl_sampleError s list lg a))) g)
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2]
  exact mul_le_mul_of_nonneg_left h' (by norm_num)

/-- The agreement that belongs to m is not negative. -/
theorem agreeAt_nonneg (c : Word) (m : ℕ) (printed : Bool) : 0 ≤ c.agreeAt m printed := by
  unfold Word.agreeAt
  positivity

/-- **In a group under the conditions of `JohnsonGroup`, at a radius from the upper radius on, the
price of a draw of t positions at the main code's agreement covers ((n - e - 1) / n) ^ t.** -/
theorem group_positions_cover {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e)
    (gp : ((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad = false)
    (hu : upperRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n ≤ e) (t : ℕ)
    (gd : (Bound.pow (analysisOfM s g).mainAt.agree t).bad = false) :
    ((((wordOf g.main).n - e - 1 : ℕ) : ℝ) / ((wordOf g.main).n : ℝ)) ^ t ≤
      (((Bound.pow (analysisOfM s g).mainAt.agree t).error.val : ℚ) : ℝ) := by
  obtain ⟨a1, d1, _, _, _⟩ := analysisOfM_main J.mainSource J.mainGood
  have hn : 0 < (wordOf g.main).n := by unfold Word.n; positivity
  exact positions_cover t a1 hn
    (agree_of_upperRadius d1 gp hu (agreeAt_nonneg _ _ _)) gd

/-- **The price of the round before a fold's rounds covers the library's bound on the main code's
list, over q.** -/
theorem fold_epsilon_covers {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e)
    (gd : (Bound.ofNat (analysisOfM s g).list * fieldError s 1).bad = false) :
    (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) /
        (s.cardE : ℝ) ≤
      (((Bound.ofNat (analysisOfM s g).list * fieldError s 1).error.val : ℚ) : ℝ) := by
  have h := list_field_covers s 1 (listMax_le_group J) gd
  simpa using h

/-- **The price of the second round of a code switch from a group g at the radius e to a group g' at
the radius e'** covers ((n - e - 1) / n) ^ t at g's main code and the library's bound on the list of
g' at e', times (rows - 1) / q. -/
theorem group_switch_covers {s : Setting} {g g' : GroupSize} {e e' : ℕ} (J : JohnsonGroup s g e)
    (J' : JohnsonGroup s g' e')
    (gp : ((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad = false)
    (hu : upperRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n ≤ e) (t rows : ℕ)
    (gd : (Bound.pow (analysisOfM s g).mainAt.agree t +
      Bound.ofNat (analysisOfM s g').list * powersError s rows).bad = false) :
    ((((wordOf g.main).n - e - 1 : ℕ) : ℝ) / ((wordOf g.main).n : ℝ)) ^ t +
        (Cb.listMax (wordOf g'.main).n ((wordOf g'.main).n - (wordOf g'.main).k) e' : ℝ) *
          ((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ) ≤
      (((Bound.pow (analysisOfM s g).mainAt.agree t +
        Bound.ofNat (analysisOfM s g').list * powersError s rows).error.val : ℚ) : ℝ) := by
  obtain ⟨a1, d1, _, _, _⟩ := analysisOfM_main J.mainSource J.mainGood
  have hn : 0 < (wordOf g.main).n := by unfold Word.n; positivity
  exact switch_covers s t rows a1 hn (agree_of_upperRadius d1 gp hu (agreeAt_nonneg _ _ _))
    (listMax_le_group J') gd

/-- A test from which the hypotheses of `group_positions_cover` on the radius follow. -/
def upperRadiusTest (s : Setting) (g : GroupSize) (e : ℕ) : Bool :=
  !((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad &&
    decide (upperRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n ≤ e)

/-- From a yes of the test: the product is not marked bad, and e is at least the upper radius. -/
theorem upperRadius_of_test {s : Setting} {g : GroupSize} {e : ℕ}
    (h : upperRadiusTest s g e = true) :
    ((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad = false ∧
      upperRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n ≤ e := by
  unfold upperRadiusTest at h
  simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] using h

end OnBytes.Params

#print axioms OnBytes.Params.enclR_powersError
#print axioms OnBytes.Params.agreeAt_nonneg
#print axioms OnBytes.Params.send_one_covers
#print axioms OnBytes.Params.send_two_covers
#print axioms OnBytes.Params.group_switch_covers
#print axioms OnBytes.Params.upperRadius_of_test
#print axioms OnBytes.Params.group_positions_cover
#print axioms OnBytes.Params.fold_epsilon_covers
#print axioms OnBytes.Params.list_field_covers
#print axioms OnBytes.Params.list_powers_covers
#print axioms OnBytes.Params.agree_of_upperRadius
#print axioms OnBytes.Params.positions_cover
#print axioms OnBytes.Params.switch_covers
#print axioms OnBytes.Params.sample_covers
