-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Third.lean: the laws on the prices of a group's rounds where the main code is read by
the Johnson count and the mask code within a third of its distance; and one form, `StageOk`, for
both sorts of group.

Where the group's radius lies within a third of the repeated mask code's distance, the planner gives
that code the source `.third`, the count errors + 1 and the list size 1 (`atDistance`,
OnBytes/Params/Distance.lean). The conditions `JohnsonGroup` (OnBytes/Params/GroupPrices.lean) and
`JohnsonPair` (Johnson/Prices/Pair.lean) ask the source `.johnson` of both codes, so they do not
reach such a group. `JohnsonMain s g e`: the nine conditions of `JohnsonPair` that speak of the main
code, the rule, the mask rows' presence, the reading of m and the slots. Under them: the laws that
read the main code alone (`listMax_le_mainG`, `fold_epsilon_main`, `positions_main`, `switch_main`).
`JohnsonThird s g e`: these nine; the mask code's source is `.third`; its count in the analysis is,
as a bound, the whole number e + 1. Under them the price of round j of a fold covers the library's
count at the main code, twice its bound on the main code's list and, while mask rows are folded,
twice e + 1, all over q (`fold_covers_third`); the like for the first round of a last step
(`base_covers_third`). `maskNum s g e`: e + 1 where the mask code's source is `.third`, else the
library's count at the repeated mask code, rounded down, with its bound on that code's list.
`foldNum`, `lastNum`: the numbers of a fold's round and of a last step's first round with `maskNum`
for the mask rows. `StageOk s g e`: `JohnsonMain`, and the two prices cover `foldNum` and `lastNum`.
It follows from `JohnsonPair` and from `JohnsonThird` (`StageOk.of_pair`, `StageOk.of_third`).
`thirdTest`: a test in the planner's own arithmetic from which `JohnsonThird` follows.

Adapted from OnBytes/Params/GroupPrices.lean and OnBytes/Params/MorePrices.lean, as
Johnson/Prices/Pair.lean is.

Main definitions: `JohnsonMain`, `JohnsonThird`, `maskNum`, `foldNum`, `lastNum`, `StageOk`,
`thirdTest`.
Main theorems: `listMax_le_mainG`, `fold_epsilon_main`, `positions_main`, `switch_main`,
`fold_covers_third`, `base_covers_third`, `StageOk.of_pair`, `StageOk.of_third`,
`johnsonThird_of_test`.
What is not claimed: that e + 1 bounds anything of mask rows: that a line through two words has at
most e + 1 points within e of a code whose distance is above 3 e is the proof library's matter, and
it is not imported. That the count is e + 1 wherever the source is `.third`: it is a condition here,
which the test compares. What the head of Johnson/Prices/Pair.lean does not claim.

-/
import Johnson.Prices.Pair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices
open Bound

/-- The conditions that speak of the main code, the rule, the reading of m and the slots. -/
structure JohnsonMain (s : Setting) (g : GroupSize) (e : ℕ) : Prop where
  rule : g.rule = .johnson
  hasMask : g.hasMask = true
  mainSource : (analysisOfM s g).mainAt.source = .johnson
  mainGood : (analysisOfM s g).mainAt.count.bad = false
  printed : s.printed = true
  mainK : 0 < (wordOf g.main).k
  radius : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ)
  mainFar : (wordOf g.main).n - (wordOf g.main).k ≤ 2 * e
  slots : 1 ≤ g.slots

/-- A group under the thirteen conditions is under these nine. -/
theorem JohnsonPair.main {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e) :
    JohnsonMain s g e :=
  ⟨J.rule, J.hasMask, J.mainSource, J.mainGood, J.printed, J.mainK, J.radius, J.mainFar, J.slots⟩

/-- Under these conditions the planner's analysis of the group is `analysisOfM`. -/
theorem JohnsonMain.analysis_eq {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonMain s g e) :
    analysis s g = analysisOfM s g := analysis_johnson J.rule

/-- The library's bound on the main code's list is at most the group's list size. -/
theorem listMax_le_mainG {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonMain s g e) :
    Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e ≤
      (analysisOfM s g).list :=
  (listMax_le_main J.mainSource J.mainGood J.printed J.mainK J.radius J.mainFar).trans
    (mainList_le_list J.hasMask J.mainGood)

/-- **The price of the round before a fold's rounds.** -/
theorem fold_epsilon_main {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonMain s g e)
    (gd : (Bound.ofNat (analysisOfM s g).list * fieldError s 1).bad = false) :
    (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) /
        (s.cardE : ℝ) ≤
      (((Bound.ofNat (analysisOfM s g).list * fieldError s 1).error.val : ℚ) : ℝ) := by
  have h := list_field_covers s 1 (listMax_le_mainG J) gd
  simpa using h

/-- **The price of a draw of positions at the main code's agreement.** -/
theorem positions_main {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonMain s g e)
    (gp : ((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad = false)
    (hu : upperRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n ≤ e) (t : ℕ)
    (gd : (Bound.pow (analysisOfM s g).mainAt.agree t).bad = false) :
    ((((wordOf g.main).n - e - 1 : ℕ) : ℝ) / ((wordOf g.main).n : ℝ)) ^ t ≤
      (((Bound.pow (analysisOfM s g).mainAt.agree t).error.val : ℚ) : ℝ) := by
  obtain ⟨a1, d1, _, _, _⟩ := analysisOfM_main J.mainSource J.mainGood
  have hn : 0 < (wordOf g.main).n := by unfold Word.n; positivity
  exact positions_cover t a1 hn
    (agree_of_upperRadius d1 gp hu (agreeAt_nonneg _ _ _)) gd

/-- **The price of the second round of a code switch.** -/
theorem switch_main {s : Setting} {g g' : GroupSize} {e e' : ℕ} (J : JohnsonMain s g e)
    (J' : JohnsonMain s g' e')
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
    (listMax_le_mainG J') gd

/-- The main code by the Johnson count, the mask code within a third of its distance. -/
structure JohnsonThird (s : Setting) (g : GroupSize) (e : ℕ) : Prop where
  main : JohnsonMain s g e
  maskThird : (analysisOfM s g).maskAt.source = .third
  maskCount : (analysisOfM s g).maskAt.count = Bound.ofNat (e + 1)

/-- **The price of round j of a fold**, the mask code within a third. -/
theorem fold_covers_third {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonThird s g e) (j : ℕ)
    (gd : (foldRoundError s g (analysisOfM s g) j).bad = false) :
    (Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e +
        (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) * 2 +
        (if (g.hasMask && decide (j ≤ g.h)) = true then 2 * ((e + 1 : ℕ) : ℝ) else 0)) /
        (s.cardE : ℝ) ≤ (((foldRoundError s g (analysisOfM s g) j).error.val : ℚ) : ℝ) := by
  obtain ⟨_, _, m2, m3, m4⟩ := analysisOfM_main J.main.mainSource J.main.mainGood
  have k2 : EnclR (analysisOfM s g).maskAt.count ((e + 1 : ℕ) : ℝ) := by
    rw [J.maskCount]
    exact enclR_ofNat (e + 1)
  exact fold_covers s g (analysisOfM s g) j m2 k2
    (bchksBound_le_countAt m3 J.main.mainK (m4 J.main.printed) J.main.radius) le_rfl
    (enclR_nonneg m2 J.main.mainGood) (Nat.cast_nonneg _) (listMax_le_mainG J.main)
    J.main.slots gd

/-- **The like for the first round of a test's last step.** -/
theorem base_covers_third {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonThird s g e)
    (gd : (baseError s g (analysisOfM s g)).bad = false) :
    (Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e +
        (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) +
        ((e + 1 : ℕ) : ℝ)) / (s.cardE : ℝ) ≤
      (((baseError s g (analysisOfM s g)).error.val : ℚ) : ℝ) := by
  obtain ⟨_, _, m2, m3, m4⟩ := analysisOfM_main J.main.mainSource J.main.mainGood
  have k2 : EnclR (analysisOfM s g).maskAt.count ((e + 1 : ℕ) : ℝ) := by
    rw [J.maskCount]
    exact enclR_ofNat (e + 1)
  have h := base_covers s g (analysisOfM s g) m2 k2
    (bchksBound_le_countAt m3 J.main.mainK (m4 J.main.printed) J.main.radius)
    (BK := ((e + 1 : ℕ) : ℝ)) le_rfl (enclR_nonneg m2 J.main.mainGood) (Nat.cast_nonneg _)
    (L := Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e)
    (listMax_le_mainG J.main) J.main.slots gd
  rw [if_pos J.main.hasMask] at h
  exact h

/-- The whole number for the mask rows' closeness term. -/
noncomputable def maskNum (s : Setting) (g : GroupSize) (e : ℕ) : ℕ :=
  if (analysisOfM s g).maskAt.source = .third then e + 1
  else ⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
    Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e

/-- The number of round j of a fold, in whole numbers, over q. -/
noncomputable def foldNum (s : Setting) (g : GroupSize) (e j : ℕ) : ℝ :=
  (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
      Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e * 2 +
      (if (g.hasMask && decide (j ≤ g.h)) = true then 2 * maskNum s g e else 0) : ℕ) : ℝ)) /
    (s.cardE : ℝ)

/-- The number of the first round of a test's last step, in whole numbers, over q. -/
noncomputable def lastNum (s : Setting) (g : GroupSize) (e : ℕ) : ℝ :=
  (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
      Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e +
      maskNum s g e : ℕ) : ℝ)) / (s.cardE : ℝ)

/-- What the laws on a proximity test's rounds ask of a stage's group. -/
structure StageOk (s : Setting) (g : GroupSize) (e : ℕ) : Prop where
  main : JohnsonMain s g e
  fold : ∀ j, (foldRoundError s g (analysisOfM s g) j).bad = false →
    foldNum s g e j ≤ (((foldRoundError s g (analysisOfM s g) j).error.val : ℚ) : ℝ)
  base : (baseError s g (analysisOfM s g)).bad = false →
    lastNum s g e ≤ (((baseError s g (analysisOfM s g)).error.val : ℚ) : ℝ)

/-- **Both codes by the Johnson count.** -/
theorem StageOk.of_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e) :
    StageOk s g e := by
  have hm : maskNum s g e =
      ⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
        Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e :=
    if_neg (by rw [J.maskSource]; decide)
  refine ⟨J.main, fun j gd => ?_, fun gd => ?_⟩
  · unfold foldNum
    rw [hm]
    exact fold_floor_pair J j gd
  · unfold lastNum
    rw [hm]
    exact base_floor_pair J gd

/-- **The mask code within a third.** -/
theorem StageOk.of_third {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonThird s g e) :
    StageOk s g e := by
  have hm : maskNum s g e = e + 1 := if_pos J.maskThird
  have f1 := Nat.floor_le (bchksBound_nonneg (wordOf g.main).n (wordOf g.main).k e)
  refine ⟨J.main, fun j gd => ?_, fun gd => ?_⟩
  · unfold foldNum
    rw [hm]
    refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      (fold_covers_third J j gd)
    split
    · push_cast
      linarith
    · push_cast
      linarith
  · unfold lastNum
    rw [hm]
    refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) (base_covers_third J gd)
    push_cast
    linarith

/-- A test, by the planner's own arithmetic, from which `JohnsonThird s g e` follows. -/
def thirdTest (s : Setting) (g : GroupSize) (e : ℕ) : Bool :=
  decide (g.rule = .johnson) && g.hasMask &&
    decide ((analysisOfM s g).mainAt.source = .johnson) && !(analysisOfM s g).mainAt.count.bad &&
    decide ((analysisOfM s g).maskAt.source = .third) &&
    decide ((analysisOfM s g).maskAt.count = Bound.ofNat (e + 1)) &&
    s.printed && decide (0 < (wordOf g.main).k) &&
    !((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad &&
    decide (e ≤ lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n) &&
    decide ((wordOf g.main).n - (wordOf g.main).k ≤ 2 * e) && decide (1 ≤ g.slots)

/-- **A yes of that test gives the conditions.** -/
theorem johnsonThird_of_test {s : Setting} {g : GroupSize} {e : ℕ}
    (h : thirdTest s g e = true) : JohnsonThird s g e := by
  unfold thirdTest at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a10⟩, a11⟩, a12⟩, a14⟩ := h
  obtain ⟨_, d2, _, _, _⟩ := analysisOfM_main a3 a4
  have hr := lowerRadius_le d2 a10
  have he : (e : ℝ) ≤ (lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n : ℝ) := by
    exact_mod_cast a11
  exact ⟨⟨a0, a1, a3, a4, a7, a8, he.trans hr, a12, a14⟩, a5, a6⟩

end OnBytes.Params.Prices
