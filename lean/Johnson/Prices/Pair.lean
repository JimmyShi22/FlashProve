-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Pair.lean: the laws of OnBytes/Params/GroupPrices.lean and MorePrices.lean on the
prices of a group's rounds under the rule `johnson`, without their condition on which code gives the
distance. The list in them stays the MAIN code's.

OnBytes/Params/GroupPrices.lean and OnBytes/Params/MorePrices.lean prove, under the fourteen
conditions `JohnsonGroup s g e`, that the prices of a fold's rounds, of the first round of a last
step, of a draw of positions, of the round before a fold and of a code switch's second round cover
numbers made of the proof library's counts and of its bound on the main code's list. One of the
fourteen is that the main code does not have the smaller rate and so gives the distance
(`maskRules g = false`). At the late stages of a proximity test the mask rows can be the longer
messages, and then the mask code gives the distance. The laws on prices use that condition at one
step only: that the library's bound on the main code's list is at most the group's list size. That
holds in both cases: the analysis's list size for the main code is at most the group's
(`mainList_le_list`). `JohnsonPair s g e`: the thirteen other conditions. Under them:
`JohnsonPair.analysis_eq`, `listMax_le_pair`, `fold_covers_pair`, `base_covers_pair`, in whole
numbers `fold_floor_pair` and `base_floor_pair`, `fold_epsilon_pair`, `positions_pair`,
`switch_pair`. The conditions follow from a yes of a test in the planner's own arithmetic
(`pairTest`, `johnsonPair_of_test`); a group under `JohnsonGroup` is under `JohnsonPair`
(`JohnsonGroup.pair`).

WHAT THESE LAWS DO NOT SERVE FOR. Where the mask code gives the distance, the main code's distance
is the larger of the two (said here without a theorem), and the proof library's list of a stage is
the list at the smaller distance (`Sg.lstJ`, OnBytes/Slice/BlocksJohnson.lean; `Sg.d`,
OnBytes/Slice/Numbers.lean): the repeated mask code's. At the typed full-size sizes it is 2 to 100
times the main code's. So at such a group the numbers on the left of these laws are true and too
small to stand between a price and a block's count: the comparison that
OnBytes/Slice/PricedRound.lean makes for a stage whose distance is that of its main rows fails for
them. For a stage whose distance is not that of its main rows no comparison of a price's number with
a block's count is made anywhere in the library. Laws with the repeated mask code's list on the left
in the main code's place are not in this file:
no law here carries that list along a whole test,
and none here evaluates numbers made of it at the
typed sizes. That those numbers serve is not shown either: no theorem ties them to the blocks'
letters; that they have the blocks' form, term by term, is a reading. This file serves a group in
which the main code gives the distance, and `mainList_le_list`.

Adapted from OnBytes/Params/GroupPrices.lean and OnBytes/Params/MorePrices.lean: the statements and
the proofs are theirs but for that step.

Main definitions: `JohnsonPair`, `pairTest`.
Main theorems: `mainList_at`, `mainList_le_list`, `listMax_le_pair`, `fold_covers_pair`,
`base_covers_pair`, `fold_floor_pair`, `base_floor_pair`, `fold_epsilon_pair`, `positions_pair`,
`switch_pair`, `johnsonPair_of_test`.
What is not claimed: what the heads of these two files do not claim, but for one sentence of
OnBytes/Params/GroupPrices.lean's: that the laws on prices do not speak of a group in which the mask
code gives the distance. These do, of the main code's list alone. That the group's list size is at
least the repeated mask code's list: proved nowhere in general.

-/
import OnBytes.Params.MorePrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices
open Bound

/-- In `analysisAt`, of a group with mask rows: the main code's list size is at most the group's. -/
theorem mainList_at {s : Setting} {g : GroupSize} {x : Proximity} (hh : g.hasMask = true)
    (hg : (analysisAt s g x).mainAt.count.bad = false) :
    (analysisAt s g x).mainAt.list ≤ (analysisAt s g x).list := by
  rw [(analysisAt_mainAt hg).1]
  unfold analysisAt
  dsimp only
  rw [if_pos hh]
  exact le_max_left _ _

/-- **Whichever code gives the distance, the main code's list size is at most the group's.** -/
theorem mainList_le_list {s : Setting} {g : GroupSize} (hh : g.hasMask = true)
    (hg : (analysisOfM s g).mainAt.count.bad = false) :
    (analysisOfM s g).mainAt.list ≤ (analysisOfM s g).list := by
  by_cases hm : maskRules g = true
  · have hA : (analysisOfM s g).mainAt =
        (analysisAt s g (atDistance s (wordOf g.main)
          (johnson (repeated g.mask g.main.logN) g.m s.printed).agree)).mainAt := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    have hB : (analysisOfM s g).list =
        (analysisAt s g (atDistance s (wordOf g.main)
          (johnson (repeated g.mask g.main.logN) g.m s.printed).agree)).list := by
      unfold analysisOfM
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hA] at hg ⊢
    rw [hB]
    exact mainList_at hh hg
  · have hm' : maskRules g = false := by simpa using hm
    have hA : analysisOfM s g = analysisAt s g (johnson (wordOf g.main) g.m s.printed) := by
      unfold analysisOfM
      simp only [hm', Bool.not_false, if_true]
    rw [hA] at hg ⊢
    exact mainList_at hh hg

/-- The conditions of `JohnsonGroup` but for the one on which code gives the distance. -/
structure JohnsonPair (s : Setting) (g : GroupSize) (e : ℕ) : Prop where
  rule : g.rule = .johnson
  hasMask : g.hasMask = true
  mainSource : (analysisOfM s g).mainAt.source = .johnson
  mainGood : (analysisOfM s g).mainAt.count.bad = false
  maskSource : (analysisOfM s g).maskAt.source = .johnson
  maskGood : (analysisOfM s g).maskAt.count.bad = false
  printed : s.printed = true
  mainK : 0 < (wordOf g.main).k
  maskK : 0 < (repeated g.mask g.main.logN).k
  radius : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ)
  mainFar : (wordOf g.main).n - (wordOf g.main).k ≤ 2 * e
  maskFar : (wordOf g.main).n - (repeated g.mask g.main.logN).k ≤ 2 * e
  slots : 1 ≤ g.slots

/-- A group under the fourteen conditions is under the thirteen. -/
theorem _root_.OnBytes.Params.JohnsonGroup.pair {s : Setting} {g : GroupSize} {e : ℕ}
    (J : JohnsonGroup s g e) : JohnsonPair s g e :=
  ⟨J.rule, J.hasMask, J.mainSource, J.mainGood, J.maskSource, J.maskGood, J.printed, J.mainK,
    J.maskK, J.radius, J.mainFar, J.maskFar, J.slots⟩

/-- Under these conditions the planner's analysis of the group is `analysisOfM`. -/
theorem JohnsonPair.analysis_eq {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e) :
    analysis s g = analysisOfM s g := analysis_johnson J.rule

/-- Under these conditions the library's bound on the main code's list is at most the group's list
size. -/
theorem listMax_le_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e) :
    Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e ≤
      (analysisOfM s g).list :=
  (listMax_le_main J.mainSource J.mainGood J.printed J.mainK J.radius J.mainFar).trans
    (mainList_le_list J.hasMask J.mainGood)

/-- **The price of round j of a fold covers the library's numbers.** -/
theorem fold_covers_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e) (j : ℕ)
    (gd : (foldRoundError s g (analysisOfM s g) j).bad = false) :
    (Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e +
        (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) * 2 +
        (if (g.hasMask && decide (j ≤ g.h)) = true then
          2 * (Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e +
            (Cb.listMax (wordOf g.main).n
              ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ)) else 0)) /
        (s.cardE : ℝ) ≤ (((foldRoundError s g (analysisOfM s g) j).error.val : ℚ) : ℝ) := by
  have hn := analysisOfM_oneLength J.hasMask J.mainGood
  obtain ⟨_, _, m2, m3, m4⟩ := analysisOfM_main J.mainSource J.mainGood
  obtain ⟨_, _, k2, k3, k4⟩ := analysisOfM_mask J.hasMask J.maskSource J.maskGood
  have heK : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ) := by
    rw [hn]
    exact J.radius
  have lK := listMax_le_mask J.hasMask J.maskSource J.maskGood J.printed J.maskK heK
    (by rw [hn]; exact J.maskFar)
  have bK := bchksBound_le_countAt k3 J.maskK (k4 J.printed) heK
  rw [hn] at lK bK
  have lK' : (Cb.listMax (wordOf g.main).n
      ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ) ≤
      ((analysisOfM s g).maskAt.list : ℝ) := by exact_mod_cast lK
  refine fold_covers s g (analysisOfM s g) j m2 k2
    (bchksBound_le_countAt m3 J.mainK (m4 J.printed) J.radius) ?_ (enclR_nonneg m2 J.mainGood)
    (enclR_nonneg k2 J.maskGood) (listMax_le_pair J) J.slots gd
  rw [hn]
  exact add_le_add bK lK'

/-- **The like for the first round of a test's last step.** -/
theorem base_covers_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e)
    (gd : (baseError s g (analysisOfM s g)).bad = false) :
    (Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e +
        (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) +
        (Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e +
          (Cb.listMax (wordOf g.main).n
            ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ))) /
        (s.cardE : ℝ) ≤ (((baseError s g (analysisOfM s g)).error.val : ℚ) : ℝ) := by
  have hn := analysisOfM_oneLength J.hasMask J.mainGood
  obtain ⟨_, _, m2, m3, m4⟩ := analysisOfM_main J.mainSource J.mainGood
  obtain ⟨_, _, k2, k3, k4⟩ := analysisOfM_mask J.hasMask J.maskSource J.maskGood
  have heK : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ) := by
    rw [hn]
    exact J.radius
  have lK := listMax_le_mask J.hasMask J.maskSource J.maskGood J.printed J.maskK heK
    (by rw [hn]; exact J.maskFar)
  have bK := bchksBound_le_countAt k3 J.maskK (k4 J.printed) heK
  rw [hn] at lK bK
  have lK' : (Cb.listMax (wordOf g.main).n
      ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ) ≤
      ((analysisOfM s g).maskAt.list : ℝ) := by exact_mod_cast lK
  have h := base_covers s g (analysisOfM s g) m2 k2
    (bchksBound_le_countAt m3 J.mainK (m4 J.printed) J.radius)
    (BK := Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e +
      (Cb.listMax (wordOf g.main).n
        ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e : ℝ))
    (by rw [hn]; exact add_le_add bK lK') (enclR_nonneg m2 J.mainGood)
    (enclR_nonneg k2 J.maskGood)
    (L := Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e)
    (listMax_le_pair J) J.slots gd
  rw [if_pos J.hasMask] at h
  exact h

/-- **The law on a fold's rounds in whole numbers.** -/
theorem fold_floor_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e) (j : ℕ)
    (gd : (foldRoundError s g (analysisOfM s g) j).bad = false) :
    (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
        Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e * 2 +
        (if (g.hasMask && decide (j ≤ g.h)) = true then
          2 * (⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
            Cb.listMax (wordOf g.main).n
              ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e) else 0) : ℕ) : ℝ)) /
        (s.cardE : ℝ) ≤ (((foldRoundError s g (analysisOfM s g) j).error.val : ℚ) : ℝ) := by
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) (fold_covers_pair J j gd)
  have f1 := Nat.floor_le (bchksBound_nonneg (wordOf g.main).n (wordOf g.main).k e)
  have f2 := Nat.floor_le
    (bchksBound_nonneg (wordOf g.main).n (repeated g.mask g.main.logN).k e)
  split
  · push_cast
    linarith
  · push_cast
    linarith

/-- **The law on the last step's first round in whole numbers.** -/
theorem base_floor_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e)
    (gd : (baseError s g (analysisOfM s g)).bad = false) :
    (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
        Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e +
        (⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
          Cb.listMax (wordOf g.main).n
            ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e) : ℕ) : ℝ)) /
        (s.cardE : ℝ) ≤ (((baseError s g (analysisOfM s g)).error.val : ℚ) : ℝ) := by
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) (base_covers_pair J gd)
  have f1 := Nat.floor_le (bchksBound_nonneg (wordOf g.main).n (wordOf g.main).k e)
  have f2 := Nat.floor_le
    (bchksBound_nonneg (wordOf g.main).n (repeated g.mask g.main.logN).k e)
  push_cast
  linarith

/-- **The price of the round before a fold's rounds.** -/
theorem fold_epsilon_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e)
    (gd : (Bound.ofNat (analysisOfM s g).list * fieldError s 1).bad = false) :
    (Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e : ℝ) /
        (s.cardE : ℝ) ≤
      (((Bound.ofNat (analysisOfM s g).list * fieldError s 1).error.val : ℚ) : ℝ) := by
  have h := list_field_covers s 1 (listMax_le_pair J) gd
  simpa using h

/-- **The price of a draw of positions at the main code's agreement.** -/
theorem positions_pair {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonPair s g e)
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
theorem switch_pair {s : Setting} {g g' : GroupSize} {e e' : ℕ} (J : JohnsonPair s g e)
    (J' : JohnsonPair s g' e')
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
    (listMax_le_pair J') gd

/-- A test, by the planner's own arithmetic, from which `JohnsonPair s g e` follows:
`johnsonGroupTest` without its question which code gives the distance. -/
def pairTest (s : Setting) (g : GroupSize) (e : ℕ) : Bool :=
  decide (g.rule = .johnson) && g.hasMask &&
    decide ((analysisOfM s g).mainAt.source = .johnson) && !(analysisOfM s g).mainAt.count.bad &&
    decide ((analysisOfM s g).maskAt.source = .johnson) && !(analysisOfM s g).maskAt.count.bad &&
    s.printed && decide (0 < (wordOf g.main).k) && decide (0 < (repeated g.mask g.main.logN).k) &&
    !((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).bad &&
    decide (e ≤ lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n) &&
    decide ((wordOf g.main).n - (wordOf g.main).k ≤ 2 * e) &&
    decide ((wordOf g.main).n - (repeated g.mask g.main.logN).k ≤ 2 * e) && decide (1 ≤ g.slots)

/-- **A yes of that test gives the conditions.** -/
theorem johnsonPair_of_test {s : Setting} {g : GroupSize} {e : ℕ}
    (h : pairTest s g e = true) : JohnsonPair s g e := by
  unfold pairTest at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩ := h
  obtain ⟨_, d2, _, _, _⟩ := analysisOfM_main a3 a4
  have hr := lowerRadius_le d2 a10
  have he : (e : ℝ) ≤ (lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n : ℝ) := by
    exact_mod_cast a11
  exact ⟨a0, a1, a3, a4, a5, a6, a7, a8, a9, he.trans hr, a12, a13, a14⟩

end OnBytes.Params.Prices
