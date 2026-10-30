-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Prox.lean: every round of a proximity test's plan is covered, from one test with code
on each stage's group.

OnBytes/Params/EntryCovered.lean has, for a group under the conditions `JohnsonGroup s g e`, that
the prices of a fold's rounds and of a code switch's two rounds cover the proof library's numbers,
against typed lists of named bounds. This file carries these laws to the planner's own list of a
proximity test, `ioppList` (OnBytes/Params/PlanListsProx.lean), for any number of stages, under the
conditions `StageOk s g e` (Johnson/Prices/Third.lean), which also admit a group in which the mask
code gives the distance (Johnson/Prices/Pair.lean) and a group whose mask code is read within a
third of its distance. `radiusOf s g`: the lower end of the main code's distance times the length,
rounded down, by the planner's own arithmetic. `stageTest s g`: `pairTest`
(Johnson/Prices/Pair.lean) or `thirdTest` (Johnson/Prices/Third.lean), and `upperRadiusTest`
(OnBytes/Params/MorePrices.lean), all at that radius; the last asks that the upper end, rounded
down, is not above it, so that one radius serves the closeness rounds and the draws of positions.
`CoveredBy s c cnt y`: the number cnt is at most the error of the round of the description y.
`ioppCounts`: for the batching the first group's list times (rows - 1) / q; then, stage by stage,
`foldNums` and the library's `switchCounts`; for the last step `lastNum` and the library's
`positionsShare`. `iopp_covered`: if every stage's group passes the test and no bound of the list is
marked bad, each number is at most the error of its round, one by one. All at every setting and all
sizes: nothing is evaluated. THE LIST IN THESE NUMBERS IS THE MAIN CODE's AT EVERY STAGE. At a stage
in which the mask code gives the distance that is not the list of the proof library's stage, which
is the list at the smaller distance, and the numbers are too small to stand between a price and a
block's count (the head of Johnson/Prices/Pair.lean). No walk in this file goes with the
list of the code that gives the distance.

Main definitions: `radiusOf`, `stageTest`, `CoveredBy`, `foldNums`, `stagesCounts`, `ioppCounts`.
Main theorems: `foldFrom_covered`, `foldList_covered`, `csList_covered`, `baseList_covered`,
`stages_covered`, `iopp_covered`, `covers_of_share`.
What is not claimed: that a group passes the test. That the numbers bound a prover's chance: see the
heads of Johnson/Prices/Third.lean and Johnson/Prices/Pair.lean and of
OnBytes/Params/EntryCovered.lean, GroupPrices.lean and MorePrices.lean, above all on the repeated
mask code, on a stage whose distance is not that of its main rows, and on the number e + 1 within a
third. A group without mask rows, or under another rule than `johnson`: it does not pass the test.

-/
import Johnson.Prices.Specs
import Johnson.Prices.Third
import OnBytes.Params.EntryCovered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices
open Bound

/-- The lower end of the main code's distance times the length, rounded down. -/
def radiusOf (s : Setting) (g : GroupSize) : ℕ :=
  lowerRadius (analysisOfM s g).mainAt.delta (wordOf g.main).n

/-- `pairTest` or `thirdTest`, and the library's `upperRadiusTest`, all at `radiusOf`. -/
def stageTest (s : Setting) (g : GroupSize) : Bool :=
  (pairTest s g (radiusOf s g) || thirdTest s g (radiusOf s g)) &&
    upperRadiusTest s g (radiusOf s g)

/-- What a yes of the test gives. -/
theorem stageTest_parts {s : Setting} {g : GroupSize} (h : stageTest s g = true) :
    StageOk s g (radiusOf s g) ∧ upperRadiusTest s g (radiusOf s g) = true := by
  unfold stageTest at h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.1 with h1 | h1
  · exact ⟨.of_pair (johnsonPair_of_test h1), h.2⟩
  · exact ⟨.of_third (johnsonThird_of_test h1), h.2⟩

/-- The number is at most the error of the description's round. -/
def CoveredBy (s : Setting) (c : Scope) (cnt : ℝ) (y : RoundSpec) : Prop :=
  cnt ≤ (((y.round s c).error.val : ℚ) : ℝ)

/-- Under a plain scope: from the routine's bound. -/
theorem coveredBy_said {s : Setting} {c : Scope} (hs : plainScope s c) {name : String}
    {why : ErrorKind} {error : Bound} {d : Draws} {bytes roots answers : ℕ} {cnt : ℝ}
    (h : cnt ≤ ((error.error.val : ℚ) : ℝ)) :
    CoveredBy s c cnt (.said name why error d bytes roots answers) := by
  unfold CoveredBy
  rw [said_error hs]
  exact h

/-- Under a plain scope: the routine's bound is not marked bad if the priced one is not. -/
theorem good_said {s : Setting} {c : Scope} (hs : plainScope s c) {name : String}
    {why : ErrorKind} {error : Bound} {d : Draws} {bytes roots answers : ℕ}
    (h : ((RoundSpec.said name why error d bytes roots answers).bound s c).bad = false) :
    error.bad = false := by
  rwa [said_bound hs] at h

/-- A relation that holds place by place on two pairs of lists holds on the joined lists. -/
theorem forall₂_app {α β : Type} {R : α → β → Prop} {a b : List α} {x y : List β}
    (h1 : List.Forall₂ R a x) (h2 : List.Forall₂ R b y) : List.Forall₂ R (a ++ b) (x ++ y) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact List.Forall₂.cons h ih

/-- The numbers of the round before a fold's rounds and of the rounds j = 1 .. k. -/
noncomputable def foldNums (s : Setting) (g : GroupSize) (e : ℕ) : List ℝ :=
  ((groupList g e : ℝ) / (s.cardE : ℝ)) :: (List.range' 1 g.k).map fun j => foldNum s g e j

section
variable {s : Setting} {c : Scope}

/-- The rounds of a fold from round j on. -/
theorem foldFrom_covered {g : GroupSize} {e : ℕ} (hs : plainScope s c) (J : StageOk s g e) :
    ∀ (fuel j : ℕ),
      (∀ y ∈ foldFromList s g (analysisOfM s g) fuel j, (y.bound s c).bad = false) →
      List.Forall₂ (CoveredBy s c) ((List.range' j fuel).map (foldNum s g e))
        (foldFromList s g (analysisOfM s g) fuel j)
  | 0, _, _ => List.Forall₂.nil
  | fuel + 1, j, h => by
    rw [List.range'_succ, List.map_cons]
    show List.Forall₂ _ _
      (foldRound s g (analysisOfM s g) j :: foldFromList s g (analysisOfM s g) fuel (j + 1))
    refine List.Forall₂.cons ?_
      (foldFrom_covered hs J fuel (j + 1) fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hg := h (foldRound s g (analysisOfM s g) j) (List.mem_cons_self ..)
    unfold foldRound at hg ⊢
    exact coveredBy_said hs (J.fold j (good_said hs hg))

/-- **A fold's rounds.** -/
theorem foldList_covered {g : GroupSize} {e : ℕ} (hs : plainScope s c) (J : StageOk s g e)
    (roots : ℕ) (h : ∀ y ∈ foldList s g roots, (y.bound s c).bad = false) :
    List.Forall₂ (CoveredBy s c) (foldNums s g e) (foldList s g roots) := by
  unfold foldList foldFirst at h ⊢
  rw [J.main.analysis_eq] at h ⊢
  unfold foldNums
  refine List.Forall₂.cons ?_
    (foldFrom_covered hs J g.k 1 fun y hy => h y (List.mem_cons_of_mem _ hy))
  exact coveredBy_said hs (fold_epsilon_main J.main (good_said hs (h _ (List.mem_cons_self ..))))

/-- **A code switch's two rounds.** -/
theorem csList_covered {g g' : GroupSize} {e e' : ℕ} (hs : plainScope s c) (hq : 2 ≤ s.cardE)
    (J : StageOk s g e) (J' : StageOk s g' e') (hu : upperRadiusTest s g e = true)
    (cube oldRows symbols roots : ℕ)
    (h : ∀ y ∈ csList s c g g' cube oldRows symbols roots, (y.bound s c).bad = false) :
    List.Forall₂ (CoveredBy s c)
      (switchCounts s g g' e e' cube (csCount s c g g' oldRows symbols)
        (oldRows + s.samples + symbols * csCount s c g g' oldRows symbols))
      (csList s c g g' cube oldRows symbols roots) := by
  obtain ⟨gp, hu'⟩ := upperRadius_of_test hu
  unfold csList at h ⊢
  generalize csCount s c g g' oldRows symbols = t at h ⊢
  unfold sendSeed at h ⊢
  simp only [sampleSum, largestList] at h ⊢
  rw [J.main.analysis_eq, J'.main.analysis_eq] at h ⊢
  unfold switchCounts
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · exact coveredBy_said hs (send_one_covers s hq
      ((listMax_le_mainG J'.main).trans (le_max_left _ _)) (le_max_right _ _)
      (good_said hs (h _ (List.mem_cons_self ..))))
  · exact coveredBy_said hs (switch_main J.main J'.main gp hu' t _
      (good_said hs (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

/-- **The last step's two rounds.** -/
theorem baseList_covered {g : GroupSize} {e : ℕ} (hs : plainScope s c) (J : StageOk s g e)
    (hu : upperRadiusTest s g e = true) (roots : ℕ)
    (h : ∀ y ∈ baseList s c g roots, (y.bound s c).bad = false) :
    List.Forall₂ (CoveredBy s c) [lastNum s g e, positionsShare g e (baseCount s c g)]
      (baseList s c g roots) := by
  obtain ⟨gp, hu'⟩ := upperRadius_of_test hu
  unfold baseList at h ⊢
  generalize baseCount s c g = t at h ⊢
  rw [J.main.analysis_eq] at h ⊢
  exact .cons (coveredBy_said hs (J.base (good_said hs (h _ (List.mem_cons_self ..)))))
    (.cons (coveredBy_said hs (positions_main J.main gp hu' t
      (good_said hs (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) .nil)

end

/-- The numbers of the rounds of the stages of a proximity test, in the order of `stagesList`. -/
noncomputable def stagesCounts (s : Setting) (c : Scope) : List StageSize → List ℝ
  | x :: y :: rest =>
    foldNums s x.g (radiusOf s x.g) ++
      (switchCounts s x.g y.g (radiusOf s x.g) (radiusOf s y.g) (stageCubeBits y.g)
          (csCount s c x.g y.g 1 (x.g.slots + (if x.g.hasMask then 2 else 0)))
          (1 + s.samples + (x.g.slots + (if x.g.hasMask then 2 else 0)) *
            csCount s c x.g y.g 1 (x.g.slots + (if x.g.hasMask then 2 else 0))) ++
        stagesCounts s c (y :: rest))
  | [x] => [lastNum s x.g (radiusOf s x.g),
      positionsShare x.g (radiusOf s x.g) (baseCount s c x.g)]
  | [] => []

/-- **The rounds of the stages of a proximity test.** -/
theorem stages_covered {s : Setting} {c : Scope} (hs : plainScope s c) (hq : 2 ≤ s.cardE)
    (fm : ℕ) (ride : Bool) :
    ∀ (first : Bool) (st : List StageSize), (∀ x ∈ st, stageTest s x.g = true) →
      (∀ y ∈ stagesList s c fm ride first st, (y.bound s c).bad = false) →
      List.Forall₂ (CoveredBy s c) (stagesCounts s c st) (stagesList s c fm ride first st)
  | _, [], _, _ => by
    unfold stagesCounts stagesList
    exact List.Forall₂.nil
  | _, [x], ht, hg => by
    unfold stagesList at hg ⊢
    unfold stagesCounts
    obtain ⟨J, hu⟩ := stageTest_parts (ht x (List.mem_cons_self ..))
    exact baseList_covered hs J hu _ hg
  | first, x :: y :: rest, ht, hg => by
    unfold stagesList at hg ⊢
    unfold stagesCounts
    obtain ⟨J, hu⟩ := stageTest_parts (ht x (List.mem_cons_self ..))
    obtain ⟨J', -⟩ := stageTest_parts (ht y (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact forall₂_app (foldList_covered hs J _ fun z hz => hg z (List.mem_append_left _ hz))
      (forall₂_app
        (csList_covered hs hq J J' hu _ _ _ _ fun z hz =>
          hg z (List.mem_append_right _ (List.mem_append_left _ hz)))
        (stages_covered hs hq fm ride false (y :: rest)
          (fun z hz => ht z (List.mem_cons_of_mem _ hz))
          fun z hz => hg z (List.mem_append_right _ (List.mem_append_right _ hz))))

/-- The numbers of the rounds of a proximity test, in the order of `ioppList`. -/
noncomputable def ioppCounts (s : Setting) (c : Scope) (st : List StageSize) (rows : ℕ) : List ℝ :=
  ((st.head?.map fun x => (groupList x.g (radiusOf s x.g) : ℝ) * ((rows - 1 : ℕ) : ℝ) /
    (s.cardE : ℝ)).getD 0) :: stagesCounts s c st

/-- **Every round of a proximity test is covered**, if every stage's group passes the test and no
bound of the list is marked bad. -/
theorem iopp_covered {s : Setting} {c : Scope} (hs : plainScope s c) (hq : 2 ≤ s.cardE)
    (st : List StageSize) (rows fm : ℕ) (ride : Bool) (ht : ∀ x ∈ st, stageTest s x.g = true)
    (hg : ∀ y ∈ ioppList s c st rows fm ride, (y.bound s c).bad = false) :
    List.Forall₂ (CoveredBy s c) (ioppCounts s c st rows) (ioppList s c st rows fm ride) := by
  unfold ioppList at hg ⊢
  unfold ioppCounts
  refine List.Forall₂.cons ?_
    (stages_covered hs hq fm ride true st ht fun y hy => hg y (List.mem_cons_of_mem _ hy))
  have h0 := hg _ (List.mem_cons_self ..)
  cases st with
  | nil =>
    unfold CoveredBy
    simp only [List.head?_nil, Option.map_none, Option.getD_none]
    exact_mod_cast Binary.val_nonneg _
  | cons x t =>
    obtain ⟨J, -⟩ := stageTest_parts (ht x (List.mem_cons_self ..))
    unfold batRound at h0 ⊢
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, largestList,
      List.head?_cons, Option.map_some, Option.getD_some] at h0 ⊢
    rw [J.main.analysis_eq] at h0 ⊢
    exact coveredBy_said hs (list_powers_covers s rows
      ((listMax_le_mainG J.main).trans (le_max_left _ _)) (good_said hs h0))

/-- `Covers` from the same inequality between real numbers. -/
theorem covers_of_real' {r : PlanRound} {count total : ℕ}
    (h : (count : ℝ) ≤ ((r.error.val : ℚ) : ℝ) * (total : ℝ)) : Covers r count total := by
  unfold Covers
  exact_mod_cast h

/-- From a share to a count: a number that is at most a round's error covers every count that is at
most the number times the total. -/
theorem covers_of_share {r : PlanRound} {cnt : ℝ} {count total : ℕ}
    (h : cnt ≤ ((r.error.val : ℚ) : ℝ)) (hc : (count : ℝ) ≤ cnt * (total : ℝ)) :
    Covers r count total :=
  covers_of_real' (hc.trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)))

end OnBytes.Params.Prices
