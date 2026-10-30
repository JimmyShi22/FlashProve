-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryCovered.lean: counts for the rounds of a proximity test and of a link, in whole
positions, lists and whole numbers of exceptional points; and that a fold's rounds and a code
switch's rounds are covered by the planner's prices, as statements on lists.

OnBytes/Params/EntryPricesRecord.lean lists the rounds of an entry's plan as names with the
planner's formulas (`foldBounds`, `switchBounds`). This file writes beside them the numbers that the
laws on prices have on their left sides. `Covered c x` says that the number c is at most the error
of the named bound x. For a group g and a radius e: `groupList` is the proof library's `Cb.listMax`
at the main code; `foldCount` the count of round j of a fold in whole numbers, over q; `foldCounts`
the list for the round before a fold's rounds and the rounds j = 1 .. k; `positionsShare` is ((n - e
- 1) / n) ^ t; `seedsShare` is (L choose 2) times, for each answer, the share of the clashing seeds;
`switchCounts` the list for the two rounds of a code switch from g at e to g' at e'; `lastStepCount`
the count of a last step's first round; `linkPointCount` and `linkPositionsShare` those of a link's
fold point and of its two lists of columns. For a group under the conditions `JohnsonGroup`
(OnBytes/Params/GroupPrices.lean), where no bound of the list is marked bad, a fold's rounds are
covered, one by one (`fold_covered`); for two such groups, the first at a radius that is also at
least the upper radius, where the extension field has two elements or more and neither bound is
marked bad, so are a code switch's two rounds (`switch_covered`). Lists that are covered can be put
one after the other (`covered_append`). `fieldError` covers degree / q (`field_covers`), and the
error of the bound 0 is not negative (`zero_covers`).

Main definitions: `Covered`, `groupList`, `foldCount`, `foldCounts`, `positionsShare`, `seedsShare`,
`switchCounts`, `lastStepCount`, `linkPointCount`, `linkPositionsShare`.
Main theorems: `fold_covered`, `switch_covered`, `covered_append`, `field_covers`, `zero_covers`.
What is not claimed: that any of these numbers bounds a prover's chance in its round: their forms
are meant to be those of the library's lemmas on the blocks; no such lemma is imported or compared
here. OnBytes/Slice/PricedRound.lean makes the comparison: at the format's field, for a stage whose
distance is that of its main rows, the counts of a link with records, of its batching and of a chain
of stages, each as a share of its round's typed values, are at most these numbers. What the heads of
OnBytes/Params/GroupPrices.lean, OnBytes/Params/MorePrices.lean and OnBytes/Params/LinkPrices.lean
do not claim. For proofs only; the program, that is the Lean port built from OnBytes/, does not
import this file.

-/
import OnBytes.Params.EntryPricesRecord

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- A count is covered by a named bound: it is at most the bound's error. -/
def Covered (c : ℝ) (x : String × Bound) : Prop := c ≤ ((x.2.error.val : ℚ) : ℝ)

/-- The library's bound on the list of a group's main code at the radius e. -/
def groupList (g : GroupSize) (e : ℕ) : ℕ :=
  Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e

/-- The count of round j of a fold, in whole numbers, over q. -/
noncomputable def foldCount (s : Setting) (g : GroupSize) (e j : ℕ) : ℝ :=
  (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
      Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e * 2 +
      (if (g.hasMask && decide (j ≤ g.h)) = true then
        2 * (⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
          Cb.listMax (wordOf g.main).n
            ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e) else 0) : ℕ) : ℝ)) /
    (s.cardE : ℝ)

/-- The counts of the round before a fold's rounds and of the rounds j = 1 .. k. -/
noncomputable def foldCounts (s : Setting) (g : GroupSize) (e : ℕ) : List ℝ :=
  ((groupList g e : ℝ) / (s.cardE : ℝ)) :: (List.range' 1 g.k).map fun j => foldCount s g e j

/-- The share of t positions that all miss the e + 1 or more places where a word is off. -/
noncomputable def positionsShare (g : GroupSize) (e t : ℕ) : ℝ :=
  ((((wordOf g.main).n - e - 1 : ℕ) : ℝ) / ((wordOf g.main).n : ℝ)) ^ t

/-- (L choose 2) times, for each answer, the share of the seeds at which one pair can clash. -/
noncomputable def seedsShare (s : Setting) (L cube answers : ℕ) : ℝ :=
  ((L.choose 2 * clashSeeds s.cardE cube ^ answers : ℕ) : ℝ) /
    ((allSeeds s.cardE cube ^ answers : ℕ) : ℝ)

/-- The counts of the two rounds of a code switch from g at the radius e to g' at the radius e'. -/
noncomputable def switchCounts (s : Setting) (g g' : GroupSize) (e e' cube t rows : ℕ) : List ℝ :=
  [seedsShare s (groupList g' e') cube s.samples,
    positionsShare g e t + (groupList g' e' : ℝ) * ((rows - 1 : ℕ) : ℝ) / (s.cardE : ℝ)]

/-- **A fold's rounds are covered**, for a group under the conditions, where none of the bounds is
marked bad. -/
theorem fold_covered {s : Setting} {g : GroupSize} {e : ℕ} (J : JohnsonGroup s g e)
    (hb : ∀ x ∈ foldBounds s g, x.2.bad = false) :
    List.Forall₂ Covered (foldCounts s g e) (foldBounds s g) := by
  have h0 : (Bound.ofNat (analysisOfM s g).list * fieldError s 1).bad = false :=
    hb ("FOLD epsilon", Bound.ofNat (analysisOfM s g).list * fieldError s 1)
      (List.mem_cons_self ..)
  have hj : ∀ j ∈ List.range' 1 g.k, (foldRoundError s g (analysisOfM s g) j).bad = false :=
    fun j hj => hb ("FOLD round", foldRoundError s g (analysisOfM s g) j)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
  refine List.Forall₂.cons (fold_epsilon_covers J h0) ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun j h => fold_covers_floor J j (hj j h)

/-- **A code switch's two rounds are covered**, for two groups under the conditions, the first at a
radius that is also at least the upper radius, where neither bound is marked bad. -/
theorem switch_covered {s : Setting} {g g' : GroupSize} {e e' : ℕ} (J : JohnsonGroup s g e)
    (J' : JohnsonGroup s g' e') (hu : upperRadiusTest s g e = true) (hq : 2 ≤ s.cardE)
    (cube t rows : ℕ) (hb : ∀ x ∈ switchBounds s g g' cube t rows, x.2.bad = false) :
    List.Forall₂ Covered (switchCounts s g g' e e' cube t rows)
      (switchBounds s g g' cube t rows) := by
  obtain ⟨gp, hu'⟩ := upperRadius_of_test hu
  have h1 : (Bound.ofWord 0 +
      sampleError s (max (analysisOfM s g').list 1) cube s.samples).bad = false :=
    hb ("SEND seed", Bound.ofWord 0 +
      sampleError s (max (analysisOfM s g').list 1) cube s.samples) (List.mem_cons_self ..)
  have h2 : (Bound.pow (analysisOfM s g).mainAt.agree t +
      Bound.ofNat (analysisOfM s g').list * powersError s rows).bad = false :=
    hb ("CS", Bound.pow (analysisOfM s g).mainAt.agree t +
      Bound.ofNat (analysisOfM s g').list * powersError s rows)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact List.Forall₂.cons
    (send_one_covers s hq ((listMax_le_group J').trans (le_max_left _ _)) (le_max_right _ _) h1)
    (List.Forall₂.cons (group_switch_covers J J' gp hu' t rows h2) List.Forall₂.nil)

/-- Two lists that are covered, one after the other. -/
theorem covered_append {a b : List ℝ} {x y : List (String × Bound)}
    (h1 : List.Forall₂ Covered a x) (h2 : List.Forall₂ Covered b y) :
    List.Forall₂ Covered (a ++ b) (x ++ y) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact List.Forall₂.cons h ih

/-- The count of the first round of a test's last step, in whole numbers, over q. -/
noncomputable def lastStepCount (s : Setting) (g : GroupSize) (e : ℕ) : ℝ :=
  (((⌊Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e⌋₊ +
      Cb.listMax (wordOf g.main).n ((wordOf g.main).n - (wordOf g.main).k) e +
      (⌊Cb.bchksBound (wordOf g.main).n (repeated g.mask g.main.logN).k e⌋₊ +
        Cb.listMax (wordOf g.main).n
          ((wordOf g.main).n - (repeated g.mask g.main.logN).k) e) : ℕ) : ℝ)) / (s.cardE : ℝ)

/-- The count of a link's fold point, in whole numbers, over q: e1 the further table's radius, e0
the first table's. -/
noncomputable def linkPointCount (s : Setting) (T : TableSize) (e1 e0 : ℕ) : ℝ :=
  (((T.v + (T.v * ⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e1⌋₊ +
        Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e1 * T.v) +
      (T.v * ⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e0⌋₊ +
        Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e0 * T.v) :
      ℕ) : ℝ)) / (s.cardE : ℝ)

/-- The share of a link's two lists of columns: the larger of the two lists' shares. -/
noncomputable def linkPositionsShare (T : TableSize) (e0 ej t0 tj : ℕ) : ℝ :=
  max (((((wordOf T.code).n - e0 - 1 : ℕ) : ℝ) / ((wordOf T.code).n : ℝ)) ^ t0)
    (((((wordOf T.code).n - ej - 1 : ℕ) : ℝ) / ((wordOf T.code).n : ℝ)) ^ tj)

/-- `fieldError` covers degree / q. -/
theorem field_covers (s : Setting) (degree : ℕ) (g : (fieldError s degree).bad = false) :
    (degree : ℝ) / (s.cardE : ℝ) ≤ (((fieldError s degree).error.val : ℚ) : ℝ) :=
  le_errorR (enclR_fieldError s degree) g

/-- The error of `Bound.ofWord 0` is not negative. -/
theorem zero_covers : (0 : ℝ) ≤ (((Bound.ofWord 0).error.val : ℚ) : ℝ) := by
  exact_mod_cast Binary.val_nonneg _

end OnBytes.Params

#print axioms OnBytes.Params.covered_append
#print axioms OnBytes.Params.field_covers
#print axioms OnBytes.Params.zero_covers
#print axioms OnBytes.Params.fold_covered
#print axioms OnBytes.Params.switch_covered
