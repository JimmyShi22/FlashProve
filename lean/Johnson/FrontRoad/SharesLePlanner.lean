-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SharesLePlanner.lean: arithmetic on written shares; no event; no prover. Where the
planner's test on range checks passes at the checks of a list of places of the smallness test
(missedInTheChecks returns false), the shares that the honest parts at these places state for their
private abort test (windowShare) add up to at most the planner's bound (shares_le_planner).
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  shares_le_planner   Ps is a list of places' numbers (Par, Johnson/Desc/First/K8/Hear.lean). The
      planner's bound is 2 ^ −(sec + the rounded-up logarithms of the slots, the batches and the
      copies), as in sum_le_planner (Johnson/FrontRoad/SumLePlanner.lean).
  matricesOf, checksOfPars   a place's matrices as (rows, columns, combinations); the range checks
      of a list of places, one for each matrix, with the verifier's constants (checkOf,
      Johnson/FrontRoad/SumLePlanner.lean). matricesOf lays the list of rows beside the list of
      columns and cuts the longer, as windowShare does.
  windowBits_eq_natBits, windowShare_val   the count of bits in a stated share (windowBits,
      Johnson/Desc/ProofFile/Honest/K8/Part.lean) is natBits, by definition; so a place's stated
      share has the value of the sum, over its matrices, of 1 / 2 ^ natBits (by oddsValue_foldl,
      Johnson/Desc/ProofFile/Honest/K8/ShareLaw.lean).

How it fits. A chain's bound on the honest prover's private aborts adds up the shares that the parts
state (sharesSum, Johnson/FrontRoad/SessionStopsOfHeld.lean). This file bounds the sum of
windowShare over a list of places by the planner's bound, where the planner's public test passes;
the tie to sharesSum is sharesSum_of_pinned (Johnson/FrontRoad/SessionStopsPinned.lean), under its
premise on the rows. At the verifier's constants windowBits and the planner's rangeCheckBits
(OnBytes/Params/Gate.lean) have the same quotient (rangeQuot_checkOf), and windowBits is at least
the planner's number wherever the planner returns one (natBits_ge). Words (member, half, part,
public and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Lemmas; not
one of the release's goal statements.

Limits.
  A stated share is a written number. This file bounds no probability. That the part's private abort
      test fires with probability at most the value of its stated share, over the uniform written
      verifier message of its one round, is small_stopDebt
      (Johnson/Desc/ProofFile/Honest/K8/WindowDebt.lean), at data that bear that round's entry and
      kind, under a premise on the cells that reads the hidden input.
  Ps, l, oneTime, columnsFirst and batches are free: tied to nothing here. That Ps are the places of
      any description, that a prover's rows have these parts, and that the checks are those that the
      verifier gives the planner are not proved here.
  The premise fails at the empty list: the planner's test is missed where no check is named.
  All limits of Johnson/FrontRoad/RangeCheckBits.lean and Johnson/FrontRoad/SumLePlanner.lean hold.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.SumLePlanner
import Johnson.Desc.ProofFile.Honest.K8.ShareLaw
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld

set_option autoImplicit false

namespace OnBytes.FrontRoad
open OnBytes.Params
open ProofFile.Honest (Odds)
open ProofFile.Honest.K8 (windowShare windowBits bitsFor oddsValue oddsValue_foldl)
open VerifiableInference.Desc.First.K8 (Par)
open scoped ENNReal

/-- The count of bits in a stated share is natBits: by definition. -/
theorem windowBits_eq_natBits (rows columns combinations : ℕ) :
    windowBits rows columns combinations = natBits rows columns combinations := rfl

/-- A place's matrices: rows, columns, combinations. -/
def matricesOf (p : Par) : List (ℕ × ℕ × ℕ) := (p.ms.zip p.ks).map fun x => (x.1, x.2, p.tau)

/-- The range checks of a list of places: one for each matrix. -/
def checksOfPars (Ps : List Par) : List RangeCheck :=
  (Ps.flatMap matricesOf).map fun x => checkOf x.1 x.2.1 x.2.2

/-- The value of a place's stated share: the sum over its matrices of 1 / 2 ^ natBits. -/
theorem windowShare_val (p : Par) :
    (windowShare p).val =
      ((matricesOf p).map fun x => ((2 : ℝ≥0∞) ^ natBits x.1 x.2.1 x.2.2)⁻¹).sum := by
  have h := (oddsValue_foldl p.tau (p.ms.zip p.ks) ⟨0, 1⟩ (by norm_num)).2
  have h01 : oddsValue ⟨0, 1⟩ = 0 := by simp [oddsValue]
  rw [h01, zero_add] at h
  unfold matricesOf
  rw [List.map_map]
  exact h

/-- Arithmetic on written shares; no event; no prover. **Where the planner's test passes at the
checks of a list of places, the shares that the parts at these places state add up to at most the
planner's bound.** -/
theorem shares_le_planner (l : Lines) (Ps : List Par) (oneTime columnsFirst batches : ℕ)
    (hm : missedInTheChecks l (checksOfPars Ps) oneTime columnsFirst batches = false) :
    (Ps.map fun p => (windowShare p).val).sum ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) + (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) := by
  have e : ∀ Qs : List Par, (Qs.map fun p => (windowShare p).val).sum =
      ((Qs.flatMap matricesOf).map fun x => ((2 : ℝ≥0∞) ^ natBits x.1 x.2.1 x.2.2)⁻¹).sum := by
    intro Qs
    induction Qs with
    | nil => rfl
    | cons p Qs ih =>
      rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, ih,
        windowShare_val]
  rw [e]
  exact sum_natBits_le_planner' l (Ps.flatMap matricesOf) oneTime columnsFirst batches hm

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.windowBits_eq_natBits
#print axioms OnBytes.FrontRoad.matricesOf
#print axioms OnBytes.FrontRoad.checksOfPars
#print axioms OnBytes.FrontRoad.windowShare_val
#print axioms OnBytes.FrontRoad.shares_le_planner
