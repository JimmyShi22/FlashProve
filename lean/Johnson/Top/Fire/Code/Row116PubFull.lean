-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116PubFull.lean: THE KEY FILE's ROW 1.16: ITS TWO PUBLIC PREMISES (at most noId stages · PubPile) AS CLOSED FACTS BY THE KERNEL AT THE WRITTEN KEY (Lk6.AtPlan.keyFull), and the joint to the source's letters: so that IN THE GOALS' SCOPE they are theorems, not tests (on a decision in this project).
  pubPileB lin lookups   PubPile as a plain test on the shape and the lookups
  pubPile_of_B           its yes gives PubPile
  stages_full · pile_full   BY THE KERNEL at keyFull
  pile_plant             A PLANT: at keyFull's lookups with the first run of the first part of the first lookup one place longer than its part: the test says no
  pub_of_full            FROM «the source's ranges and shape are keyFull's» (one_full, KeyPublicAtSeat.lean, gives both in scope, by key_at_chains · five_at, Johnson/RunOne/Law/KeyInScope.lean): the two premises of r1_16_whole
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyClaimFacts
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

def pubPileB (lin : LinShape) (lookups : List WfLookup) : Bool :=
  decide ((Wf.matrixOf lin).kRow ≤ 63) && lookups.all fun L => L.parts.all fun p => p.runs.all fun r => decide (r.firstPlace + r.places ≤ 2 ^ p.logPlaces)

theorem pubPile_of_B (one : OneTime) (h : pubPileB one.lin one.ranges.lookups = true) : PubPile one := by
  unfold pubPileB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem stages_full : keyFull.ranges.x.stages.length ≤ noId := by decide +kernel

theorem pile_full : pubPileB keyFull.once.shape keyFull.ranges.x.lookups = true := by decide +kernel

/-- The first run of the first part of the first lookup, made as long as its part and one place more. -/
def bentRuns (l : List WfLookup) : List WfLookup :=
  match l with
  | L :: t => { L with parts := match L.parts with
      | p :: ps => { p with runs := match p.runs with
          | r :: rs => { r with places := 2 ^ p.logPlaces + 1 } :: rs
          | [] => [] } :: ps
      | [] => [] } :: t
  | [] => []

theorem pile_plant : pubPileB keyFull.once.shape (bentRuns keyFull.ranges.x.lookups) = false := by decide +kernel

theorem pub_of_full (one : OneTime) (h1 : one.ranges = keyFull.ranges.x) (h2 : one.lin = keyFull.once.shape) :
    one.ranges.stages.length ≤ noId ∧ PubPile one := by
  refine ⟨by rw [h1]; exact stages_full, pubPile_of_B one ?_⟩
  rw [h1, h2]
  exact pile_full

end LPFD

#print axioms LPFD.stages_full
#print axioms LPFD.pile_full
#print axioms LPFD.pile_plant
#print axioms LPFD.pub_of_full
