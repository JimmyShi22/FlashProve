-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/RunsDefs.lean: a list written as distinct values and runs, and the walk that compares a
list of rounds with their error bounds, as the planner makes it, against such a written list.
Definitions alone, so that the file can stand beneath a verifier's list of tests
and be read by itself.
What they give is proved in Johnson/G/Runs.lean and
Johnson/Desc/Ok/NumberPrices/ByRuns.lean.

Definitions.
  `unrunG vals runs`: the list that is written: each run (how often, which of the distinct values)
    laid out.
  `valRuns vals runs`: the runs with each index replaced by its value.
  `sameBy r k A B`: one walk along two lists of runs: r says yes of the two values at every place,
    and the lists end together; k bounds the steps. The written side is never laid out.
  `Lit`: a written list of rounds with error bounds: a setting, the distinct rounds, the runs.
    `Lit.plan`: the list that it writes.
  `sameRound a b`: the seven fields of two rounds are the same: the entry, the error bound, the
    group from which it was priced, the kind of argument, the footing of a count, who pays for the
    proof of work, the mark of a fault.
  `rideB k P L`: P has L's setting, and one walk finds L's rounds in P's, field by field.

Limits. Nothing is proved here. `sameBy` can say no where the lists are the same: at a run of 0
members, or where k is too small.
-/
import OnBytes.Params.Planner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.Runs

variable {α β : Type}

/-- The list of a list of runs: how often, which of the distinct values. -/
def unrunG (recs : List α) (runs : List (Nat × Nat)) : List α :=
  runs.flatMap fun x => (recs[x.2]?).elim [] (List.replicate x.1)

/-- The runs with each index replaced by its value. -/
def valRuns (recs : List α) : List (Nat × Nat) → List (Nat × α)
  | [] => []
  | x :: xs => (recs[x.2]?).elim (valRuns recs xs) fun r => (x.1, r) :: valRuns recs xs

/-- One walk along two lists of runs: r says yes of the two values at every place, and the lists end
together. k bounds the steps. -/
def sameBy (r : α → β → Bool) : Nat → List (Nat × α) → List (Nat × β) → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | _ + 1, [], _ :: _ => false
  | _ + 1, _ :: _, [] => false
  | k + 1, x :: xs, y :: ys =>
    if r x.2 y.2 = true then
      if x.1 = y.1 then sameBy r k xs ys
      else if x.1 < y.1 then sameBy r k xs ((y.1 - x.1, y.2) :: ys)
      else sameBy r k ((x.1 - y.1, x.2) :: xs) ys
    else false

end Johnson.G.Runs

namespace VerifiableInference.Number.ByRuns
open OnBytes.Params Johnson.G.Runs

/-- A written list of rounds with error bounds: a setting, the distinct rounds, the runs. -/
structure Lit where
  set : Setting
  recs : List PlanRound
  runs : List (Nat × Nat)

/-- The list that it writes. -/
def Lit.plan (L : Lit) : Planned := ⟨L.set, unrunG L.recs L.runs⟩

/-- The seven fields of two rounds are the same. -/
def sameRound (a b : PlanRound) : Bool :=
  decide (a.entry = b.entry) && decide (a.error = b.error) && decide (a.group = b.group) &&
    decide (a.why = b.why) && decide (a.rests = b.rests) && decide (a.scope = b.scope) &&
    decide (a.wordFault = b.wordFault)

/-- P has L's setting, and one walk finds L's rounds in P's, field by field. -/
def rideB (k : Nat) (P : Planned) (L : Lit) : Bool :=
  decide (P.set = L.set) &&
    sameBy sameRound k (P.rounds.map fun r => (1, r)) (valRuns L.recs L.runs)

end VerifiableInference.Number.ByRuns
