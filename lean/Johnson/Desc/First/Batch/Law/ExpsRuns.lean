-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ExpsRuns.lean
(kind K9's soundness lemma; toward hok): THEOREM: THE DISCIPLINE ON THE EXPONENTS
(Law/ExpsOk.lean) OF A STEP OF ADDING, FROM THE DISCIPLINE OF EACH RUN OF ITS GATHERING.
A step's terms are its runs' terms in a row (Law/Gather.lean: termsRuns). So the step's two clauses
(its exponents differ from each other; they lie in its window of numbers or in its window of
equations) follow from the like of each run, the runs' windows laid end to end.
  asMove          a run with its terms, read as a move with the same terms (a device of the proof).
  termsRuns_eq, lenRuns_eq   the runs' terms and number are those moves'.
  disc_gather     **the step's two clauses, from DiscFrom of its runs.**
Not claimed: the discipline of any real run.

-/
import Johnson.Desc.First.Batch.Law.Gather
import Johnson.Desc.First.Batch.Law.ExpsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model

variable {T P K : Type}

/-- A run with its terms, read as a move with the same terms. -/
def asMove (r : TermedRun T P K) : Termed T P K := ⟨.quiet .ok, r.tm, r.len⟩

theorem termsRuns_eq (p : P) (y : Bound K) : ∀ (rl : List (TermedRun T P K)) (n : ℕ),
    termsRuns p y rl n = termsOf p y (rl.map asMove) n
  | [], _ => rfl
  | r :: l, n => by
    simp only [termsRuns, List.map_cons, termsOf, termsRuns_eq p y l]
    rfl

theorem lenRuns_eq (p : P) : ∀ (rl : List (TermedRun T P K × ℕ)),
    lenRuns p (rl.map (·.1)) = lenAll p (rl.map fun r => (asMove r.1, r.2))
  | [] => rfl
  | r :: l => by
    simp only [List.map_cons, lenRuns, lenAll, lenRuns_eq p l]
    rfl

/-- **The step's two clauses, from the discipline of its runs.** -/
theorem disc_gather (p : P) (y : Bound K) (plan : ℕ) (rl : List (TermedRun T P K × ℕ)) (n t : ℕ)
    (h : DiscFrom p y plan (rl.map fun r => (asMove r.1, r.2)) n t)
    (hp : n + lenRuns p (rl.map (·.1)) ≤ plan) :
    ((termsRuns p y (rl.map (·.1)) n).map (·.1)).Nodup ∧
      ∀ x ∈ termsRuns p y (rl.map (·.1)) n,
        InWin n (lenRuns p (rl.map (·.1))) plan t
          (tieAll (rl.map fun r => (asMove r.1, r.2))) x.1 := by
  have e : termsRuns p y (rl.map (·.1)) n =
      termsOf p y ((rl.map fun r => (asMove r.1, r.2)).map (·.1)) n := by
    rw [termsRuns_eq, List.map_map, List.map_map]
    rfl
  rw [e, lenRuns_eq]
  exact disc_terms p y plan _ n t h (by rw [← lenRuns_eq]; exact hp)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.disc_gather
