-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SitsAt.lean: "W sits as the plan says" at the first chain's record: one test
with code on the record against the plan, and what its yes gives. A definition, and statements with
their proofs.
Main names:
  `wSitsL cs P s`: named tests with code, for a print: the record has what the block behind W's
    commitment leaves (`evalLaidB`, Johnson/Desc/K13/Law/Bools.lean); the reader `laidOf` gives a
    record of (Eval); and the five of `sitsL` (Johnson/Desc/K13/Law/Sits.lean) at it. `wSitsB`: all
    of them.
  `wSitsB_gives`: **a yes gives**: the reader's record, its three public facts, that its statement
    is the record's, and the five facts.
  `wSitsB_none`: a try: where no claim lies the test says no.

What is not claimed. That a run's record passes the test: a run can show it. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.LaidAt
import Johnson.Desc.K13.Law.Sits
import Johnson.Desc.K13.Law.Bools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S)

/-- Named tests with code. -/
def wSitsL (cs : Codes) (P : Where) (s : S) : List (String × Bool) :=
  ("the record has what the block behind W's commitment leaves", evalLaidB P s) ::
    match laidOf P s with
    | some D => ("the reader gives a record of (Eval)", true) :: sitsL cs P.lin D
    | none => [("the reader gives a record of (Eval)", false)]

/-- All of them. -/
def wSitsB (cs : Codes) (P : Where) (s : S) : Bool := (wSitsL cs P s).all (·.2)

/-- **What a yes gives.** -/
theorem wSitsB_gives {cs : Codes} {P : Where} {s : S} (h : wSitsB cs P s = true) :
    ∃ D, laidOf P s = some D ∧ D.Ok P.lin ∧ D.st = s.st ∧ SitsPlain cs P.lin D := by
  unfold wSitsB wSitsL at h
  rw [List.all_cons, Bool.and_eq_true] at h
  obtain ⟨D, hD, hok, _, hst, _⟩ := laidOf_ok ((evalLaidB_iff P s).1 h.1)
  refine ⟨D, hD, hok, hst, (sitsB_iff cs P.lin D).1 ?_⟩
  have h2 := h.2
  rw [hD, List.all_cons, Bool.and_eq_true] at h2
  exact h2.2

/-- **A try**: where no claim lies the test says no. -/
theorem wSitsB_none {cs : Codes} {P : Where} {s : S} (h : linAt s = none) :
    wSitsB cs P s = false := by
  unfold wSitsB wSitsL evalLaidB
  rw [h]
  rfl

end VerifiableInference.Desc.K13.Law
