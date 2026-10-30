-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/RunsHand.lean: kind K5: the kind's three runs of forms, taken AS RUNS OF
CLAIMS (runOfForms, Johnson/Desc/First/Batch/ClaimsAtS.lean): a yes hands the record back as it is, and
its claims are the plain claims of the forms that the run of forms returns at that record.

Main name: runOfForms_hands. It is runsK_step (Claims/RunsStep.lean: the three runs return the very
record; general in the seat) read through runOfForms' text. No new argument.
For whom: a law on one run of claims that asks "a yes hands the record back".
IS IT EMPTY HERE? Where a run refuses it says nothing. That a run returns is not shown here.
Limits. THE FOURTH RUN of the kind's list at the first chain's record, the lookup's "join", IS NOT AMONG
  THE THREE: nothing is said of it here. (What lies: joinRun_step, Claims/RunsStep.lean: the record is
  handed back as it is, or with the join's debt marked as paid in the ledger.) Nothing on which forms
  the runs return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.RunsStep
import Johnson.Desc.First.Batch.ClaimsAtS

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S Claim)
open VerifiableInference.Desc.K9 (runOfForms ofForm)
open VerifiableInference.Desc.First.Att

/-- **A yes of one of the three runs, as a run of claims.** -/
theorem runOfForms_hands (seat : P.SeatC First.S) (c : P.ParC) :
    ∀ r ∈ P.runsK seat c, ∀ (n : ℕ) (e : First.S) (cl : List Claim) (e₁ : First.S),
      (runOfForms r).2 n e = .ok (cl, e₁) →
        e₁ = e ∧ ∃ l, r.2 n e = .ok (l, e) ∧ cl = l.map fun f => ({ form := f } : Claim) := by
  intro r hr n e cl e₁ h
  unfold runOfForms at h
  cases hx : r.2 n e with
  | error m => simp only [hx] at h; cases h
  | ok y =>
    simp only [hx] at h
    have h' : (y.1.map ofForm, y.2) = (cl, e₁) := Except.ok.inj h
    obtain ⟨a1, a2⟩ := Prod.mk.inj h'
    have e2 : y.2 = e := runsK_step seat c r hr n e y.1 y.2 hx
    refine ⟨a2.symm.trans e2, y.1, ?_, a1.symm⟩
    rw [← e2]

end K5Law

#print axioms K5Law.runOfForms_hands
