-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/CoefficientsAll.lean: THE WEIGHTS' STEP LEAVES THE LIBRARY's coefAll: a yes of the plain step
coefficientsP (Coefficients.lean), and so of the three steps behind the adding as one (testsP, SelfRows.lean),
returns the ledger that the laws on the lookup's ends name coefAll tl g F
(OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean: there «the state behind the routine»).

Statements and proofs. No routine of `verify-on-bytes` is named. USED OF THE FILES UNDER OnBytes/, ON RECORDS AND PLAIN
DATA ALONE: coefAll (a plain function of a record, what the lookup heard and a ledger); excBind_ok through tests_ok.
Main names:
  coefBody_all: coefBody tl g F = coefAll tl g F (rfl: the two texts unfold to one term).
  coef_all: coefficientsP tl F = .ok Fc gives what was heard, g, and Fc = coefAll tl g F.
  tests_all: the same from testsP nU tl F = .ok Fc.
Limits: from a yes alone.

-/
import Johnson.Desc.First.TailClaims.EquationsTests
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc.First.TailClaims

theorem coefBody_all (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    coefBody tl g F = Fo.coefAll tl g F := rfl

/-- **A yes of the weights' step returns coefAll.** -/
theorem coef_all {tl : HTailF2} {F Fc : Fork} (h : coefficientsP tl F = .ok Fc) :
    ∃ g, tl.heard = some g ∧ Fc = Fo.coefAll tl g F := by
  unfold coefficientsP at h
  cases hg : tl.heard with
  | none => rw [hg] at h; exact nomatch h
  | some g =>
    rw [hg] at h
    exact ⟨g, rfl, (Except.ok.inj h).symm.trans (coefBody_all tl g F)⟩

/-- **So does a yes of the three steps as one.** -/
theorem tests_all {nU : Array Nat} {tl : HTailF2} {F Fc : Fork} (h : testsP nU tl F = .ok Fc) :
    ∃ g, tl.heard = some g ∧ Fc = Fo.coefAll tl g F := coef_all (tests_ok h).2.1

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.coefBody_all
#print axioms VerifiableInference.Desc.First.TailClaims.Law.tests_all
