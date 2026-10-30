-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WalkDigits.lean: kind K5: the step without a round that the lookup's kind lays behind its block on the
smallness test's digits, at an attention link (K3.quietDigits, Johnson/Desc/First/Look/K3Whole.lean), carries the ledger and what
K5 heard (CarK5, Claims/WalkK5.lean): it lays the ledger with one number of the plan written in; the slots and what lies under
them do not turn.

Main names:
  quietDigits_carries: by the lookup's kind's own quietDigits_ok (Johnson/Desc/First/Look/K3QuietLaws.lean).
  seated7_steps: a block that carries, with that step laid behind it by Block.andThen (as K3.theWhole lays it), carries.
IS IT EMPTY HERE? Where the step refuses nothing is said.
Limits. That the lookup's block itself carries is a premise of seated7_steps: the lookup's files' law.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3QuietLaws
import Johnson.Desc.Sound.StepsThrough
import Johnson.Desc.First.Att.Claims.WalkK5

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S Block roundlessBlock stepsAndThen)

theorem quietDigits_carries (used claims : ℕ) {s t : First.S}
    (h : VerifiableInference.Desc.K3.quietDigits used claims s = .ok t) : CarK5 s t := by
  obtain ⟨F, hF, _, rfl⟩ := VerifiableInference.Desc.K3.quietDigits_ok used claims s t h
  refine carK5_putFork s _ fun F' hF' _ => ?_
  obtain rfl : F' = F := Option.some.inj (hF'.symm.trans hF)
  exact PscRun.SlotsSame.later ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The seated block at the digits**: the lookup's block with the quiet step behind it. -/
theorem seated7_steps {Cl : Type} (b : Block First.S Cl) (hb : b.Steps CarK5) (name name' : String) (link : Option ℕ)
    (piece used claims : ℕ) :
    (b.andThen name (roundlessBlock name' 1 link piece
      (VerifiableInference.Desc.K3.quietDigits used claims))).Steps CarK5 :=
  stepsAndThen carK5_pre name _ _ hb fun _ _ _ _ h => quietDigits_carries used claims h

end K5Law

#print axioms K5Law.quietDigits_carries
#print axioms K5Law.seated7_steps
