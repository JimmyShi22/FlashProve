-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendPlan.lean: THEOREMS. **What a yes of the key file's fold pays, on the plan's side, toward the law of a sending (send_goodIn) at the first chain's sendings.**
  lengths_of_ok      the public tests' clause «lengths»: every message length of the one-time chain's codes is a power of two
  send_plan_of_yes   from a yes of Key.descriptionFromSource X N P: that clause, at the very codes that K1's numbers carry at every place of the chain (sendingPar … .codes), and: every block of the first chain has passed its own test on the plan
What is not claimed. The law's other premises. Nothing on soundness.

-/
import Johnson.RunOne.KeyPayD

set_option autoImplicit false

namespace Johnson.RunOne.KeyPay

open OnBytes OnBytes.Params VerifiableInference.Desc.Key
open VerifiableInference.Desc (FileDescription)

theorem lengths_of_ok {Y : KeySource} (h : sourceOk Y = true) : Y.k.oneTime.codes.lengthsOk = true :=
  clause_of_ok h (n := "lengths") (b := Y.k.oneTime.codes.lengthsOk) (by simp [sourceClauses])

theorem send_plan_of_yes {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {x : Xi} {v₁ v₂ v₃ : Fmt.View} (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) :
    (∀ piece what msg groups, (sendingPar X.Y.k.oneTime piece what msg groups).codes.lengthsOk = true) ∧ ∀ b ∈ (descriptionFromSource X N P).first.blocksInOrder, b.planOk = true := by
  obtain ⟨p, q⟩ := paid hy
  exact ⟨fun _ _ _ _ => lengths_of_ok q.file.ok, fun b hb => (p.blocks₁ b hb).1⟩

end Johnson.RunOne.KeyPay

#print axioms Johnson.RunOne.KeyPay.lengths_of_ok
#print axioms Johnson.RunOne.KeyPay.send_plan_of_yes
