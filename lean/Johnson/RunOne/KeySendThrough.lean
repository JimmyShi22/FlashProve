-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendThrough.lean: THEOREMS. **What a block brings to the law of a sending passes to every block that holds it**: a block b' at a wider record whose yes at two rounds holds a yes of b, at these two rounds and
some opened columns, at a projection of the record (a lift, a block held beside an instance, a block laid below another).
  isSend_through   IsSend P stOf b ⇒ IsSend P (stOf ∘ π) b'
  pays_through     the same of Pays
What is not claimed. That a given frame's wrapper is such a block: that is one law on that wrapper's decide. Nothing on soundness.

-/
import Johnson.RunOne.KeySendGood

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (Par IsSend)

variable {T T' Cl Cl' : Type}

theorem isSend_through (P : Par) (stOf : T → Statement) (b : Block T Cl) (b' : Block T' Cl') (π : T' → T)
    (h : ∀ s s' r₁ r₂ gs, b'.decide s [r₁, r₂] gs = .ok s' → ∃ gs', b.decide (π s) [r₁, r₂] gs' = .ok (π s')) (hS : IsSend P stOf b) : IsSend P (fun t => stOf (π t)) b' :=
  fun s s' r₁ r₂ gs hy => (h s s' r₁ r₂ gs hy).elim fun gs' hy' => hS (π s) (π s') r₁ r₂ gs' hy'

theorem pays_through (P : Par) (stOf : T → Statement) (b : Block T Cl) (b' : Block T' Cl') (π : T' → T)
    (h : ∀ s s' r₁ r₂ gs, b'.decide s [r₁, r₂] gs = .ok s' → ∃ gs', b.decide (π s) [r₁, r₂] gs' = .ok (π s')) (hb : Pays P stOf b) : Pays P (fun t => stOf (π t)) b' :=
  ⟨hb.plan, isSend_through P stOf b b' π h hb.send⟩

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.isSend_through
#print axioms Johnson.RunOne.KeySendGood.pays_through
