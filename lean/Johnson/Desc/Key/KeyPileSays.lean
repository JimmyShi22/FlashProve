-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyPileSays.lean: THE KEY FILE's ROW 1.16: layPile's yes WITH THE MAKING OF ITS ROWS HANDED OUT.
KeyPend's (Johnson/RunOne/KeyPend.lean) mapM_get · mapM_if | mapM_if_all · pendingAt_is | pendingAt_ok · pend_law are called.
  layPile_whole   WHAT KeyPend.pend_law DOES NOT HAND OUT: the equation of the making itself: (lookups.zip keys).mapM (tableRowsOf m · ·) = some rowss: so that a law on tableRowsOf's yes (KeyPend.pendingAt_ok) can be called at each list
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyBattSays
import Johnson.RunOne.KeyPend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.K13 (pure_ok)

variable {β : Type}

theorem layPile_whole (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (s t : ChainState β) (h : layPile keysOf one s = .ok t) :
    ∃ rowss, one.ranges.lookups.length = (keysOf s.base).length ∧
      ((one.ranges.lookups.zip (keysOf s.base)).mapM fun x => tableRowsOf (Wf.matrixOf one.lin) x.1 x.2) = some rowss ∧ t = { s with pile := rowss.flatten } := by
  unfold layPile at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, h2, h⟩ := bind_ok h
  obtain ⟨rows, h3, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have e3 := Johnson.RunOne.KeyRows1.namedX h3
  rw [zipT_eq] at e3
  exact ⟨rows, beq_iff_eq.1 (Johnson.RunOne.KeyRows1.needX h2), e3, (pure_ok h).symm⟩

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.layPile_whole
