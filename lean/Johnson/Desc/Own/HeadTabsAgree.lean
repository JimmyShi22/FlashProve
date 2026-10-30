-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/HeadTabsAgree.lean: the description's five own makers for the head's list of tables
(Johnson/Desc/Own/HeadTabs.lean) say just what the hand-written program's cutLast, lastOf
(OnBytes/Model/Tensors.lean), Head.callNo (OnBytes/Model/HeadHeard.lean), Forest.phiB
(OnBytes/Model/Look.lean) and Head.addFun (OnBytes/Model/HeadTables.lean) say, at all arguments. Of
the first two, which refuse under a name: but for that name.
A YARDSTICK BESIDE: no block imports this file. It says nothing on whether the makers refuse enough.
No soundness is claimed.

-/
import Johnson.Desc.Own.HeadTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Model

theorem cutTail_agrees (z : Array E) (k : Nat) : (cutLast z k).toOption = cutTail z k := by
  unfold cutLast cutTail
  split <;> rfl

theorem tailOf_agrees (z : Array E) (k : Nat) : (lastOf z k).toOption = tailOf z k := by
  unfold lastOf tailOf cutLast cutTail
  split <;> rfl

theorem callWith_agrees (L : Head.HL) (seg : String) : Head.callNo L seg = callWith L seg := rfl

theorem planeWeights_agrees (g : Forest.Heard) (lm e : Nat) :
    Forest.phiB g lm e = planeWeights g lm e := by
  unfold Forest.phiB planeWeights Forest.planeCols Forest.Heard.zb
  dsimp only
  by_cases c : (lm < 5 || lm > g.shape.kT + 5) = true
  · rw [if_pos c, if_pos c]
    rfl
  · rw [if_neg c, if_neg c]
    rfl

theorem tableAdded_agrees (mats : Array TMat) (t : Head.Tables) (M0 parts Lf : Nat) (phi : Array E)
    (nm : String) : Head.addFun mats t M0 parts Lf phi nm = tableAdded mats t M0 parts Lf phi nm :=
  rfl

end VerifiableInference.Desc.Own
