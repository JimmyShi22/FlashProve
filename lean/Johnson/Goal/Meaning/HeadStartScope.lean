-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadStartScope.lean: at all public files in the goals' scope, the test on the
request under which the first chain's first record is made gives the test on the request that the
law on the output head's own rounds asks.

What the file holds. X: what publicOf returns on public files in scope.
  V_public         X.P.h.V = X.hS.V, wherever publicOf returns.
  T_in_scope       X.T = 2 ^ X.hS.lt: the number of a request's tokens, as the layers' layout has
                   it, is the head's.
  start_in_scope   where S.reqOk X.T X.P.h.V says yes at a record s0, and a later record s has the
                   field req of s0: the kind's test on the request (Par.okStart) says yes at the
                   request that the head's seat reads off s.
Why. Johnson/Desc/Kinds/Law/StartPays.lean shows this at the numbers 2 ^ h.lt and h.V. A description
makes its first record under S.reqOk at the public part's own X.T and X.P.h.V. Here the two pairs of
numbers are tied.

What it does not give. Nothing on soundness. That a given description makes its first record under
that test, and that its blocks leave the field req up to the head's own rounds: both are premises.
That any files meet the premises on Z: see the head of HeadCondScope.lean.

-/
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.Desc.Kinds.Law.StartPays

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)
open VerifiableInference.Desc.First (S)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

theorem V_public {pol KL : ByteArray} (h : publicOf pol KL lay = .ok X) : X.P.h.V = X.hS.V := by
  rw [Meaning.HeadS.headShape_of_public h]
  rfl

theorem T_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.T = 2 ^ X.hS.lt := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  obtain ⟨e, -⟩ := OnBytes.Road.laid_of_layout B.lay B.switches.p3
  have L2 := OnBytes.Road.laid2_of_layout B.lay
  show X.y.T = 2 ^ X.hS.lt
  rw [L2.T, e, Meaning.HeadS.headShape_of_public h]
  rfl

/-- **The first record's test on the request pays the law's clause on the request.** -/
theorem start_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (w iU3 : Nat) (s0 s : S)
    (hq : s0.reqOk X.T X.P.h.V = true) (hr : s.req = s0.req) :
    (parOf X.hS w).okStart ((seatAt X.hS iU3).request s) = true := by
  rw [T_in_scope hZ hR h, V_public h] at hq
  exact StartPays.start_pays X.hS w iU3 s0 s hq hr

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.T_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.start_in_scope
