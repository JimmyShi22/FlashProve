-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/PlanValues/KeyFullAtScope.lean: at every three public files in the scope of the goals,
the sizes of the key file's blocks in what the program computes are the one typed value keyFull
(Johnson/Goal/PlanValues/KeySizedReturns.lean); also in the record that Johnson.G.OfPlan.madeOf
makes of the three files.

Johnson/Goal/PlanValues/ScopeAtPlan.lean: at every file in scope the key's sizes are what
Plan.keySized returns at the written lines and the layout of the written sizes.
KeySizedReturns.lean: there it returns keyFull. So the two are equal. Johnson.G.OfPlan.madeOf
(Johnson/G/RoundsOfPlan.lean) begins with a call of Model.Verify.planned on the same three files and
keeps what that returns.

Main names.
  key_eq_at_scope    planned Z.pol Z.KL (some Z.lay) = .ok p gives
                     p.chains.made.sized.key = keyFull.
  madeOf_planned     madeOf pol lay KL = .ok m gives planned pol KL (some lay) = .ok m.p.
  made_eq_at_scope   madeOf Z.pol Z.lay Z.KL = .ok m gives m.p.chains.made.sized.key = keyFull.

Limits. One direction: from a program that returns: that Model.Verify.planned or madeOf returns at
any file is not shown. Of what is read back from a chain's parameter bytes (p.chains.key) nothing is
said here. Nothing on soundness.
-/
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params

/-- **At every three public files in scope the key's sizes are the typed value.** -/
theorem key_eq_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.key = keyFull := by
  obtain ⟨Y, sh, hY, hs, hz⟩ := key_at_scope hZ hp
  exact Option.some.inj (hz.symm.trans (keySized_returns hY hs))

/-- What madeOf returns holds what the program's planner returns on the same three files. -/
theorem madeOf_planned {pol lay KL : ByteArray} {m : Johnson.G.OfPlan.Made}
    (h : Johnson.G.OfPlan.madeOf pol lay KL = .ok m) :
    Model.Verify.planned pol KL (some lay) = .ok m.p := by
  unfold Johnson.G.OfPlan.madeOf at h
  obtain ⟨p, hp, h⟩ := exc_bind h
  obtain ⟨l, _, h⟩ := exc_bind h
  split at h
  · cases h
    exact hp
  · cases h

/-- So in that record too the key's sizes are the typed value, at every file in scope. -/
theorem made_eq_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL = .ok m) :
    m.p.chains.made.sized.key = keyFull :=
  key_eq_at_scope hZ (madeOf_planned h)

end Lk6.AtPlan

#print axioms Lk6.AtPlan.key_eq_at_scope
#print axioms Lk6.AtPlan.madeOf_planned
#print axioms Lk6.AtPlan.made_eq_at_scope
