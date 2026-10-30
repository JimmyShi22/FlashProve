-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/UnitsInScope.lean: THE
UNITS OF ROWS THAT THE KEY FILE'S DESCRIPTION READS ARE THE WRITTEN LAYOUT'S, IN SCOPE, AT ANY
DIGEST. The source's ninth part (units: what the clause "weights" of the test on the file reads,
Johnson/Desc/Key/Source.lean) is made of the layout of the committed matrix in what was read of the
public files (sourceOf, Johnson/Desc/Key/Desc.lean). At every parameter file in the goals' scope
that layout is what wsLayOf returns at the ten written sizes.

Main names (wsLay_at_policy, sourceOf_units and units_in_scope have moved, under their full names,
to KeyInScope.lean):
  units_at_o: units_in_scope from the yes of
    (publicOfO o pol KL (some lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z lay.

Object: Key.sourceOf's ninth part, through Key.madeAt.
User: none yet (units_in_scope: all_in_scope, AllAtO.lean).
Letters: Zp: three public files in scope · Z under ReadOf Zp.pol Z · cfg: any digest · o: any
function in the hash function's place.

Limits. The layout FILE's bytes are not spoken of: nothing here ties them to this layout. One size.
One direction: from routines that return. Nothing on soundness.

-/
import Johnson.RunOne.Law.ReadAtO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.UnitsInScope
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines)
open Lk6.AtPlan
open VerifiableInference.PlanWritten (publicOfO)
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (Source madeAt sourceOf keyDataAndDecisionAtFixedDigest KeyRun)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.ReadAtO

/-- **The same at every letter o.** -/
theorem units_at_o {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {o : Nat → ByteArray → ByteArray} {D : OnBytes.Maker.WholeD} {r : KeyRun}
    (h : ((publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z Zp.lay) =
      .ok (D, r)) :
    ∃ X N P Y, (FK X N P).planOk = true ∧ (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ wsLayOf wsFull true recordLines.blockLog = .ok Y ∧
      X.Y.units = Plan.unitsOfLayout Y := by
  obtain ⟨Z, hP, hl⟩ := exc_bind h
  obtain ⟨m, X, N, P, hm, hX, hp, hD, hr⟩ := Johnson.RunOne.Law.KeyInScope.laid_parts hl
  obtain ⟨Y, h1, h2⟩ := units_in_scope hZ (readOf_publicOfO hP) hm hX
  exact ⟨X, N, P, Y, hp, hD, hr, h1, h2⟩

end Johnson.RunOne.Law.UnitsInScope

#print axioms Johnson.RunOne.Law.UnitsInScope.units_at_o
