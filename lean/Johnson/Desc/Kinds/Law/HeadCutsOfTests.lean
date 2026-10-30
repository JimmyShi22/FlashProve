-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/HeadCutsOfTests.lean: THE FIELD head_cuts AT THE COMPOSED MEANING's
CONSTANT (Law/HeadCutsAtAll.lean: headCuts_atAll) FROM THE CONSTANT's HEAD AND TWO TESTS WITH CODE
ON PUBLIC DATA. One theorem: two calls.

  headCuts_of_tests   the premise on the pads is paid by Law/PadsFreeAtAll.lean
                   (OffPad.padsFree_atAll) from its test padsAtZ Zp (Kinds/HeadDoorAtZ.lean).

WHAT IT IS NOT. An implication. THE HEAD h IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). THE TWO TESTS:
each has been evaluated at the full-size stored public files on a sheet
(not here): evaluations, no theorems. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsAtAll
import Johnson.Desc.Kinds.Law.PadsFreeAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **"HEAD CUTS" AT THE CONSTANT, FROM ITS HEAD AND TWO TESTS WITH CODE.** -/
theorem headCuts_of_tests {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D r Zp Np cF x)
    (htab : tabIsEXB (P5J.At.tabH x) = true) (hp : OffPad.padsAtZ Zp = true) :
    P5J.HeadCuts (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) OnBytes.Flat.putReq h.𝔇.H
      h.𝔇.headPart :=
  headCuts_atAll h htab (OffPad.padsFree_atAll h.toAtMg hp)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headCuts_of_tests
