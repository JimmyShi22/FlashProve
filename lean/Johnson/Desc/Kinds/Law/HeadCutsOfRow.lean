-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/HeadCutsOfRow.lean: THE FIELD head_cuts AT THE COMPOSED MEANING's CONSTANT
FROM THE CONSTANT's HEAD AND THE ROW madeRow AS A VERIFIER's LIST OF TESTS WRITES IT (not
at the full size's key, or the row). One theorem: two calls.

  headCuts_of_row    Law/HeadCutsOfPin.lean's headCuts_of_pin, its premise had by
                     pinnedAt_of_row (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean).

WHAT IT IS NOT. An implication. THE HEAD h IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). THE ROW STAYS A
PREMISE: that a verifier's list holds it, in this form, is not said here. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.HeadCutsOfPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey pinnedAt_of_row)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **"HEAD CUTS" AT THE CONSTANT, FROM ITS HEAD AND THE ROW.** -/
theorem headCuts_of_row {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D r Zp Np cF x)
    (hr : (!Decidable.decide (keyOfScan Zp.p.X.P = fullKey) || madeRow Zp) = true) :
    P5J.HeadCuts (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) OnBytes.Flat.putReq h.𝔇.H
      h.𝔇.headPart :=
  headCuts_of_pin h (pinnedAt_of_row hr)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headCuts_of_row
