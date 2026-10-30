-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/HeadCutsOfPads.lean: THE FIELD head_cuts AT THE COMPOSED MEANING's
CONSTANT FROM THE CONSTANT's HEAD AND ONE TEST WITH CODE ON PUBLIC DATA. One theorem: two calls.

  headCuts_of_pads   Law/HeadCutsOfTests.lean's headCuts_of_tests with its premise on the table of
                     the exponential's lookup (tabIsEXB (P5J.At.tabH x) = true) paid by
                     Law/TabIsEXInScope.lean's tabIsEX_in_scope, off four fields of the head: scope,
                     reads, pubOne, headAt. P5J.At.tabH x is tabOf (rowH x) by its definition.

WHAT IT IS NOT. An implication. THE HEAD h IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). THE TEST
padsAtZ Zp STAYS A PREMISE. The second hash function o is a letter: the head's field pubOne speaks
of the library's publicOf at every o. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.HeadCutsOfTests
import Johnson.Desc.Kinds.Law.TabIsEXInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **"HEAD CUTS" AT THE CONSTANT, FROM ITS HEAD AND ONE TEST WITH CODE.** -/
theorem headCuts_of_pads {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D r Zp Np cF x)
    (hp : OffPad.padsAtZ Zp = true) :
    P5J.HeadCuts (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) OnBytes.Flat.putReq h.𝔇.H
      h.𝔇.headPart :=
  headCuts_of_tests h (InScope.tabIsEX_in_scope h.scope h.reads h.pubOne h.headAt) hp

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headCuts_of_pads
