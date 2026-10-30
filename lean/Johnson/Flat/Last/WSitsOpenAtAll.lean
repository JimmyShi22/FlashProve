-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/WSitsOpenAtAll.lean: THE PUBLIC TEST "K13.wSits" IS OPEN AT THE FIRST TABLE's
LAST BORDER, AT THE CLOSED CONSTANT P5J.mgAtAll h (Johnson/P5J/MgAtAll.lean), in the spellings of
Johnson/P5J/ for the list of segments: the premise h3 of the tops on the shared chain and
on row 0 of the last table, at the closed constant. One theorem: a call.

  h3_atAll  wSits_open_mgAll (Johnson/Flat/Last/RowZeroAtMgAllFull.lean: the kernel, at the
            composed meaning's closed list of extra public tests) at 𝔇 := h.𝔇 and Mg := mgBase:
            mgAtAll h is mgAll h.𝔇 mgBase, mgBase's own list is empty, and At.links is the full
            list: all three by unfolding. NO PREMISE BUT THE HEAD h, of which nothing is spent but
            that it names the constant.
Nothing on soundness.

-/
import Johnson.Flat.Last.RowZeroAtMgAllFull
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (pubSets)
open VerifiableInference.Desc.Sound (mgBase)
open VerifiableInference.Desc.K13.Law (wSitsItem)
open OnBytes.Maker (WholeD)

/-- **"K13.wSits" is open at the first table's last border, at the closed constant.** -/
theorem h3_atAll {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : P5J.AtMgA o Z D r Zp Np cF x) :
    wSitsItem ∈ (pubSets (P5J.mgAtAll h).more P5J.At.links
      (VerifiableInference.Desc.First.flatPlaces true P5J.At.links true))[
        (VerifiableInference.Desc.First.flatPlaces true P5J.At.links true).length]?.getD [] :=
  wSits_open_mgAll h.𝔇 mgBase rfl

end VerifiableInference.OnPublicFiles.Last
