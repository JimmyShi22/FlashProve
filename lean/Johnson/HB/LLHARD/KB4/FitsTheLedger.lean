-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/FitsTheLedger.lean: a test of fit, which proves nothing new. It makes Lean
check that key_planOk (Row.lean in this folder) is, to the letter, the premise r4 of
IM.keyBack_of_rows (Johnson/IMR/KeyBackOfRows.lean), the theorem whose premises together make
Key.keyDataAndDecisionOfPlannerAnswer return; and that, under the same Pins, the premises r8 and r8' are had from
KB8/Row.lean.

Main name. fits_the_ledger (the "ledger" is that theorem's list of premises): that theorem's
conclusion, with r4, r8 and r8' filled in; r1, r2, r3, r5, r6, r7 and hk stay premises, with Pins
and key_planOk's four premises on parts of X.

Limits. None of the premises is proved here. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Row
import Johnson.HB.LLHARD.KB8.Row
import Johnson.IMR.KeyBackOfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference VerifiableInference.Desc
open Johnson.G (dryKeyFull writtenKFull)
open Johnson.G.OfPlan (Made writtenOf)

/-- **A test of fit.** IM.keyBack_of_rows takes key_planOk as its r4, and KB8's r8_of_pins and
r8'_of_lin as its r8 and r8'. -/
theorem fits_the_ledger {m : Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (X₀ : OnBytes.Model.Verify.Public) (lay : ByteArray) (r1 : Key.sourceOf m = .ok X)
    (r2 : Key.rangesNumbers m = .ok N) (r3 : Key.laterPlaces m = .ok P) (h : Pins X N P)
    {b₁ b₂ b₃ : ByteArray} (hread : OnBytes.Params.KeyChains.read b₁ b₂ b₃ = some X.Y.k)
    (hcfg : (X.Y.k.oneTime.given.cfg != Fmt.zero32) = true) (hmade : Key.madeAgainOk X.Y = true)
    (hunits : Key.weightsCovered X.Y.units X.Y.k.oneTime.ranges = true)
    (r5 : (Key.descriptionFromSource X N P).wantedOk = true) (r6 : (Key.descriptionFromSource X N P).owedOk = true)
    (r7 : ∀ n : OnBytes.Model.Verify.ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hk : PlanWritten.keyOf m = PlanWritten.fullKey) :
    Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m = .ok (writtenKFull, ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run) :=
  IM.keyBack_of_rows X₀ lay r1 r2 r3 (key_planOk h hread hcfg hmade hunits) r5 r6 r7 hk
    (Johnson.KB8.r8_of_pins (kb8Pins_of h)) (Johnson.KB8.r8'_of_lin N P h.lin₂)

end Johnson.KB4

#print axioms Johnson.KB4.fits_the_ledger
