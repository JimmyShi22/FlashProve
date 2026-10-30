-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/FitsTheLedger.lean: a test of fit, which proves nothing new. It makes Lean
check that `r8_of_returns` and `r8'_of_returns` (PinsOfReturns.lean in this folder) are, to the
letter, the premises r8 and r8' of `IM.keyBack_of_rows` (Johnson/IMR/KeyBackOfRows.lean),
the theorem whose premises together make `Key.keyDataAndDecisionOfPlannerAnswer` return, and that the fourth conclusion
of `IM.keyPins_at_made` is its hk.

Main name. `fits_the_ledger` (the "ledger" is that theorem's list of premises): that theorem's
conclusion, with r8, r8' and hk filled in from hZ, hX, hm and h32 (the premises of
PinsOfReturns.lean), which stay premises; so do its other seven premises (r1 to r7) and the part on
N and P (`PinsNP`).

Limits. No premise is proved: none of r1 to r7, and not that `publicOfO` or `Key.madeAt` returns at
any files. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.PinsOfReturns
import Johnson.IMR.KeyBackOfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference VerifiableInference.Desc
open Johnson.G (dryKeyFull writtenKFull)
open Johnson.G.OfPlan (Made writtenOf)
open OnBytes.Model.Verify (Public chainsOf chainsOf_parts)
open Lk6.AtPlan (keyFull)

section
variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {cfg : ByteArray} {m : Made}
  {X : Key.Source}

/-- **A test of fit.** `IM.keyBack_of_rows` takes `r8_of_returns` and `r8'_of_returns` as its r8 and
r8', and the fourth conclusion of `IM.keyPins_at_made` as its hk. -/
theorem fits_the_ledger (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay cfg = .ok m) (h32 : cfg.size = 32) (r1 : Key.sourceOf m = .ok X)
    {N : H2U.PlaceNums} {P : Key.LaterPlaces} (r2 : Key.rangesNumbers m = .ok N)
    (r3 : Key.laterPlaces m = .ok P) (r4 : (Key.descriptionFromSource X N P).planOk = true)
    (r5 : (Key.descriptionFromSource X N P).wantedOk = true) (r6 : (Key.descriptionFromSource X N P).owedOk = true)
    (r7 : ∀ n : OnBytes.Model.Verify.ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hn : PinsNP N P) :
    Key.keyDataAndDecisionOfPlannerAnswer X₀ Z.lay m = .ok (writtenKFull, ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run) :=
  IM.keyBack_of_rows X₀ Z.lay r1 r2 r3 r4 r5 r6 r7 (IM.keyPins_at_made hZ hX hm).2.2.2.1
    (r8_of_returns hZ hX hm h32 r1 hn) (r8'_of_returns hZ hX hm h32 r1 N P)

end

end Johnson.KB8

#print axioms Johnson.KB8.fits_the_ledger
