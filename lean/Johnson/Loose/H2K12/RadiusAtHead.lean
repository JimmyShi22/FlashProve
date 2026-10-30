-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.HB.LLHARD.RadiiInScope
import Johnson.P5J.MgAtAll
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
/-
Johnson/Loose/H2K12/RadiusAtHead.lean: The proximity test
(the kind K12) on the proof file's first chain, sub-protocol number 354 of the table of joints: THE ONE CLOSED FACT ON A RADIUS that
is left of its law's list of debts (the field radius of K12Rest₆, K12LeftOfRest.lean), UNDER THE HEAD OF THE COMPOSED MEANING's
CONSTANT AND ONE ENTRY TEST. One statement; its proof is one call of another file's theorem.
  `radius_at_head`: under the head, where the row `madeRow` accepts: whatever rows the maker of the sendings' rows
    returns at the three public files, the radius at sending 75, place 0 is the written rows'.
THE CALL: `rad_in_scope` (Johnson/HB/LLHARD/RadiiInScope.lean) at (75, 0): its scope and its
public part are the head's fields; its accept of `madePinnedAt` is `pinnedAt_of_row`
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) at the row's accept; its written radii are, by their text, entries
24 to 105 of the written list of all chains' rows.
THE BUILD THAT IT NEEDS: whatever holds that theorem's cone: four files in its own folder (Johnson/HB/LLHARD/) and seven other files
(Johnson/Desc/First/Link/RowsRun · Link/Law/RowsFrom · RowsFromCongr · RowsNoArms · RowsOfMade ·
Johnson/LPFE1R/RowsAtWritten · RowsOneInScope).
What it is not. NO EXAMPLE BY A THEOREM OF THIS FILE. It says nothing where the rows' maker refuses (that it returns under the
head is `rows_return`, H2K12/ClosedOfPins354.lean). The full size alone. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes.Maker
open P5J (AtMgA TS)

/-- **The radius at sending 75, place 0 is the written rows'.** -/
theorem radius_at_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hm : VerifiableInference.PlanWritten.madeRow Zp = true) :
    ∀ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R → P5T.rad? R 75 0 =
      (((((Johnson.G.packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2) :=
  fun _ hR => VerifiableInference.Desc.LinkJoin.rad_in_scope h.scope h.laid.pub
    (VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [hm, Bool.or_true])) hR 75 0

end H2K12

#print axioms H2K12.radius_at_head
