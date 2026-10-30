-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/FallsAtLive.lean: the falls' measure at the room of the completeness error, from the
public tests alone, and at the stored full-size files with no premise.

  shareLines_of_head   the test on stated shares holds of all records, under the head
  falls_at_live        TheFallsArePaid, at public files in scope, read, passing protocolDataWellFormed
  falls_at_full        the same at the stored full-size files

Limits. The measure is that of the set at which a listed fall speaks. Whether a proof is accepted
where none speaks is another statement. Nothing in the main library imports this file.
-/
import Johnson.P1K8R.FallsPaidOfLines
import AtFullSide.K8.ShareLinesPart1
import AtFullSide.K8.ShareLinesRest
import AtFullSide.K8.QuietLine
import AtFullSide.Top.LaidAtFull
import E2E.Lookup.LookupMarksPassTheSharesTest
import Johnson.Desc.ProofFile.Honest.K4.Law.SharesSmallAtTheTest

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheFalls
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/-- **The test on stated shares holds of all records, under the head.** -/
theorem shareLines_of_head {Z : PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) : ShareLines Zp G₀ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  exact AtFullSide.K8.lines_of_others h hG (AtFullSide.K8.quiet_line h)
    (AtPublicFiles.Lookup.lookupMarksPassTheSharesTest Zp Bs.G₀) (ProofFile.Honest.K4.k4MarksWide_small h hG)
    (AtFullSide.K8.k5_marks_small h O.made) (AtFullSide.K8.k6_marks_small h hG)

/-- **The falls are paid, from the public tests alone.** -/
theorem falls_at_live {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (Relation : FullSizeMatrix → XF → Prop) : TheFallsArePaid Z Relation := by
  refine theFallsArePaid_of_lines scope hr live (fun returned hM => ?_) Relation
  obtain ⟨Np, cF, D, r, L, -, -⟩ := return_laid live hM
  obtain ⟨xh, h⟩ := head_at_laid Z scope live L
  exact shareLines_of_head h (return_ground hM)

end AtPublicFiles.AtFiles.HonestTerm

/-- **At the stored full-size files.** -/
theorem AtFullSide.K8.falls_at_full (Relation : AtPublicFiles.AtFiles.FullSizeMatrix → LPFD.Full.XF → Prop) :
    AtPublicFiles.AtFiles.HonestTerm.TheFallsArePaid VerifierAndGoals.storedPublicFiles Relation := by
  obtain ⟨pp, -, -, -, -, -, scope, hr, live, -⟩ := AtFullSide.Top.premises_met_at_full
  exact AtPublicFiles.AtFiles.HonestTerm.falls_at_live scope hr live Relation

#print axioms AtPublicFiles.AtFiles.HonestTerm.shareLines_of_head
#print axioms AtPublicFiles.AtFiles.HonestTerm.falls_at_live
#print axioms AtFullSide.K8.falls_at_full
