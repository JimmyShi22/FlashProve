-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SpotsAtName.lean: THE NAMED TEST At.spotsB (in
Johnson/P5J/OptsOk.lean) ACCEPTS, IN THE LETTER OF THE JOIN OF THE NAMED CONDITIONS: at files in the
goals' scope, where the description's value is laid (LaidAt), UNDER ONE NAMED RESIDUE: hrows: «the
second reading of the three public files returns». NO PIN IS SPENT, and not the test on the rounds'
data (protocolDataWellFormed). A law file; no running text imports it.

  spotsB_at_name   InScope Z · readFiles Z = .ok pp ·
                   LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF ·
                   hrows : ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R ⟹
                   At.spotsB Zp Z.lay = true.
BY: SpotsOfRows.lean's spots_core (the typed table is made, with at most 25 rows) ·
SpotsAnswer.lean's pAt_answers (the places' numbers answer at all 25), whose premise «the sized
request has 25 links» is PlannerRequestHas25Links.lean's pub_links, from the scope alone · LaidAt's fields pub,
planOk, opened · the public part holds the two files that it was made of (pubBy_fields).
hrows IS NOT PAID: see SpotsOfRows.lean's head.
Limits. The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.Opts.SpotsOfRows
import Johnson.Top.H0.Opts.SpotsAnswer
import Johnson.P5J.OptsOk
import Johnson.P5J.LaidOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc.First.K2Caller (spots_core pub_links)

/-- **The named test accepts, under the one residue.** -/
theorem spotsB_at_name {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hR : VerifierAndGoals.readFiles Z = .ok pp) {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hrows : ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) : spotsB Zp Z.lay = true := by
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain ⟨-, -, -, -, -, e1, e2⟩ := ProofFile.Law.pubBy_fields
    (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Z.pol Z.lay Z.KL = .ok Zp
      from L.pub)
  exact spots_core hZ hrows e1 e2 (P1K2.pAt_answers hZ hR O L.planOk (pub_links hZ L.pub))

end P5J.At

#print axioms P5J.At.spotsB_at_name
