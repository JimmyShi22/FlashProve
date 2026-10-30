-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/MemberAtSite.lean: the kind "lookup" (K3): conditional,
under the library's hypothesis `P5J.AtMgA` alone: the first chain's member at a site's place
declares the plan's entries at the site, and these pass the verifier's test at the site's face. One
theorem.

Terms. Honest/K3/GLOSSARY.md: see there site, lot, member and flat list.

What is shown.
  `member_at_site`: the member's rounds, and the entries' test.

How the proof goes. The head's field "laid" opens the description's return; there the lookups' lot
has a sub-protocol at every site's place (`lot_of_site`, Honest/K3/Law/LotOfSite.lean); every member
passes its test on the plan (`plans_at`, Johnson/AtFull/Shape/PlansAtHead.lean);
the rest is `member_plan_site` (Honest/K3/Law/Thread/SitePays.lean).

Hypotheses that remain.
  `h`: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x` (Johnson/P5J/MgAtAll.lean): the library's
    hypothesis at the full size.
  `hs`, `hb`, `hp`: the site; the member of the flat list; it stands at the site's place.

The default. `s.p.entries.getD []` reads an option of public data. At the empty list the second half
of the end is false: the verifier's list is never empty.

Users. Honest/K3/Good/H3/Member.lean and Guards.lean.

Limits. At the full size alone: that limit comes with `P5J.AtMgA`. No instance of that hypothesis is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.AtFull.Shape.PlansAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K3 (entriesFit)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on P5J.AtMgA: the first chain's member at a site's place declares the plan's entries
at the site, and these pass the verifier's test at the site's face. -/
theorem member_at_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (b : Block TS ProofFile.Cl) (hb : b ∈ cF.blocksInOrder) (hp : b.place = s.at_.place) :
    b.rounds = (s.p.entries.getD []).map Law.declOf ∧
      entriesFit s.at_.face (s.p.entries.getD []) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hl, hls⟩ := Law.lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  obtain ⟨h1, _, h3⟩ := Law.AtThr.member_plan_site _ _ _ _ _ Zp Bs base cF _ _ O s hs lot b hl hls
    hb (hp.trans hls.symm) (Johnson.AtFull.Shape.plans_at h b hb)
  exact ⟨h1, h3⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.member_at_site
