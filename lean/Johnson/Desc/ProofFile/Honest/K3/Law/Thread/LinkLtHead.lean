-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LinkLtHead.lean: under the library's hypothesis
`P5J.AtMgA` every site's link is below 25. One theorem, a composition of two others; no definition.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `link_lt_head`: s ∈ lookSites Zp gives s.link < 25.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hs`: s is a site of the public part (`lookSites Zp`).

How the proof goes. It calls `lot_of_site` (Honest/K3/Law/LotOfSite.lean) and `site_border`
(Honest/K3/Law/Thread/SiteAtLetters.lean).

Users. The main theorems at a site of Honest/K3/Law/Thread/AtLink.lean, and the files on the digits
behind it, take "s.link < 25" as a hypothesis. It follows from `h` and `hs`.

Limits. On public data alone. At the full size alone, since `P5J.AtMgA` is. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under `P5J.AtMgA` every site's link is below 25.** -/
theorem link_lt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : s.link < 25 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hb, hbs⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  exact (site_border h s hs lot hb hbs).1

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.link_lt_head
