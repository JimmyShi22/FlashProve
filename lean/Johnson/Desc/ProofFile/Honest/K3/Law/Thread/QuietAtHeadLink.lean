-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/QuietAtHeadLink.lean: under the library's hypothesis
`P5J.AtMgA` the equation on `quietAt` (Johnson/Desc/First/Look/K3Whole.lean) is shown at the digits
of the head's own link, 24: what stands behind the lookup there without a round is `quietHead`. The
companion of Honest/K3/Law/Thread/QuietAtLink.lean, which shows the equation at the other 24 links.
Theorems, by unfolding; no definition.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `isHead_head`: link 24 is the head's.
  `quiet_head_head`: the equation at link 24.
  `quiet_head_site`: the same at a site whose link is 24.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `e`: (in `quiet_head_site`) the site's link is 24.

How the proof goes. The proofs call the library's `H2K5.Door.scope_all`
(Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean): attention is covered; there are twelve groups.

Users. Honest/K3/Law/Thread/HeadDigitsAtLink.lean calls `isHead_head` and `quiet_head_site`;
Honest/K3/Law/Thread/LaysNextLight.lean calls `quiet_head_site`;
Honest/K3/Shape/ClaimAtHeadLink.lean [not in this library] calls `isHead_head`;
Honest/K3/Law/Thread/CallerAtLink.lean imports this file.

Limits. On public data alone. At the full size alone, since `P5J.AtMgA` is. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.First.Att.Door.Law.K5RestOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K3 (quietAt quietHead isHead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Link 24 is the head's. -/
theorem isHead_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : isHead Zp.p.X 24 = true := by
  obtain ⟨p4, ng, -⟩ := H2K5.Door.scope_all h
  have p4' : Zp.p.X.p4 = true := p4
  have ng' : Zp.p.X.NGr = 12 := ng
  unfold isHead
  rw [p4', ng']
  rfl

/-- **The equation at the head's own link.** Conditional on `P5J.AtMgA`. -/
theorem quiet_head_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    quietAt Zp.p.X 24 true = some (quietHead Zp.p.X) := by
  unfold quietAt
  simp [isHead_head h]

/-- The same at a site whose link is 24. -/
theorem quiet_head_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (e : s.link = 24) :
    quietAt Zp.p.X s.link true = some (quietHead Zp.p.X) := by
  rw [e]
  exact quiet_head_head h

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.isHead_head
#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_head_head
#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_head_site
