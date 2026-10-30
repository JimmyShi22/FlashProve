-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CallerAtLink.lean: conditional on the library's
hypothesis `P5J.AtMgA`, a site's caller is the head exactly at link 24; so what is asked "at the
digits, where the caller is the head" is asked at no site but those on the digits of link 24.
Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: `hc` is "the site's caller is the head" (`s.caller =
.head`); `hq` is "the step without a round behind the lookup on the digits is the head's" (`quietAt
Zp.p.X s.link true = some (quietHead Zp.p.X)`).

What is shown.
  `caller_head_iff`: at a site of `lookSites Zp`, `hc` holds exactly where the site's link is 24.
  `caller_ne_head`: at a link other than 24 the caller is not the head.
  `headReturns_offHead`: `HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean) holds, emptily, at every
    site whose link is not 24.
  `headReturns_but_one`: the same at every site on the calls or off link 24: it leaves out the sites
    on the digits of link 24 alone.
  `quiet_of_caller`: `hc` gives `hq`.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hs`: the site stands in `lookSites Zp`.
  `e`: (in `caller_ne_head`, `headReturns_offHead`) the site's link is not 24. `hn`: (in
    `headReturns_but_one`) the site is on the calls, or its link is not 24. `hc`: (in
    `quiet_of_caller`) as under Terms.

How the proof goes. A site's caller is `callerOf` (Honest/K3/Lot.lean) of two public numbers and the
link (`site_facts`, Honest/K3/Law/MemberSite.lean); under `P5J.AtMgA` the two numbers are "attention
links stand between" and 12 groups (`H2K5.Door.scope_all`,
Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean). `caller_head_site`
(Honest/K3/Law/Thread/HeadDigitsAtLink.lean) is one direction of the first theorem.

Imported, through Honest/K3/Law/Thread/QuietAtHeadLink.lean and
Honest/K3/Law/Thread/HeadReturnsElse.lean. Files under Honest/Thread/.

Users. `headReturns_notHead` and `headReturns_else` (Honest/K3/Law/Thread/HeadReturnsElse.lean) take
"the caller is not the head" as a hypothesis: the second theorem shows it at the 24 other links.
`carries_headDigits` (Honest/K3/Law/Thread/CarriesHeadDigits.lean) takes `hq` and
`returns_headDigits` (there) takes `hc`: the last theorem lets one hypothesis serve both. Both lacks
were pointed out for the files under Honest/Thread/.

Limits. `hq` is not shown to give `hc`: one direction alone. At the digits of link 24 nothing is
shown of `HeadReturns`. Public data alone, but for the form of `HeadReturns`, which speaks of a
thread's letters: where this file shows it, it holds emptily. That a site stands at each link, and
how many, is not this file's (`site_at_all_fifty`, Honest/K3/Law/Thread/SiteAllFifty.lean, has the
first). At the full size alone: `P5J.AtMgA` speaks of no other. No instance of these hypotheses is
exhibited in this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtHeadLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadReturnsElse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K3 (quietAt quietHead)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.FirstThread (Letters)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At a site of `lookSites Zp` the caller is the head exactly where the link is 24. Conditional on
`P5J.AtMgA`. No instance of this hypothesis is exhibited in this file. -/
theorem caller_head_iff (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : s.caller = .head ↔ s.link = 24 := by
  unfold lookSites at hs
  obtain ⟨y, -, hy⟩ := List.mem_filterMap.1 hs
  obtain ⟨-, -, f3, -, -, -, f7, -⟩ := site_facts _ _ y s hy
  obtain ⟨p4, ng, -⟩ := H2K5.Door.scope_all h
  have p4' : Zp.p.X.p4 = true := p4
  have ng' : Zp.p.X.NGr = 12 := ng
  rw [f7, ← f3, p4', ng']
  by_cases e : s.link = 24
  · simp [callerOf, e]
  · by_cases m : s.link % 2 = 0 <;> simp [callerOf, e, m]

/-- At a link other than 24 the caller is not the head. Conditional on `P5J.AtMgA`. No instance of
this hypothesis is exhibited in this file. -/
theorem caller_ne_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (e : s.link ≠ 24) : s.caller ≠ .head :=
  fun hc => e ((caller_head_iff h s hs).1 hc)

/-- Where the caller is the head, the step without a round behind the lookup on the digits is the
head's. Conditional on `P5J.AtMgA`. No instance of this hypothesis is exhibited in this file. -/
theorem quiet_of_caller (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hc : s.caller = .head) :
    quietAt Zp.p.X s.link true = some (quietHead Zp.p.X) :=
  quiet_head_site h s ((caller_head_iff h s hs).1 hc)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- `HeadReturns` holds, emptily, at every site whose link is not 24. Conditional on `P5J.AtMgA`.
No instance of this hypothesis is exhibited in this file. -/
theorem headReturns_offHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (b : Nat) (s : Site)
    (hs : s ∈ lookSites Zp) (e : s.link ≠ 24) : HeadReturns L b Zp s :=
  headReturns_notHead L b Zp s (caller_ne_head h s hs e)

/-- `HeadReturns` holds, emptily, at every site on the calls or off link 24. Conditional on
`P5J.AtMgA`. No instance of this hypothesis is exhibited in this file. -/
theorem headReturns_but_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (b : Nat) (s : Site)
    (hs : s ∈ lookSites Zp) (hn : s.digits = false ∨ s.link ≠ 24) : HeadReturns L b Zp s :=
  headReturns_else L b Zp s (hn.imp id (caller_ne_head h s hs))

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.caller_head_iff
#print axioms ProofFile.Honest.K3.Law.AtThr.caller_ne_head
#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_of_caller
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_offHead
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_but_one
