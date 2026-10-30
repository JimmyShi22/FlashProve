-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CallsHeardLink.lean: under the library's hypothesis
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), behind an accepting step of the member at a lookup on the
calls: what the state then holds as heard is the hearing's own return from the ledger in front on
the step's rounds; its open part (the eleven fields of `OpenSame`, Honest/K3/HeardWhole.lean) is the
one that the challenges alone make; the form in which the key side ends and the form that the
leaves' sumcheck was handed name no entry of a virtual row. Theorems: each joins earlier ones; no
definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the hearing is `hearVia s.p F rs`
(Johnson/Desc/First/Look/Via/Via.lean). `lookHeardAt` (Honest/K3/HeardWhole.lean) computes the open
part from the shape, a base and a list of challenges. `borderOf l d`
(Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the border in front of link l's lookup, and
`IM.k3Place l d` (Johnson/IMR/K3Seat.lean) is that lookup's place; d is false for the lookup on the
calls. `Good.Ok rs` (Honest/K3/Good/Levels.lean) says that the words of every sampled element of the
rounds rs are below the prime.

What is shown.
  `calls_heard_site`: the statement above at a site on the calls, at the member at the border
    `borderOf s.link false`, from whatever state and on whatever rounds. A last clause, on the field
    eps of what the leaves' sumcheck was handed, also assumes `Good.Ok rs`: eps is the first element
    sampled in the first round of the stage leaves.
  `calls_heard_link`: at a link's number l < 25 there are a site on the calls and a member at the
    border `borderOf l false`, at the place `IM.k3Place l false`, and the same holds there.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hs`, `hl`, `hd`: s is a site of the public part; its link is below 25; it is on the calls (`hl`
    follows from `h` and `hs`: `link_lt_head`, Honest/K3/Law/Thread/LinkLtHead.lean).
  Inside the statements: the member at the border; the acceptance of its step; for the clause on
    eps, `Good.Ok rs`.

Follows. This file is the counterpart, at the calls, of Honest/K3/Law/Thread/DigitsHeardLink.lean,
whose two main theorems it follows line by line.

How the proof goes. The theorems call `site_hub` (Honest/K3/Law/Thread/AtLink.lean), `member_back`
(Honest/K3/Law/Thread/MemberBack.lean), `site_facts` (Honest/K3/Law/MemberSite.lean),
`heardWhole_of_hearVia` (Honest/K3/Law/HeardWholeLaw.lean), `cEnd_below`
(Honest/K3/Law/Thread/CEndBelow.lean), `hearVia_leaves` (Honest/K3/Law/Thread/DigitsHeardLink.lean),
`site_there_head` (Honest/K3/Law/Thread/SiteThereHead.lean) and `member_at_link`
(Honest/K3/Law/Thread/AtLinkThere.lean).

Users. `calls_heard_site_front` (Honest/K3/Law/Thread/CallsHeardFront.lean [not in this library])
calls `calls_heard_site`.

Limits. On the verifier's side alone. At the full size alone: that limit comes with `P5J.AtMgA`.
Whether a step accepts anywhere is not spoken of. Right behind the member's step: nothing on later
states. No instance of these hypotheses is exhibited in this file. No state and no rounds are shown
at which the step accepts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsHeardLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a site on the calls, behind an accepting step of the member at the border in front of the
lookup**, from whatever state and on whatever rounds. Conditional on `P5J.AtMgA` and the site; the
clause on eps also on `Good.Ok rs`. No instance of these hypotheses is exhibited in this file. -/
theorem calls_heard_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = false) :
    ∀ blk, cF.blocksInOrder[borderOf s.link false]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ F g G, sj.fork? = some F ∧ hearVia s.p F rs = some (g, G) ∧ sj'.lookHeard? = some g ∧
          OpenSame g (lookHeardAt s.shape 0 (rs.map (·.drawn))) ∧
          g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
          (Good.Ok rs → g.leaves.eps = one rs (firstRound s.at_.face .leaves)) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  obtain ⟨F, H, G, a1, hv, a3⟩ := member_back _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1
    m2 m3 ft sj sj' n rs c hstep
  rw [hd] at a1 a3
  have a1' : sj.fork? = some F := a1
  have a3' : sj'.lookHeard? = some H := a3
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _, _, _, f6, _, _⟩ := site_facts _ _ y s hsy
  have W := heardWhole_of_hearVia s.p s.shape f2 F G rs H [] [] hv
  rw [List.nil_append, List.append_nil] at W
  obtain ⟨l1, l2⟩ := hearVia_leaves f2 hv
  refine ⟨F, H, G, a1', hv, a3', W, (cEnd_below hv).1, l1, ?_⟩
  rw [f6]
  exact l2

/-- **At a link's number**: a site on the calls, a member at the border in front of the lookup and
at the lookup's place, and the same there. Conditional on `P5J.AtMgA`. No instance of these
hypotheses is exhibited in this file. -/
theorem calls_heard_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = false ∧
      ∃ blk, cF.blocksInOrder[borderOf l false]? = some blk ∧ blk.place = IM.k3Place l false ∧
        ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
          blk.step ft sj rs c = .ok (sj', n) →
          ∃ F g G, sj.fork? = some F ∧ hearVia s.p F rs = some (g, G) ∧
            sj'.lookHeard? = some g ∧
            OpenSame g (lookHeardAt s.shape 0 (rs.map (·.drawn))) ∧
            g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
            (Good.Ok rs → g.leaves.eps = one rs (firstRound s.at_.face .leaves)) := by
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_there_head h l hl false fun e => nomatch e
  subst e1
  obtain ⟨blk, b1, b2⟩ := member_at_link h s.link hl false
  exact ⟨s, hs, rfl, e2, blk, b1, b2, calls_heard_site h s hs hl e2 blk b1⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.calls_heard_site
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_heard_link
