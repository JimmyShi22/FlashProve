-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsHeardLink.lean: what stands in the state behind an
accepting step of the description's own member at a lookup on the digits, under the library's
hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the smallness test's structure holds what was
heard; its eleven open fields are those that the challenges and the shape fix; the form in which the
key side ends and the form that the leaves' sumcheck was handed name no entry of a virtual row; the
field eps of what the leaves' sumcheck was handed is the first element that the first round of the
stage leaves sampled. Theorems: each joins earlier ones; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the hearing is `hearVia p F rs`
(Johnson/Desc/First/Look/Via/Via.lean). The eleven open fields are those of `OpenSame`, and
`lookHeardAt` computes them from the shape, a base and a list of challenges (both
Honest/K3/HeardWhole.lean). `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of
the border in front of link l's lookup, and `IM.k3Place l d` (Johnson/IMR/K3Seat.lean) is that
lookup's place; d is true for the lookup on the digits.

What is shown.
  `hearVia_leaves`: behind the hearing: the form that the leaves' sumcheck was handed names no
    entry; the clause on eps.
  `digits_heard_site`: the statement above at a site on the digits, at whatever state and rounds.
  `digits_heard_f9`: the same written at the state's own field f9. It also assumes that this field
    is the site's shape.
  `digits_heard_link`: at a link's number: a site, a member at the border `borderOf l true`, and the
    same there. It also assumes `hr`.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hs`, `hl`, `hd`: s is a site of the public part; its link is below 25; it is on the digits (`hl`
    follows from `h` and `hs`: `link_lt_head`, Honest/K3/Law/Thread/LinkLtHead.lean).
  `hr`: (in `digits_heard_link`) `rngIn` (Honest/K3/Lot.lean) returns a number at the link; it is
    the hypothesis of `site_there_head` (Honest/K3/Law/Thread/SiteThereHead.lean) at the digits.
  `Good.Ok rs` (Honest/K3/Good/Levels.lean): the words of every sampled element are below the prime.
    It is assumed for the clause on eps alone.
  tl.f9 = s.shape: (in `digits_heard_f9`) assumed of the state behind the step. By a reading of
    Johnson/Desc/First/Look/K3Seat.lean and Johnson/Desc/First/Look/K3Whole.lean, and not by a Lean
    proof, nothing in the step at the digits compares the state's f9 with the shape that was heard.
  Inside the statements: the member at the border; the acceptance of its step.
  In the helper `hearVia_leaves` both letters have another sense: `hs`: p.shape = some sh; `h`: the
    seated hearing returns.

How the proof goes. The theorems call `site_hub` (Honest/K3/Law/Thread/AtLink.lean),
`member_at_link` (Honest/K3/Law/Thread/AtLinkThere.lean), `member_back`
(Honest/K3/Law/Thread/MemberBack.lean), `cEnd_below` (Honest/K3/Law/Thread/CEndBelow.lean),
`heardWhole_of_hearVia` (Honest/K3/Law/HeardWholeLaw.lean), `hearV_ne`
(Honest/K3/Parts/NoEntries.lean), `hearV_messages` (Honest/K3/Law/GoesOn.lean) and `heard_out`
(Honest/K3/Good/Walk.lean).

Users. `digits_heard_site` is called in Honest/K3/Law/Thread/DigitsPointsAt.lean,
Honest/K3/Law/Thread/DigitsShapeHead.lean and Honest/K3/Law/Thread/OkOfRounds.lean; `hearVia_leaves`
in Honest/K3/Law/Thread/CallsHeardLink.lean, which follows this file's two main theorems at the
calls. Honest/K3/Law/Thread/SiteAllFifty.lean imports this file too.

Limits. On the verifier's side alone. At the full size alone: that limit comes with `P5J.AtMgA`.
Whether a step accepts anywhere is not spoken of. No instance of these hypotheses is exhibited in
this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLinkThere
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.MemberBack
import Johnson.Desc.ProofFile.Honest.K3.Law.HeardWholeLaw
import Johnson.Desc.ProofFile.Honest.K3.Good.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.K3 (hearV toHeard toHeardG faceOf)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.K3.Parts (hearV_ne)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **Behind the hearing**: the form that the leaves' sumcheck was handed names no entry of a
virtual row; and, where the words of every sampled element are below the prime, the field eps is the
first element that the first round of the stage leaves sampled. Conditional on the public parameters
having the shape and on the hearing's return. -/
theorem hearVia_leaves {p : P} {sh : OnBytes.Model.Forest.Shape} {F G : Fork} {rs : List Fmt.RoundView}
    {H : OnBytes.Model.Forest.Heard} (hs : p.shape = some sh)
    (h : hearVia p F rs = some (H, G)) :
    H.leaves.start.ents.isEmpty = true ∧
      (Good.Ok rs → H.leaves.eps = one rs (firstRound (faceOf sh) .leaves)) := by
  unfold hearVia at h
  rw [hs] at h
  dsimp only at h
  by_cases hc : 1 < sh.NC
  · rw [if_pos hc] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨g, G'⟩ := y
    obtain ⟨H', hH, e⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hokf, hm⟩ := hearV_messages hy
    obtain ⟨_, _, m3⟩ := hearV_ne hy
    unfold toHeard at hH
    have hk : (toHeardG g).keys = g.keys := rfl
    rw [hk] at hH
    match hg : g.keys, hH with
    | [(point, form)], hH =>
      dsimp only at hH
      split at hH
      · obtain rfl := Option.some.inj hH
        exact ⟨m3, fun hok => (Good.heard_out hokf hok hm).eps⟩
      · exact nomatch hH
  · rw [if_neg hc] at h
    exact nomatch h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a site on the digits, behind an accepting step of the member at the border in front of the
lookup**, from whatever state and on whatever rounds: the smallness test's structure holds a
heard structure g; the open part of g is `lookHeardAt` at the site's shape, the base 0 and the
step's own challenges; the two forms name no entry of a virtual row; the clause on eps. Conditional
on `P5J.AtMgA` and the site; the clause on eps also on `Good.Ok rs`. No instance of these hypotheses
is exhibited in this file. -/
theorem digits_heard_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
          OpenSame g (lookHeardAt s.shape 0 (rs.map (·.drawn))) ∧
          g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
          (Good.Ok rs → g.leaves.eps = one rs (firstRound s.at_.face .leaves)) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  obtain ⟨F, H, G, _, hv, a3⟩ := member_back _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1
    m2 m3 ft sj sj' n rs c hstep
  rw [hd] at a3
  have a3' : sj'.tl?.bind (·.heard) = some H := a3
  obtain ⟨tl, t1, t2⟩ := Option.bind_eq_some_iff.1 a3'
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _, _, _, f6, _, _⟩ := site_facts _ _ y s hsy
  have W := heardWhole_of_hearVia s.p s.shape f2 F G rs H [] [] hv
  rw [List.nil_append, List.append_nil] at W
  obtain ⟨l1, l2⟩ := hearVia_leaves f2 hv
  refine ⟨tl, H, t1, t2, W, (cEnd_below hv).1, l1, ?_⟩
  rw [f6]
  exact l2

/-- The same written at the state's own field f9. It also assumes that this field, at the state
behind the step, is the site's shape. -/
theorem digits_heard_f9 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) → (∀ tl, sj'.tl? = some tl → tl.f9 = s.shape) →
        ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
          OpenSame g (lookHeardAt tl.f9 0 (rs.map (·.drawn))) ∧
          g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
          (Good.Ok rs → g.leaves.eps = one rs (firstRound (faceOf tl.f9) .leaves)) := by
  intro blk hblk ft sj sj' n rs c hstep hf
  obtain ⟨tl, g, t1, t2, W, c1, l1, l2⟩ :=
    digits_heard_site h s hs hl hd blk hblk ft sj sj' n rs c hstep
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, _, _, _, _, f6, _, _⟩ := site_facts _ _ y s hsy
  refine ⟨tl, g, t1, t2, ?_, c1, l1, ?_⟩
  · rw [hf tl t1]
    exact W
  · rw [hf tl t1, ← f6]
    exact l2

/-- **At a link's number**: a site on the digits, a member at the border in front of the lookup and
at the lookup's place, and the same there. Conditional on `P5J.AtMgA` and `hr`. No instance of these
hypotheses is exhibited in this file. -/
theorem digits_heard_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hr : (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      ∃ blk, cF.blocksInOrder[borderOf l true]? = some blk ∧ blk.place = IM.k3Place l true ∧
        ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
          blk.step ft sj rs c = .ok (sj', n) →
          ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
            OpenSame g (lookHeardAt s.shape 0 (rs.map (·.drawn))) ∧
            g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
            (Good.Ok rs → g.leaves.eps = one rs (firstRound s.at_.face .leaves)) := by
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_there_head h l hl true fun _ => hr
  subst e1
  obtain ⟨blk, b1, b2⟩ := member_at_link h s.link hl true
  exact ⟨s, hs, rfl, e2, blk, b1, b2, digits_heard_site h s hs hl e2 blk b1⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.hearVia_leaves
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_site
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_f9
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_link
