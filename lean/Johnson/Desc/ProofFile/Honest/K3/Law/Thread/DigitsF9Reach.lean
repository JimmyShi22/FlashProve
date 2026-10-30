-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsF9Reach.lean: at every state that the verifier
reaches in front of a lookup on the digits, under the library's hypothesis `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean), the field f9 of the state's structure of the smallness test is the
plan's. So the one hypothesis on the state that Honest/K3/Law/Thread/DigitsTlKept.lean leaves gives
way to "the state is reached at that border". Theorems: each joins lemmas of the library; no
definition.

Terms. Honest/K3/GLOSSARY.md. In this file: "reached" is the library's `Reach`
(Johnson/Top/H0/Walk/Reach.lean) at the first tree's number 0, the first chain's flat list and the
description's first state. `tlAt X l` (Johnson/Desc/First/Look/Laid.lean) is the plan's structure of
link l's smallness test. `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the
border in front of link l's lookup; d is true for the lookup on the digits.

What is shown.
  `f9_planned`: the reading f9 is a planned reading (`Planned`,
    Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
  `built_tl_head`: the plan's structure at link l (`tlAt`) is the built link's.
  `border_digits`: the border in front of the lookup on the digits stands two behind the border of
    the draw.
  `f9_reach_core`, `f9_at_reach`: at every state reached at that border, the structure's f9 is the
    plan's.
  `digits_heard_reach`: `digits_heard_front` (Honest/K3/Law/Thread/DigitsTlKept.lean) with "the
    state in front is reached at the border" in the place of its hypothesis on the state.

Hypotheses that remain.
  `h`, `hl`: the library's hypothesis `P5J.AtMgA`; the link's number is below 25.
  `hr`: (in `f9_reach_core`, `f9_at_reach`) the state is reached at the border.
  In `digits_heard_reach`:
  `hs`, `hd`: a site on the digits; `site_there_head` (Honest/K3/Law/Thread/SiteThereHead.lean)
    gives one under its hypothesis hr: `rngIn` (Honest/K3/Lot.lean) returns a number at the link.
  Inside the statement: the state in front is reached at that border; the step accepts.
  For the clause on eps alone: `Good.Ok rs` (Honest/K3/Good/Levels.lean). The library's test
    okRoundsE yields it (Honest/K3/Law/Thread/OkOfRounds.lean); on rounds that the frame has played,
    okRoundsE is shown in `okRounds_played` and `okRounds_moved`
    (Honest/K3/Law/Thread/OkPlayed.lean).
Who shows "reached" where these theorems are used is not settled here.
In the steps: `O`, `e3`: (in `built_tl_head`) the description returns; the ground's built list has
Xl at l. `hx`, `hp`, `hn`: (in `f9_reach_core`) (l, i, n) is one of the library's stretches, (l, i)
one of its places; 1 ≤ n.

How the proof goes. The theorems call the library's `planned_at_draw`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean), `stretch_leaves`
(Johnson/Desc/First/Link/Law/PlannedToBatch.lean), `reach_carries`
(Johnson/Desc/First/Link/Law/ReachLeaves.lean), `P1K8S.sitsAt_open`
(Johnson/P1K8R/OrderAtSeat.lean), `tlAt_of_built` (Johnson/P5T/DigStaticAtMg.lean), `zip_tails`
(Johnson/P5T/DigFiveAtMg.lean), `Meaning.K2.blank_built` (Johnson/IMR/OwnSeat.lean) and
`ProofFile.Law.pub_builtOf` (Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean).

Users. Honest/K3/Law/Thread/DigitsHeardThr.lean [not in this library] calls `digits_heard_reach`.

Limits. On the verifier's side alone. At the full size and the earlier hash (`OnBytes.secondHashFunction`)
alone. This file shows of no proof that a state is reached there. No instance of these hypotheses is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsTlKept
import Johnson.Desc.First.Link.Law.PlannedAtDraw
import Johnson.P5T.DigStaticAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (HTailF2)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.Look (tlAt)
open VerifiableInference.Desc.First.K8 (readTl)
open VerifiableInference.Desc.LinkJoin (Planned planned_at_draw stretch_leaves reach_carries
  tlAt_of_built zip_tails)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The reading f9 is a planned reading. -/
theorem f9_planned : Planned (fun tl : HTailF2 => tl.f9) :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- The border in front of the lookup on the digits stands two behind the border of the draw. -/
theorem border_digits (l : Nat) :
    borderOf l true = 14 * l + (if l = 24 then 5 else 4) + 2 + 2 := by
  unfold borderOf ixOf
  by_cases h24 : l = 24
  · subst h24
    rfl
  · simp only [h24, ↓reduceIte]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The plan's structure at link l is the built link's.** Conditional on `P5J.AtMgA` and the
description's return. -/
theorem built_tl_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    {Fd : FileDescription Inst} {Bs : PureBase} {base : List (Block TS ProofFile.Cl)} {A : SharedSeat}
    {B : SecondSeat} (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL Fd Zp Bs base cF A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : tlAt Zp.p.X l = some Xl.tl := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built O.blank
  rw [e] at e3
  obtain ⟨b, hb, eT, _⟩ := zip_tails e3
  obtain ⟨b', hb', e'⟩ := ProofFile.Law.pub_builtOf h.laid.pub
  rw [← e'] at hb
  have hb2 : (b'.links.map ProofFile.Law.blank)[l]? = some b := hb
  rw [Array.getElem?_map] at hb2
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hb2
  rw [eT]
  show tlAt Zp.p.X l = some Y.tl
  exact tlAt_of_built h.scope h.reads h.pubOne hb' hl hY

/-- The core, at an entry of the library's two lists `P1K8S.stretches` and `P1K8S.places`. -/
theorem f9_reach_core (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (i n : Nat) (hx : (l, i, n) ∈ P1K8S.stretches) (hp : (l, i) ∈ P1K8S.places) (hn : 1 ≤ n)
    (a : ProofFile.InstPub × TS)
    (hr : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + i + 2 + 2) a) :
    ∃ tlP, tlAt Zp.p.X l = some tlP ∧ a.2.tl?.map (·.f9) = some tlP.f9 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, _, Xl, _, _, _, e3, _⟩ := P1K8S.sitsAt_open h.scope h.reads O _ hp
  refine ⟨Xl.tl, built_tl_head h l hl O e3, ?_⟩
  exact reach_carries 0 cF.blocksInOrder (ProofFile.startS Zp) (readTl fun tl : HTailF2 => tl.f9)
    (14 * l + i + 2) 2
    (fun j h1 h2 b hb => stretch_leaves h.scope h.reads O hx _ f9_planned.four f9_planned.draw j h1
      (show j < 14 * l + i + 2 + (n + 1) by omega) b hb)
    (fun _ => some Xl.tl.f9)
    (fun b hb => planned_at_draw f9_planned h.scope h.reads O hp e3 b hb) a hr

/-- **At every state reached in front of the lookup on the digits of link l, the f9 of the smallness
test's structure is the plan's.** Conditional on `P5J.AtMgA`. No instance of these hypotheses is
exhibited in this file. -/
theorem f9_at_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (a : ProofFile.InstPub × TS)
    (hr : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf l true) a) :
    ∃ tlP, tlAt Zp.p.X l = some tlP ∧ a.2.tl?.map (·.f9) = some tlP.f9 := by
  rw [border_digits] at hr
  exact f9_reach_core h l hl _ (if l = 24 then 3 else 2)
    (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩) (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)
    (by split <;> omega) a hr

/-- **`digits_heard_front` with "reached" in the place of its hypothesis on the state.** Conditional
on `P5J.AtMgA`, the site, and the state in front being reached at the border. The clause on eps also
on `Good.Ok rs`. No instance of these hypotheses is exhibited in this file. -/
theorem digits_heard_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
      ∀ (z : ProofFile.InstPub) (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf s.link true)
          (z, sj) →
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
          OpenSame g (lookHeardAt tl.f9 0 (rs.map (·.drawn))) ∧
          g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
          (Good.Ok rs → g.leaves.eps = one rs (firstRound (faceOf tl.f9) .leaves)) := by
  obtain ⟨tlP, ht, hP⟩ := digits_heard_front h s hs hl hd
  intro blk hblk z ft sj sj' n rs c hr hstep
  obtain ⟨tlQ, hq, e⟩ := f9_at_reach h s.link hl (z, sj) hr
  obtain rfl : tlP = tlQ := Option.some.inj (ht.symm.trans hq)
  refine hP blk hblk ft sj sj' n rs c hstep fun tl₀ k => ?_
  have e' : sj.tl?.map (·.f9) = some tlP.f9 := e
  rw [k] at e'
  exact Option.some.inj e'

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.f9_planned
#print axioms ProofFile.Honest.K3.Law.AtThr.border_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.built_tl_head
#print axioms ProofFile.Honest.K3.Law.AtThr.f9_reach_core
#print axioms ProofFile.Honest.K3.Law.AtThr.f9_at_reach
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_reach
