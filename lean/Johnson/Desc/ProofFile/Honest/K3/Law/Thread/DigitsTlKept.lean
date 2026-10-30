-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsTlKept.lean: the accepting step at a lookup on the
digits sets four fields of the state's structure of the smallness test anew and leaves the rest: so
the structure behind has the f9 of the structure in front. This holds at all three sorts of link
alike. Theorems: each joins earlier ones; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: a sub-protocol of the lookups' form is one with `FormAt`
(Honest/K3/Law/MemberOne.lean). `tlAt X l` (Johnson/Desc/First/Look/Laid.lean) is the
plan's structure of link l's smallness test. `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is
the number of the border in front of link l's lookup; d is true for the lookup on the digits.

What is shown.
  `form_tl`: at a sub-protocol of the lookups' form on the digits: the structure behind, written
    out.
  `digits_tl_site`: the same at the description's own member at the border `borderOf s.link true`,
    under the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). The head of
    Honest/K3/Law/Thread/DigitsShapeHead.lean points here for the fact that the step does not change
    f9.
  `digits_heard_front`: `digits_heard_plan` (DigitsShapeHead.lean) written at the f9 of
    the structure behind. It also assumes that the structure in front has the plan's f9.

Hypotheses that remain.
  `Fm`, `h`: (in `form_tl`) b has the lookups' form, on the digits; its step accepts.
  `h`: (in the two others) the library's hypothesis `P5J.AtMgA`.
  `hs`, `hl`, `hd`: s is a site of the public part; its link is below 25; it is on the digits (`hl`
    follows from `h` and `hs`: `link_lt_head`, Honest/K3/Law/Thread/LinkLtHead.lean).
  In `digits_heard_front`: the structure in the state in front has the plan's f9. This is a fact on
    the state in front of the step: whoever entered the link laid that structure. It is other files'
    to show; it is not shown here.
  For the clause on eps alone: `Good.Ok rs` (Honest/K3/Good/Levels.lean).

How the proof goes. The theorems call `form_state` and `digits_put`
(Honest/K3/Law/Thread/StateBehind.lean), `tl_of_fork` (Honest/K3/Law/Seats.lean), `site_block`
(Honest/K3/Law/MemberSite.lean), `memberAtSite` (Honest/K3/Law/MemberAtSite.lean) and `site_hub`
(Honest/K3/Law/Thread/AtLink.lean), and the library's `tl_putTl`
(Johnson/Desc/First/TailClaims/EquationsAtS.lean), `putFork_tl` and `quietAt_tl`
(Johnson/Desc/First/Link/Law/FourBehindDigits.lean).

Users. `digits_heard_reach` (Honest/K3/Law/Thread/DigitsF9Reach.lean) calls `digits_heard_front`,
with "the state in front is reached at the border" in the place of the hypothesis on the structure
in front.

Limits. On the verifier's side alone. Under `P5J.AtMgA`: at the full size alone. No instance of
these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsShapeHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehind
import Johnson.Desc.First.Link.Law.FourBehindDigits
import Johnson.Desc.First.TailClaims.EquationsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf quietAt seatDigits)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (P tlAt)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The structure behind, written out**, at a sub-protocol of the lookups' form on the digits.
Conditional on the form and on the step's acceptance. -/
theorem form_tl {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat} {p : P}
    {b : Block FS Cl} (Fm : FormAt claim X i true p b) (ft : Nat) (s t : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : b.step ft s rs c = .ok (t, n)) :
    ∃ tl F H G, s.tl? = some tl ∧ s.fork? = some F ∧ hearVia p F rs = some (H, G) ∧
      t.tl? = some { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H } := by
  obtain ⟨F, H, G, a1, _, _, _, a5, hQ⟩ := form_state Fm ft s t n rs c h
  have a1' : s.fork? = some F := a1
  obtain ⟨tl, htl⟩ := tl_of_fork s a1'
  have hp : ((seatDigits claim).put s H G).tl? = some { tl with
      foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H } := by
    rw [digits_put claim s htl a1' H G, VerifiableInference.Desc.LinkJoin.putFork_tl,
      VerifiableInference.Desc.First.TailClaims.Law.tl_putTl s tl _ htl]
  refine ⟨tl, F, H, G, htl, a1', a5, ?_⟩
  unfold QuietBehind at hQ
  cases hq : quietAt X i true with
  | none =>
    rw [hq] at hQ
    have hQ' : t = (seatDigits claim).put s H G := hQ
    rw [hQ']
    exact hp
  | some f =>
    rw [hq] at hQ
    have hQ' : f ((seatDigits claim).put s H G) = .ok t := hQ
    rw [VerifiableInference.Desc.LinkJoin.quietAt_tl X i f hq _ t hQ']
    exact hp

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The same at the description's own member at the border in front of the lookup.** Conditional
on `P5J.AtMgA` and the site. No instance of these hypotheses is exhibited in this file. -/
theorem digits_tl_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ tl F H G, sj.tl? = some tl ∧ sj.fork? = some F ∧ hearVia s.p F rs = some (H, G) ∧
          sj'.tl? = some { tl with
            foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H } := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  obtain ⟨Fm, _⟩ := site_block _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1 m2 m3
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite _ _ _ _ Fd Zp Bs base cF A B O lot hb blk m1 m2
  obtain ⟨hlot, _, _⟩ := (hst ft sj sj' n rs c).1 hstep
  rw [hd] at Fm
  exact form_tl Fm ft sj sj' n rs c hlot

/-- **`digits_heard_plan` at the f9 of the structure behind.** Conditional on `P5J.AtMgA` and the
site. It also assumes that the structure in the state in front has the plan's f9. The clause on eps
also on `Good.Ok rs`. No instance of these hypotheses is exhibited in this file. -/
theorem digits_heard_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∃ tlP, tlAt Zp.p.X s.link = some tlP ∧
      ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
        ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
          blk.step ft sj rs c = .ok (sj', n) → (∀ tl₀, sj.tl? = some tl₀ → tl₀.f9 = tlP.f9) →
          ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
            OpenSame g (lookHeardAt tl.f9 0 (rs.map (·.drawn))) ∧
            g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
            (Good.Ok rs → g.leaves.eps = one rs (firstRound (faceOf tl.f9) .leaves)) := by
  obtain ⟨tlP, ht, hP⟩ := digits_heard_plan h s hs hl hd
  refine ⟨tlP, ht, fun blk hblk ft sj sj' n rs c hstep hf => ?_⟩
  obtain ⟨tl, g, t1, t2, W, c1, l1, l2⟩ := hP blk hblk ft sj sj' n rs c hstep
  obtain ⟨tl₀, F, H, G, k1, _, _, k4⟩ :=
    digits_tl_site h s hs hl hd blk hblk ft sj sj' n rs c hstep
  have e : tl.f9 = tlP.f9 := by
    have e1 := Option.some.inj (t1.symm.trans k4)
    rw [e1]
    exact hf tl₀ k1
  refine ⟨tl, g, t1, t2, ?_, c1, l1, ?_⟩
  · rw [e]
    exact W
  · rw [e]
    exact l2

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.form_tl
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_tl_site
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_front
