-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AtYesMore.lean: the kind "the code switch" (K2): TWO MORE OF
THE TWENTY-ONE FIELDS OF THE RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), IN
THE RECORD's OWN TEXT: groupNo · inRange. Under the library's head and the opening, at a switch of
the plan, WHERE THE KIND's OWN DECISION SAYS YES at the state behind the place's step in front. BOTH
ARE PUBLIC. IT DOES NOT SAY THAT THE RECORD IS MET. That file is not imported: the fields' texts are
copied. No definition; one closed fact by evaluation in Lean's kernel, with a control; lemmas.

  `yes_group_range`   at a yes of the kind's own decision: the front's group is the place's number
                    grp, and each position drawn lies below 2 ^ logN: the decision's own two tests
  `placeLinksW`     BY LEAN's KERNEL: a written place's link is its place's, and 25 where the place
                    names none; a control: against 24 the test says no somewhere
  `grp_at_head`     the plan's number grp at a switch is the switch's link
  `two_more_at_yes`   THE END: groupNo · inRange

By, sealed, of other authors: `stands`, `link_inv`, `head_inv`, `finish_inv`
(Johnson/Top/H0/Tw/K2C/Laws.lean, Closed.lean) · `firstBehind_iff` (Asks.lean) · `frontOf_iff`
(DebtsState.lean) · `numsAt_grp`, `prepOf_request` (GroupAtNums.lean) · `listOfT_eq`
(OnBytes/Chain/Draws.lean) · `AtYes` (Johnson/Top/H0/K2Hears/Whole.lean). Ours: `request_at_head`
(Honest/K2/Law/AtYesTarget.lean) · `places_at_head` (PlacesWritten.lean).

Limits. PUBLIC: no coin, input or run occurs. THE YES (hy) AND `AtYes` ARE PREMISES; hy may stand at
other groups of columns than `AtYes`: of hy the front and the second round's positions alone are
read. The table's numbers are the head's (`P5J.At.N`), whose groupAt is the identity. The full size
and the format's second hash function alone. The head and the opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesTarget
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Top.H0.Tw.K2C.DebtsState
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes FrontOf decideWith frontOf_iff stands link_inv
  head_inv finish_inv)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **At a yes of the kind's own decision**: the front's group; the positions' range. -/
theorem yes_group_range {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, FrontOf p s x ∧ x.f.group = p.grp ∧
      ∀ v ∈ r₂.drawn.poss, v < 2 ^ p.logN := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, A', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨mask, B⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 hl.hBehind
    refine ⟨x, Or.inl ⟨hp, hl.hFront⟩, ?_, hl.hRange⟩
    have e := hl.hGrp
    rw [B.frame] at e
    exact e
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    exact ⟨_, Or.inr (Or.inl ⟨hp, o, G, hl.hHere, hl.hGroup, rfl⟩), hl.hGrp, hl.hRange⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    exact ⟨_, Or.inr (Or.inr ⟨hp, o, G, hl.hHere, hl.hLaid, rfl⟩), hl.hGrp, hl.hRange⟩

set_option maxRecDepth 1000000 in
/-- **A written place's link is its place's, and 25 where the place names none**; the written
request has 25 links; a control: against 24 the test says no. -/
theorem placeLinksW :
    (placesW.all fun p => p.link == p.place.link.getD 25) = true ∧
      proofSizedFull.request.link.length = 25 ∧
      (placesW.all fun p => p.link == p.place.link.getD 24) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **The plan's number grp at a switch is the switch's link.** -/
theorem grp_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) : n.grp = p.link := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  rw [P1K2.numsAt_grp hn, (P1K2.prepOf_request hP).2, O.first, request_at_head h, placeLinksW.2.1]
  exact (beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hpW)).symm

/-- **TWO MORE FIELDS OF `MadeAsks`, IN ITS OWN TEXT**: groupNo · inRange. hy: the kind's own
decision says yes at s₁, at the same two rounds. -/
theorem two_more_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) {st : First.K2.At} (nm : String) {s₁ t u : TS}
    {r₁ r₂ : Fmt.RoundView} {gs gs' : List (List (Nat × List UInt64))}
    (hy : decideWith sendByL8 (k2P Zp p.place nm st n) s₁ [r₁, r₂] gs' = .ok u)
    {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    (P5J.At.N Zp cF).groupAt p.link = x.f.group ∧
      ∀ v ∈ (Positions.ofDraws (k2P Zp p.place nm st n).logN r₂.drawn.poss).all.toList,
        v < 2 ^ (S3.codes.base.getD x.f.rows.code default).logN := by
  obtain ⟨x', hx', hg, hr⟩ := yes_group_range hy
  obtain rfl : x' = x := Option.some.inj ((frontOf_iff.1 hx').symm.trans A.front)
  refine ⟨?_, ?_⟩
  · rw [hg]
    show p.link = n.grp
    exact (grp_at_head h O hp hP hn).symm
  · intro v hv
    have hv' : v ∈ listOfT r₂.drawn.poss := by simpa [Positions.ofDraws] using hv
    rw [listOfT_eq, Fmt.listOf_mem] at hv'
    have ec : S3.codes.base.getD x'.f.rows.code default = cd := by
      rw [A.same.codes, Array.getD_eq_getD_getElem?, A.code]
      rfl
    rw [ec, A.logN]
    exact hr v hv'

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.yes_group_range
#print axioms ProofFile.Honest.K2.Law.placeLinksW
#print axioms ProofFile.Honest.K2.Law.grp_at_head
#print axioms ProofFile.Honest.K2.Law.two_more_at_yes
