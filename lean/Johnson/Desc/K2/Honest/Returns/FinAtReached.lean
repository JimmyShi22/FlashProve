-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FinAtReached.lean: THE LAW "THE KIND's OWN DECISION SAYS YES AT THE
PLACE BEHIND THE LAST SEGMENT, BEHIND ITS QUIET FRONT" (`FinBehind`, Returns/ArmsBehind.lean),
WHOLE, AT A STATE THAT IS REACHED AT THE NUMBER 353, AT THE NUMBERS THAT THE PLAN's OWN MAKER LAYS
FOR THE PLACE, FROM WHAT IS LEFT (`FinRest`: thirteen clauses): UNDER THE PREMISES IN FRONT AND
THREE NAMED TESTS ON THE PUBLIC PART, AND UNDER THE ONE HEAD `P5J.AtMg` ALONE. SO THE KIND's OWN
DECISION RETURNS THERE. What Returns/HeadAtReached.lean has at the output head's place. A join.
Statements with their proofs: calls.

  `h25_of_hy` in scope the test hy gives: the first chain's shape has 25 segments, which this
                    folder's files at this place take as a premise
  `fin_paid` `CallPaid` (Returns/CallJoin.lean) at the place's front, and the range of the positions
                    drawn
  `fin_number_reached` `FinBehind.number`: the place's own frame's group is the plan's number
  `FinRest p t r₁ r₂ gs a Q c` WHAT IS LEFT: `CallRest`'s eleven at the place's front · noneLeft ·
                    groups
  `fin_behind_reached`, `fin_returns_reached` FOR ALL t, a, Q, c₀ that are the state's own (the
                    quiet front's yes from the reached state to t; `t.here = .fin a`; `a.G = some
                    Q`; the code that stands in t's statement's list at the frame's shape's code):
                    `FinRest` gives `FinBehind`; and so the decision's yes at t
  `fin_behind_at_head`, `fin_returns_at_head` the same under the head alone: no test

THE COUNT. `FinBehind` laid open has 59 clauses: nine of its own and the call's 50. 43 are laid in
by payers; three are look-ups (quiet · here · laid); 13 are `FinRest`'s. Of the 43, fifteen stand
under the three tests as typed, and `number`, `oldCode`, `keptPos`, `stored` and what hangs on the
25 segments under hy (under the head: under nothing more), six under the entry's test and the rounds
that fit.

WHO PAYS WHAT. `fin_waits_reached` (Returns/ArmsFree.lean) · `fin_oldCode_reached`,
`fin_keptPos_reached` (Returns/ArmsPlan.lean) · `finish_draws_plan` (Returns/LinkReached.lean):
range and four on the draws · `fin_lay_reached`, `fin_members_reached`, `fin_closed_reached`
(Returns/ClosedArms.lean) · `stated_of_close` (Returns/MembersReached.lean) ·
`fin_claimMain_reached` (Returns/ClaimMainReached.lean) · `fin_goodS_reached`, `fin_stored_reached`
(Returns/StoredArms.lean) · `fin_shape_reached` (Returns/PinArms.lean) · `fin_public_reached`
(Returns/PinPublic.lean) · `tests_at_head` (Returns/UnderHead.lean) · the library's `sw_finish`
(Johnson/P1K2R/HstReached.lean): the entry's test is led from the plan's own list to the front's
notices · `front_nums_fin` (Johnson/IMR/FinCount.lean), `numsAt_grp`, `prepOf_z`
(Johnson/Top/H0/Tw/K2C/GroupAtNums.lean), `request_links_in_scope`, `first_links_in_scope`
(Johnson/Goal/Numbers/RequestLinks.lean), `sized_of_made`, `first_of_made`
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean): number; the 25 · `bookHas_reached`
(Johnson/IMR/AtReach.lean), `front_len` (Johnson/IMR/FinPin.lean), `finishFrontQ_rest`
(Johnson/Top/H0/Tw/K2C/FinFront.lean), `finishFrontQ_size` (Johnson/Top/H0/Tw/K2C/StillKeeps.lean):
step · `closeFrame_sizes` (Johnson/Desc/First/Link/Law/CarriedSizes.lean): two masks · `frontAt_of`
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean)
· `stands` holds by unfolding. Sealed payers that are not called: of "each message that the reading
names is in the statement": `rows_sent_front` (Johnson/IMR/RowsSent.lean), for every copy of the
frame at every cut up to 353, and `closeFrame_sent` (Johnson/Desc/First/Close/Law/CarriedSent.lean);
of the two masks: `front_pin_fin` (Johnson/IMR/FinPin.lean).

Limits. THE PREMISES IN FRONT AND THE TESTS, OR THE HEAD, WITH THE TWO ON THE ENTRY AND `FinRest`,
ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. That the quiet front says yes at a reached state
is not shown. `mainVars`, `d0`, `d1` come by the tested road (`ShapeFits`), though
`fin_carried_free` (Returns/ArmsFree.lean) has them with no test. At the format's second hash function
alone. The full size alone. "Reached" is: over the list of the wrapped sub-protocols. This file's
imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.CallJoin
import Johnson.Desc.K2.Honest.Returns.ArmsFree
import Johnson.Desc.K2.Honest.Returns.ArmsPlan
import Johnson.Desc.K2.Honest.Returns.ClaimMainReached
import Johnson.Desc.K2.Honest.Returns.StoredArms
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.IMR.FinCount
import Johnson.Goal.Numbers.RequestLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S FinOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat finFrontOf frontAt_of
  finishFrontQ finishFrontQ_rest finishFrontQ_size)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.LinkJoin (closeFrame_sizes)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt sized_of_made first_of_made
  request_links_in_scope first_links_in_scope)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (front_nums_fin)
open P1K2 (Prep Nums numsAt prepOf sw_finish numsAt_grp prepOf_z)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- **What is left of `FinBehind` at a reached state.** t: the state behind the quiet front; c: the
old main code. -/
structure FinRest (p : P2) (t : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : FinOwn) (Q : ReqGroup) (c : Code) : Prop where
  call : CallRest p (finFrontOf t a Q) t.book t.roots r₁ r₂ (flat p gs) c t.check.frame.shape.code
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) t.book
    (treesOf (callIn p (finFrontOf t a Q) t.book t.roots r₁ r₂ (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **In scope the test on what is made gives the 25 segments.** -/
theorem h25_of_hy (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.shape.link.length = 25 :=
  first_links_in_scope hS O.pub (first_of_made hy)

/-- **What the payers deliver at the place's front.** -/
theorem fin_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none n.sent (par9 (k2P Z a' nm .finish n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀) :
    CallPaid (k2P Z a' nm .finish n) (finFrontOf t a Q) t.book r₁ r₂ c₀ ∧
      ∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a' nm .finish n).logN := by
  have h25 := h25_of_hy hS O hy
  have hfx : First.K2.frontAt (k2P Z a' nm .finish n) t = some (finFrontOf t a Q) :=
    frontAt_of (Or.inr (Or.inr ⟨rfl, a, Q, here, laid, rfl⟩))
  obtain ⟨d1, d2, d3, d4, d5⟩ :=
    finish_draws_plan hS hR O hF hpl h25 hP hn hr hq a' nm hfx r₁ r₂ he hrf
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr hq here
  obtain ⟨Gf, -, hm, -⟩ := closeFrame_sizes hx
  obtain ⟨m1, m2, m3⟩ := fin_members_reached hS hR O hr hq here Q
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length :=
    le_of_eq (Meaning.K2.front_len hS hR O).symm
  have H := stated_of_close hx hg
  rw [← hf] at H
  refine ⟨?_, d1⟩
  exact
    { entry := by rw [(sw_finish hS hR O hF hpl h25 a' nm hP hn hr hq).2 _ hfx]; exact he
      step := by
        show t.st.oracles.size = t.book.place.size
        rw [finishFrontQ_size hq, (finishFrontQ_rest hq).1]
        exact (Meaning.K2.bookHas_reached O (reach_raw hr) hlen).symm
      draw := d2, poss := d3, trits := d4, factor := d5
      oldCode := fin_oldCode_reached hS hR O hF hpl h25 hP hn hr hq here Q hc
      keptPos := fin_keptPos_reached hS hR O hF hpl h25 hP hn hr hq here laid
      masks := by
        show a.fr.rows.masks = 2
        rw [hf]
        exact hm
      lay := fin_lay_reached hS hR O hr hq here Q
      stated := H
      good := fin_goodS_reached hS hR O hF hpl h25 hP hn hr hq a Q
      shape := fin_shape_reached hS hR O hF hpl hy hcut hB hr hq here laid
      pub := fin_public_reached hS hR O hF hpl hy hcut hB hr hq here laid
      rows := m1, named := m2
      stored := fin_stored_reached hS hR O hF hpl h25 hP hn hr hq a Q
      claimKept := m3
      claimMain := fin_claimMain_reached hS hR O hr hq here Q }

/-- **`FinBehind.number` at a reached state.** -/
theorem fin_number_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q) :
    a.fr.group = (k2P Z a' nm .finish n).grp := by
  have hfx : First.K2.frontAt (k2P Z a' nm .finish n) t = some (finFrontOf t a Q) :=
    frontAt_of (Or.inr (Or.inr ⟨rfl, a, Q, here, laid, rfl⟩))
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  have e := (front_nums_fin hS hR O f₀ hq (q := (k2P Z a' nm .finish n)) rfl hfx).1
  show a.fr.group = n.grp
  rw [numsAt_grp hn]
  show a.fr.group = Pp.z.request.link.length
  rw [prepOf_z hP, request_links_in_scope hS O.pub (sized_of_made hy)]
  exact e

/-- **`FinBehind`, whole, at a reached state, from what is left.** -/
theorem fin_behind_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a' nm .finish n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (E : FinRest (k2P Z a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    FinBehind (k2P Z a' nm .finish n) s t r₁ r₂ gs a Q c₀ := by
  obtain ⟨Pd, d1⟩ :=
    fin_paid hS hR O hF hpl hy hcut hB hP hn hr hq a' nm r₁ r₂ he hrf here laid hc
  exact
    { quiet := hq, stands := rfl, range := d1, here := here
      number := fin_number_reached hS hR O hy hP hn hr hq a' nm here laid
      laid := laid, waits := fin_waits_reached hS hR O hr hq
      call := callCore_join Pd E.call, noneLeft := E.noneLeft, groups := E.groups }

/-- **So the kind's own decision says yes there.** -/
theorem fin_returns_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a' nm .finish n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (E : FinRest (k2P Z a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Z a' nm .finish n) t [r₁, r₂] gs = .ok s' :=
  finish_returns_behind
    (fin_behind_reached hS hR O hF hpl hy hcut hB hP hn hr hq a' nm r₁ r₂ gs he hrf here laid hc
      E)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}

/-- **The law whole, under the head alone, from what is left.** -/
theorem fin_behind_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Zp a' nm .finish n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Zp a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (E : FinRest (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    FinBehind (k2P Zp a' nm .finish n) s t r₁ r₂ gs a Q c₀ := by
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h O
  exact fin_behind_reached h.scope h.reads O h.laid.value h.laid.planOk hy hcut hB hP hn hr hq a'
    nm r₁ r₂ gs he hrf here laid hc E

/-- **And the decision's yes.** -/
theorem fin_returns_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Zp a' nm .finish n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Zp a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (E : FinRest (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .finish n) t [r₁, r₂] gs = .ok s' :=
  finish_returns_behind (fin_behind_at_head h O hP hn hr hq a' nm r₁ r₂ gs he hrf here laid hc E)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.h25_of_hy
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_number_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_behind_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_returns_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_behind_at_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_returns_at_head
