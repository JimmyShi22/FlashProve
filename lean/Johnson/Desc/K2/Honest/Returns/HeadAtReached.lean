-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/HeadAtReached.lean: THE LAW "THE KIND's OWN DECISION SAYS YES AT THE
OUTPUT HEAD's PLACE" (`HeadBehind`, Returns/ArmsBehind.lean), WHOLE, AT A STATE THAT IS REACHED IN
FRONT OF THE OUTPUT HEAD's SWITCH (NUMBER 339), AT THE NUMBERS THAT THE PLAN's OWN MAKER LAYS FOR
THE PLACE, FROM WHAT IS LEFT (`HeadRest`: thirteen clauses): UNDER THE PREMISES IN FRONT AND THREE
NAMED TESTS ON THE PUBLIC PART, AND UNDER THE ONE HEAD `P5J.AtMg` ALONE. SO THE KIND's OWN DECISION
RETURNS THERE. What Returns/LinkAtReached.lean, Returns/UnderHead.lean and Returns/LinkRest.lean
have at the links. A join. Statements with their proofs: calls.

  `head_paid` `CallPaid` (Returns/CallJoin.lean) at the head's front, and the range of the positions
                    drawn
  `head_number_reached` `HeadBehind.number`: the head's own frame's group is the plan's number
  `HeadRest p s r₁ r₂ gs a Q c` WHAT IS LEFT: `CallRest`'s eleven at the head's front · noneLeft ·
                    groups
  `head_behind_reached`, `head_returns_reached` FOR ALL a, Q, c₀ that are the state's own (three
                    look-ups: `s.here = .head a`; the frame's group at its segment; the code that
                    stands in the statement's list at the frame's shape's code): `HeadRest` gives
                    `HeadBehind`; and so the decision's yes
  `head_behind_at_head`, `head_returns_at_head` the same under the head alone: no test

THE COUNT. `HeadBehind` laid open has 60 clauses: ten of its own and the call's 50. 45 are laid in
by payers; two are look-ups (here · group); 13 are `HeadRest`'s. Of the 45, fifteen stand under the
three tests as typed (under the head: under nothing more), six under the entry's test and the rounds
that fit.

WHO PAYS WHAT. `group_reached` (Returns/ArmsReached.lean): fresh · code · `head_waits_reached`
(Returns/ArmsFree.lean) · `head_oldCode_reached`, `head_keptPos_reached` (Returns/ArmsPlan.lean) ·
`head_draws_plan` (Returns/LinkReached.lean): range and four on the draws · `head_lay_reached`,
`head_members_reached`, `head_closed_reached` (Returns/ClosedArms.lean) · `stated_of_close`
(Returns/MembersReached.lean) · `head_claimMain_reached` (Returns/ClaimMainReached.lean) ·
`head_goodS_reached`, `head_stored_reached` (Returns/StoredArms.lean) · `head_shape_reached`
(Returns/PinArms.lean) · `head_public_reached` (Returns/PinPublic.lean) · `tests_at_head`
(Returns/UnderHead.lean) · the library's `sw_head` (Johnson/P1K2R/HstReached.lean): the entry's test
is led from the plan's own list to the front's notices · `front_nums_head`
(Johnson/IMR/HeadFront.lean), `numsAt_grp` (Johnson/Top/H0/Tw/K2C/GroupAtNums.lean): number ·
`bookHas_reached` (Johnson/IMR/AtReach.lean), `front_len` (Johnson/IMR/FinPin.lean): step ·
`closeFrame_sizes` (Johnson/Desc/First/Link/Law/CarriedSizes.lean): two masks · `frontAt_of`
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean) · `fold_back` (Johnson/IMR/FoldTools.lean) · `reach_raw`,
`Reach.fold` (Johnson/Top/H0/Walk/Reach.lean) · `stands` holds by unfolding. Sealed payers that are
not called: of "each message that the reading names is in the statement": `rows_sent_front`
(Johnson/IMR/RowsSent.lean), for every copy of the frame at every cut up to 353, and
`closeFrame_sent` (Johnson/Desc/First/Close/Law/CarriedSent.lean); of the two masks:
`front_pin_head` (Johnson/IMR/FrontPin.lean).

Limits. THE PREMISES IN FRONT AND THE TESTS, OR THE HEAD, WITH THE TWO ON THE ENTRY AND `HeadRest`,
ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. That there is an a: `head_here_reached`
(Returns/LinkReached.lean). `mainVars`, `d0`, `d1` come by the tested road (`ShapeFits`), though
`head_carried_free` (Returns/ArmsFree.lean) has them with no test. At the format's second hash function
alone. The full size alone. "Reached" is: over the list of the wrapped sub-protocols. This file's
imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.CallJoin
import Johnson.Desc.K2.Honest.Returns.ArmsFree
import Johnson.Desc.K2.Honest.Returns.ArmsPlan
import Johnson.Desc.K2.Honest.Returns.ArmsReached
import Johnson.Desc.K2.Honest.Returns.ClaimMainReached
import Johnson.Desc.K2.Honest.Returns.StoredArms
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.IMR.HeadFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat headFrontOf frontAt_of)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.LinkJoin (closeFrame_sizes)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (front_nums_head fold_back)
open P1K2 (Prep Nums numsAt prepOf sw_head numsAt_grp)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- **What is left of `HeadBehind` at a reached state.** c: the old main code. -/
structure HeadRest (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : HeadOwn) (Q : ReqGroup) (c : Code) : Prop where
  call : CallRest p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) c
    s.check.frame.shape.code
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (callIn p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs)))
    (flat p gs) = []
  groups : gs.length = p.read.length

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **What the payers deliver at the head's front.** -/
theorem head_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none n.sent (par9 (k2P Z a' nm .head n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) :
    CallPaid (k2P Z a' nm .head n) (headFrontOf s a Q.target) s.book r₁ r₂ c₀ ∧
      ∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a' nm .head n).logN := by
  have hfx : First.K2.frontAt (k2P Z a' nm .head n) s = some (headFrontOf s a Q.target) :=
    frontAt_of (Or.inr (Or.inl ⟨rfl, a, Q, here, group, rfl⟩))
  obtain ⟨d1, d2, d3, d4, d5⟩ := head_draws_plan hS hR O hF hpl hP hn hr a' nm hfx r₁ r₂ he hrf
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  obtain ⟨Gf, -, hm, -⟩ := closeFrame_sizes hx
  obtain ⟨m1, m2, m3⟩ := head_members_reached hS hR O hr here Q.target
  have hlen : 339 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have H := stated_of_close hx hg
  rw [← hf] at H
  refine ⟨?_, d1⟩
  exact
    { entry := by rw [(sw_head hS hR O hF hpl a' nm hP hn hr).2 _ hfx]; exact he
      step := (Meaning.K2.bookHas_reached O (reach_raw hr) hlen).symm
      draw := d2, poss := d3, trits := d4, factor := d5
      oldCode := head_oldCode_reached hS hR O hF hpl hP hn hr here Q.target hc
      keptPos := head_keptPos_reached hS hR O hF hpl hP hn hr a group
      masks := by
        show a.fr.rows.masks = 2
        rw [hf]
        exact hm
      lay := head_lay_reached hS hR O hr here Q.target
      stated := H
      good := head_goodS_reached hS hR O hF hpl hP hn hr a Q.target
      shape := head_shape_reached hS hR O hF hpl hy hcut hB hr here group
      pub := head_public_reached hS hR O hF hpl hy hcut hB hr here group
      rows := m1, named := m2
      stored := head_stored_reached hS hR O hF hpl hP hn hr a Q.target
      claimKept := m3
      claimMain := head_claimMain_reached hS hR O hr here Q.target }

/-- **`HeadBehind.number` at a reached state.** -/
theorem head_number_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    {lay : ByteArray} (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Prep} {n : Nums} (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) (a' : Place) (nm : String)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    a.fr.group = (k2P Z a' nm .head n).grp := by
  have hfx : First.K2.frontAt (k2P Z a' nm .head n) s = some (headFrontOf s a Q.target) :=
    frontAt_of (Or.inr (Or.inl ⟨rfl, a, Q, here, group, rfl⟩))
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  have e := (front_nums_head hS hR O fm f₀ (q := (k2P Z a' nm .head n)) rfl hfx).1
  show a.fr.group = n.grp
  rw [numsAt_grp hn]
  exact e

/-- **`HeadBehind`, whole, at a reached state, from what is left.** -/
theorem head_behind_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a' nm .head n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : HeadRest (k2P Z a' nm .head n) s r₁ r₂ gs a Q c₀) :
    HeadBehind (k2P Z a' nm .head n) s r₁ r₂ gs a Q c₀ := by
  obtain ⟨Pd, d1⟩ :=
    head_paid hS hR O hF hpl hy hcut hB hP hn hr a' nm r₁ r₂ he hrf here group hc
  obtain ⟨g1, g2⟩ := group_reached hS hR O s (reach_raw hr)
  exact
    { fresh := g1, code := g2, stands := rfl, range := d1, here := here
      number := head_number_reached hS hR O hn hr a' nm here group
      group := group, waits := head_waits_reached hS hR O hr
      call := callCore_join Pd E.call, noneLeft := E.noneLeft, groups := E.groups }

/-- **So the kind's own decision says yes there.** -/
theorem head_returns_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a' nm .head n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : HeadRest (k2P Z a' nm .head n) s r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Z a' nm .head n) s [r₁, r₂] gs = .ok s' :=
  head_returns_behind
    (head_behind_reached hS hR O hF hpl hy hcut hB hP hn hr a' nm r₁ r₂ gs he hrf here group hc E)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}

/-- **The law whole, under the head alone, from what is left.** -/
theorem head_behind_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Zp a' nm .head n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Zp a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : HeadRest (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    HeadBehind (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀ := by
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h O
  exact head_behind_reached h.scope h.reads O h.laid.value h.laid.planOk hy hcut hB hP hn hr a' nm
    r₁ r₂ gs he hrf here group hc E

/-- **And the decision's yes.** -/
theorem head_returns_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Zp a' nm .head n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Zp a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : HeadRest (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .head n) s [r₁, r₂] gs = .ok s' :=
  head_returns_behind (head_behind_at_head h O hP hn hr a' nm r₁ r₂ gs he hrf here group hc E)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_number_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_behind_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_returns_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_behind_at_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_returns_at_head
