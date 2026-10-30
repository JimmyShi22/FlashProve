-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/UnderHead.lean: THE THREE NAMED TESTS ON THE PUBLIC PART UNDER WHICH
Returns/PinReached.lean, Returns/PinArms.lean, Returns/PinPublic.lean AND Returns/LinkAtReached.lean
STAND (hy · hcut · hB) ARE TWO IN THE GOALS' SCOPE, AND NONE UNDER THE ONE HEAD `P5J.AtMg`: THE
LIBRARY PAYS THEM. SO, UNDER THAT HEAD ALONE, AT A STATE REACHED IN FRONT OF THE SWITCH INTO A LATER
GROUP, WHAT IS LEFT (`LinkLeft`) GIVES THE LAW WHOLE (`LinkPlain`), AND THE KIND's OWN DECISION
RETURNS. Statements with their proofs: calls.

  `hB_of_hy` in scope, where the description passes its test on the plan: hy gives hB
  `link_plain_two`, `link_returns_two` `link_plain_reached`, `link_returns_reached` without hB
  `tests_at_head` under the head, at every opening of its own letters: hy, hcut and hB
  `link_plain_at_head`, `link_returns_at_head` the two tops under the head: the five premises in
                    front are the head's own fields; no test is left

By, all the library's: `madeRow_in_scope` (Johnson/LTPileR/SeatsOneTest.lean) ·
`sendsAre_of_madeRow` (Johnson/IMR/AtReachFits.lean) · `AtMg.pins` (Johnson/P5T/FenceAtMg.lean) ·
`pinnedAt_row` (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) · `key_in_scope_pure`
(Johnson/Goal/Numbers/KeyInScope.lean) · `cut_of_row`
(Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean). Near relatives, not called: `hB_paid`
(Johnson/IMR/EndFiveMade.lean), `Sh.row_in_scope`
(Johnson/Desc/K14/Law/SharedConstReachClosed.lean): the two steps of `hB_of_hy` in other letters ·
`cut_of_head` (Johnson/Road/K4/K4HeadWritten.lean), `pins_at_head`
(Johnson/Desc/First/Att/Door/Law/K5CondOfHead.lean): hcut under the head.

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE: NO MEMBER. `LinkLeft`, the entry's test at the plan's
own list and the rounds that fit stay premises. The opening is a premise in the head's own letters;
that there is one is the head's field `laid.opened`. The head's word `TS` for the state's type is
`S` by unfolding. The links' places alone. At the format's second hash function alone. The full size alone.
This file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.LinkAtReached
import Johnson.LTPileR.SeatsOneTest
import Johnson.IMR.AtReachFits
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (decideWith rounds par9)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt pinnedAt_row key_in_scope_pure
  cut_of_row)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (madeRow_in_scope sendsAre_of_madeRow)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **In scope the test on the sendings follows from the test on what is made.** -/
theorem hB_of_hy (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true :=
  sendsAre_of_madeRow hS hR O hpl (madeRow_in_scope hS O.pub hy)

/-- `link_plain_reached` under two tests. -/
theorem link_plain_two (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a nm .link n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hz : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (E : LinkLeft (k2P Z a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Z a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ :=
  link_plain_reached hS hR O hF hpl hy hcut (hB_of_hy hS hR O hpl hy) h23 hP hn hr a nm r₁ r₂ gs he
    hrf hL hQ hc hz E

/-- `link_returns_reached` under two tests. -/
theorem link_returns_two (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a nm .link n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : LinkLeft (k2P Z a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Z a nm .link n) s [r₁, r₂] gs = .ok s' :=
  link_returns_reached hS hR O hF hpl hy hcut (hB_of_hy hS hR O hpl hy) h23 hP hn hr a nm r₁ r₂ gs
    he hrf hL hQ hc E

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}

/-- **Under the head all three tests accept.** -/
theorem tests_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true ∧
      VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull ∧
      sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true := by
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Zp := h.laid.pub
  refine ⟨?_, (cut_of_row h.pins.2).1, sendsAre_of_madeRow h.scope h.reads O h.laid.planOk h.pins.1⟩
  rw [pinnedAt_row, if_pos (key_in_scope_pure h.scope hZ)]
  exact h.pins.1

/-- **The law whole, under the head alone, from what is left.** -/
theorem link_plain_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Zp a nm .link n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hz : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (E : LinkLeft (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ := by
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h O
  exact link_plain_reached h.scope h.reads O h.laid.value h.laid.planOk hy hcut hB h23 hP hn hr a nm
    r₁ r₂ gs he hrf hL hQ hc hz E

/-- **And the decision's yes.** -/
theorem link_returns_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Zp a nm .link n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : LinkLeft (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂] gs = .ok s' := by
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h O
  exact link_returns_reached h.scope h.reads O h.laid.value h.laid.planOk hy hcut hB h23 hP hn hr a
    nm r₁ r₂ gs he hrf hL hQ hc E

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.hB_of_hy
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_two
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_two
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tests_at_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_at_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_at_head
