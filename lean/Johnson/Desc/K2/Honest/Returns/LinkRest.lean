-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/LinkRest.lean: UNDER THE ONE HEAD `P5J.AtMg`, AT A STATE THAT IS
REACHED IN FRONT OF THE SWITCH INTO A LATER GROUP, FIFTEEN CLAUSES (`LinkRest`), THE ENTRY's TEST AT
THE PLAN's OWN LIST AND ROUNDS THAT FIT GIVE THE LAW "THE KIND's OWN DECISION SAYS YES AT A
SEGMENT's FIRST PLACE" WHOLE (`LinkPlain`, Returns/LinkSent.lean), AND SO THE DECISION's YES.
Returns/LinkAtReached.lean's `LinkLeft` has sixteen; the sixteenth, `TablesFit.claimMain`, is paid
in Returns/ClaimMainReached.lean. A join. Statements with their proofs: calls.

  `LinkRest p s r₁ r₂ gs L Q c` `LinkLeft` without `claimMain`, field for field: six on the two
                    rounds and the columns (fits₁ · vals · answers · loc · noneLeft · groups) ·
                    `ReadFits.opens` and `own` · six on what the frame holds of the plan (plain ·
                    plan · trees · own · `FrontCore.groupCode` · copiesCode) · `FrontCore.inRange`
  `linkLeft_of_rest` in scope, at a reached state: `LinkRest` gives `LinkLeft`
  `link_plain_rest`, `link_returns_rest` the two tops under the head

THE COUNT. Of `LinkPlain`'s 67 clauses 52 are laid in by payers, under the head alone but for the
six that stand under the entry's test and the rounds that fit; 15 are `LinkRest`'s.

By: `link_claimMain_reached` (Returns/ClaimMainReached.lean) · `link_plain_at_head`,
`link_returns_at_head` (Returns/UnderHead.lean).

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE: NO MEMBER. `LinkRest`, the entry's test and the rounds
that fit stay premises. The opening is a premise in the head's own letters. The links' places alone.
At the format's second hash function alone. The full size alone. This file's imports are heavy. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.Desc.K2.Honest.Returns.ClaimMainReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat locOk behindArgs)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- **What is left of `LinkPlain` at a reached state**: `LinkLeft` without `claimMain`. c: the old
main code. -/
structure LinkRest (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) (c : Code) : Prop where
  plain : L.plain = 0
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  plan : K1.planOkOwn (sendingAt p (frontAt s L Q)) = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p (frontAt s L Q)) r₂)).length =
    (sendingAt p (frontAt s L Q)).answers
  trees : ((layTrees (sendingAt p (frontAt s L Q)).codes
    (sendingAt p (frontAt s L Q)).sent).getD {}).shapes.size = (par9 p).eSeed.roots
  loc : locOk (behindArgs (par9 p) (frontAt s L Q) (sentOf p s L Q r₁ r₂) r₂ (flat p gs)) c.logN =
    true
  readsOwn : ∀ t ∈ treesOf (readIn p s r₁ r₂ gs L Q), ∀ tree,
    (readIn p s r₁ r₂ gs L Q).book.trees[t]? = some tree →
    ∀ q ∈ tree.parts.toList, q ∈ (idsOf (readIn p s r₁ r₂ gs L Q)).toList
  readsOpens : AllOpen (readIn p s r₁ r₂ gs L Q).st (readIn p s r₁ r₂ gs L Q).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (readIn p s r₁ r₂ gs L Q).book
    (treesOf (readIn p s r₁ r₂ gs L Q)) (readIn p s r₁ r₂ gs L Q).opened
  inRange : ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
    v < 2 ^ ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logN
  groupCode : (frontAt s L Q).T.shape.code = s.check.frame.shape.code
  copiesCode : ∀ k ∈ (frontAt s L Q).T.kept.toList, k.shape.code = s.check.frame.shape.code
  own : ∀ (j : Nat) (m : Params.ReqMessage), (frontAt s L Q).own[j]? = some m →
    ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
      (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
      (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
      (0 < m.life → 0 < n.shape.mainRows)
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (readIn p s r₁ r₂ gs L Q))
    (flat p gs) = []
  groups : gs.length = p.read.length

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

theorem linkLeft_of_rest (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {p : P2} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {L : Params.ReqLink}
    {Q : ReqGroup} {c₀ : Code} (E : LinkRest p s r₁ r₂ gs L Q c₀) :
    LinkLeft p s r₁ r₂ gs L Q c₀ :=
  { plain := E.plain
    fits₁ := E.fits₁
    plan := E.plan
    vals := E.vals
    answers := E.answers
    trees := E.trees
    loc := E.loc
    readsOwn := E.readsOwn
    readsOpens := E.readsOpens
    inRange := E.inRange
    groupCode := E.groupCode
    copiesCode := E.copiesCode
    claimMain := link_claimMain_reached hS hR O h23 hr L Q
    own := E.own
    noneLeft := E.noneLeft
    groups := E.groups }

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}

/-- **The law whole, under the head alone, from the fifteen.** -/
theorem link_plain_rest (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : LinkRest (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ :=
  link_plain_at_head h O h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc hz
    (linkLeft_of_rest h.scope h.reads O h23 hr E)

/-- **And the decision's yes.** -/
theorem link_returns_rest (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : LinkRest (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂] gs = .ok s' :=
  link_returns_at_head h O h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc
    (linkLeft_of_rest h.scope h.reads O h23 hr E)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.linkLeft_of_rest
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_rest
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_rest
