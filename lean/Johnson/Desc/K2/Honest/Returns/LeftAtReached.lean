-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/LeftAtReached.lean: THE CODE SWITCH's RETURNS LAW, WHOLE, AT A
REACHED STATE, AT ALL THREE SORTS OF PLACE, UNDER THE ONE HEAD `P5J.AtMg` ALONE, FROM WHAT IS LEFT
WHEN `FrontCore.groupCode` AND `copiesCode` ARE PAID TOO (Returns/TargetReached.lean): THIRTEEN
CLAUSES AT A LINK (`LinkLast`), ELEVEN AT EACH OF THE TWO OTHER PLACES (`HeadLast`, `FinLast`).
Joins over Returns/LinkRest.lean, Returns/HeadAtReached.lean, Returns/FinAtReached.lean. Statements
with their proofs: calls.

  `CallLast p x B roots r₁ r₂ cols c` `CallRest` (Returns/CallJoin.lean) without groupCode and
                    copiesCode, field for field: NINE: five on the two rounds and the columns (fits₁
                    · vals · answers · loc · `ReadFits.opens`) · `ReadFits.own` · two on what the
                    front holds of the plan (plan · trees) · `FrontCore.inRange`
  `callRest_of_last` with the two clauses it gives `CallRest`
  `LinkLast p s r₁ r₂ gs L Q c` `LinkRest` without the two, field for field: THIRTEEN: the nine in
                    the link's letters · plain · own · noneLeft · groups
  `HeadLast`, `FinLast` `CallLast` at the place's front · noneLeft · groups: ELEVEN
  `link_plain_last`, `link_returns_last`, `head_behind_last`, `head_returns_last`,
                    `fin_behind_last`, `fin_returns_last` the six tops, each FOR ALL letters that
                    are the state's own look-ups

THE COUNT. Links: of `LinkPlain`'s 67 clauses 54 are laid in by payers, 13 are left. The output
head's place: of `HeadBehind`'s 60: 47 · two look-ups · 11. Behind the last segment: of
`FinBehind`'s 59: 45 · three look-ups · 11.

By, this folder's: `link_target_reached`, `head_target_reached`, `fin_target_reached`
(Returns/TargetReached.lean) · `link_plain_rest`, `link_returns_rest` (Returns/LinkRest.lean) ·
`head_behind_at_head` (Returns/HeadAtReached.lean) · `fin_behind_at_head`, `h25_of_hy`
(Returns/FinAtReached.lean) · `tests_at_head` (Returns/UnderHead.lean) · `head_returns_behind`,
`finish_returns_behind` (Returns/ArmsBehind.lean).

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE: NO MEMBER. What is left, the entry's test at the
plan's own list and the rounds that fit stay premises; at the third place the quiet front's yes too.
The opening is a premise in the head's own letters. Nine structures of this folder now say "what is
left" (`LinkLeft`, `LinkRest`, `LinkLast`; `CallRest`, `CallLast`; and two pairs at the arms): each
elder one was frozen when the next payer came. At the format's second hash function alone. The full size
alone. This file's imports are heavy. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.TargetReached
import Johnson.Desc.K2.Honest.Returns.LinkRest
import Johnson.Desc.K2.Honest.Returns.HeadAtReached
import Johnson.Desc.K2.Honest.Returns.FinAtReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat locOk behindArgs headFrontOf
  finFrontOf finishFrontQ)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Front Col sendByL8)
open ProofFile (Cl)

/-- **What is left of the call**: `CallRest` without groupCode and copiesCode. c: the old main
code. -/
structure CallLast (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (c : Code) : Prop where
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  plan : K1.planOkOwn (sendingAt p x) = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p x) r₂)).length = (sendingAt p x).answers
  trees : ((layTrees (sendingAt p x).codes (sendingAt p x).sent).getD {}).shapes.size =
    (par9 p).eSeed.roots
  loc : locOk (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols) c.logN =
    true
  readsOwn : ∀ t ∈ treesOf (callIn p x B roots r₁ r₂ cols), ∀ tree,
    (callIn p x B roots r₁ r₂ cols).book.trees[t]? = some tree →
    ∀ q ∈ tree.parts.toList, q ∈ (idsOf (callIn p x B roots r₁ r₂ cols)).toList
  readsOpens : AllOpen (callIn p x B roots r₁ r₂ cols).st (callIn p x B roots r₁ r₂ cols).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (callIn p x B roots r₁ r₂ cols).book
    (treesOf (callIn p x B roots r₁ r₂ cols)) (callIn p x B roots r₁ r₂ cols).opened
  inRange : ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
    v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN

theorem callRest_of_last {p : P2} {x : Front} {B : TreeBook} {roots : Nat} {r₁ r₂ : Fmt.RoundView}
    {cols : List OpenedColumn} {c : Code} {code : Nat} (E : CallLast p x B roots r₁ r₂ cols c)
    (g : x.T.shape.code = code) (k : ∀ k ∈ x.T.kept.toList, k.shape.code = code) :
    CallRest p x B roots r₁ r₂ cols c code :=
  { fits₁ := E.fits₁
    plan := E.plan
    vals := E.vals
    answers := E.answers
    trees := E.trees
    loc := E.loc
    readsOwn := E.readsOwn
    readsOpens := E.readsOpens
    inRange := E.inRange
    groupCode := g
    copiesCode := k }

/-- **What is left at a link**: `LinkRest` without groupCode and copiesCode. c: the old main
code. -/
structure LinkLast (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
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
  own : ∀ (j : Nat) (m : Params.ReqMessage), (frontAt s L Q).own[j]? = some m →
    ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
      (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
      (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
      (0 < m.life → 0 < n.shape.mainRows)
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (readIn p s r₁ r₂ gs L Q))
    (flat p gs) = []
  groups : gs.length = p.read.length

/-- **What is left at the output head's place.** -/
structure HeadLast (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : HeadOwn) (Q : ReqGroup) (c : Code) : Prop where
  call : CallLast p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) c
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (callIn p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs)))
    (flat p gs) = []
  groups : gs.length = p.read.length

/-- **What is left behind the last segment.** t: the state behind the quiet front. -/
structure FinLast (p : P2) (t : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : FinOwn) (Q : ReqGroup) (c : Code) : Prop where
  call : CallLast p (finFrontOf t a Q) t.book t.roots r₁ r₂ (flat p gs) c
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) t.book
    (treesOf (callIn p (finFrontOf t a Q) t.book t.roots r₁ r₂ (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}

/-- **The law whole at a link, under the head alone, from the thirteen.** -/
theorem link_plain_last (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : LinkLast (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ := by
  obtain ⟨-, -, g, k⟩ :=
    link_target_reached h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr L hQ
  exact link_plain_rest h O h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc hz
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
      groupCode := g
      copiesCode := k
      own := E.own
      noneLeft := E.noneLeft
      groups := E.groups }

theorem link_returns_last (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : LinkLast (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂] gs = .ok s' := by
  obtain ⟨-, -, g, k⟩ :=
    link_target_reached h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr L hQ
  exact link_returns_rest h O h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc
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
      groupCode := g
      copiesCode := k
      own := E.own
      noneLeft := E.noneLeft
      groups := E.groups }

theorem head_behind_last (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : HeadLast (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    HeadBehind (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀ := by
  obtain ⟨-, -, g, k⟩ :=
    head_target_reached h.scope h.reads O h.laid.value h.laid.planOk hP hn hr a group
  exact head_behind_at_head h O hP hn hr a' nm r₁ r₂ gs he hrf here group hc
    { call := callRest_of_last E.call g k, noneLeft := E.noneLeft, groups := E.groups }

theorem head_returns_last (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : HeadLast (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .head n) s [r₁, r₂] gs = .ok s' :=
  head_returns_behind (head_behind_last h O hP hn hr a' nm r₁ r₂ gs he hrf here group hc E)

theorem fin_behind_last (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : FinLast (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    FinBehind (k2P Zp a' nm .finish n) s t r₁ r₂ gs a Q c₀ := by
  have h25 := h25_of_hy h.scope O (tests_at_head h O).1
  obtain ⟨-, -, g, k⟩ :=
    fin_target_reached h.scope h.reads O h.laid.value h.laid.planOk h25 hP hn hr hq here laid
  exact fin_behind_at_head h O hP hn hr hq a' nm r₁ r₂ gs he hrf here laid hc
    { call := callRest_of_last E.call g k, noneLeft := E.noneLeft, groups := E.groups }

theorem fin_returns_last (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
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
    (E : FinLast (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .finish n) t [r₁, r₂] gs = .ok s' :=
  finish_returns_behind (fin_behind_last h O hP hn hr hq a' nm r₁ r₂ gs he hrf here laid hc E)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.callRest_of_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_behind_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_returns_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_behind_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_returns_last
