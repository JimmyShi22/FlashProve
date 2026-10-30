-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/LinkProver.lean: THE CODE SWITCH's RETURNS LAW, WHOLE, AT A STATE
THAT IS REACHED IN FRONT OF THE SWITCH INTO A LATER GROUP, UNDER THE ONE HEAD `P5J.AtMgA`, FROM
SEVEN CLAUSES THAT NAME THE PROVER's TWO ROUNDS OR THE COLUMNS (`LinkSeven`) AND "THE ROUNDS FIT",
AT ALL 23 SUCH SWITCHES. A join of Returns/LeftAtReached.lean and Returns/OwnFirst.lean with files
of another house. Statements with their proofs: calls.

  `LinkEight p s r₁ r₂ gs L Q c` `LinkLast` (Returns/LeftAtReached.lean) without plain, plan, trees,
                    inRange and own, field for field: fits₁ · vals · answers · loc · readsOwn ·
                    readsOpens · noneLeft · groups
  `LinkSeven p s r₁ r₂ gs L Q c` the same without readsOwn
  `linkLast_of_eight` under the head, the rounds that fit and the state's own look-ups: `LinkEight`
                    gives `LinkLast`, and the entry's test at the plan's own list holds
  `link_plain_eight`, `link_returns_eight` m < 23: `LinkPlain`; the kind's own decision's yes
  `link_plain_seven`, `link_returns_seven` m < 23: the same from `LinkSeven`

THE COUNT. Of `LinkPlain`'s 67 clauses 60 are laid in by payers; SEVEN are left. The entry's test is
a premise no more.

ANOTHER HOUSE's, CALLED: `link_two_reached` (plain · own), `link_plan_reached`
(Johnson/AtFull/Shape/LinkLeftPlan.lean) · `link_trees_reached`, `link_entry_reached`,
`link_inRange_reached` (Johnson/AtFull/Shape/LinkLeftNums.lean). BY THAT HOUSE's OWN PAPERS: the two
files called have that house's ride of record at the bytes that it has lined for the next sealed
library; each was read whole, proofs too, once, in its first issue, by one reader of that house who
is not its pen, and since by difference (an import line and comments have turned): neither whole at
the lined bytes; they decide eight closed facts by Lean's kernel under a raised recursion limit
(four of them controls); both strike the instance `Inst.Model.Scl.ref`; two of the five stand at the
raw flat list; they stand over two more files of that house (Johnson/AtFull/Shape/PlansAtHead.lean,
AtSwitchReached.lean), lined too; the second was read whole, the proof too, by that same reader, and
since by difference. NONE OF THE FOUR IS IN A SEALED LIBRARY YET. This folder's: `link_plain_last`,
`link_returns_last` (Returns/LeftAtReached.lean) · `link_own_all` (Returns/OwnFirst.lean) ·
`link_draws_own` (Returns/FirstReached.lean): the range of the positions drawn. The library's
`reach_raw` (Johnson/Top/H0/Walk/Reach.lean).

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE: NO MEMBER. THE HEAD IS `P5J.AtMgA`, WHICH ASKS MORE
THAN THE `P5J.AtMg` OF THIS FOLDER's OTHER TOPS. The seven and the rounds that fit stay premises.
THE SEVEN ARE NOT ON THE ROUNDS AND THE COLUMNS ALONE: readsOpens asks four facts a tree of the
verifier's state; answers and loc hold three ties of the plan's numbers. The links alone: nothing at
the two other sorts of place. The opening is a premise in the head's own letters. At the format's
second hash function alone. The full size alone. This file's imports are heavy. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.LeftAtReached
import Johnson.Desc.K2.Honest.Returns.OwnFirst
import Johnson.AtFull.Shape.LinkLeftNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat locOk behindArgs)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.AtFull.Shape (link_two_reached link_plan_reached link_trees_reached
  link_entry_reached link_inRange_reached)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- **What is left at a link when the plan's clauses are paid.** c: the old main code. -/
structure LinkEight (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) (c : Code) : Prop where
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p (frontAt s L Q)) r₂)).length =
    (sendingAt p (frontAt s L Q)).answers
  loc : locOk (behindArgs (par9 p) (frontAt s L Q) (sentOf p s L Q r₁ r₂) r₂ (flat p gs)) c.logN =
    true
  readsOwn : ∀ t ∈ treesOf (readIn p s r₁ r₂ gs L Q), ∀ tree,
    (readIn p s r₁ r₂ gs L Q).book.trees[t]? = some tree →
    ∀ q ∈ tree.parts.toList, q ∈ (idsOf (readIn p s r₁ r₂ gs L Q)).toList
  readsOpens : AllOpen (readIn p s r₁ r₂ gs L Q).st (readIn p s r₁ r₂ gs L Q).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (readIn p s r₁ r₂ gs L Q).book
    (treesOf (readIn p s r₁ r₂ gs L Q)) (readIn p s r₁ r₂ gs L Q).opened
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (readIn p s r₁ r₂ gs L Q))
    (flat p gs) = []
  groups : gs.length = p.read.length

/-- **The seven that name the prover's two rounds or the columns.** c: the old main code. -/
structure LinkSeven (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) (c : Code) : Prop where
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p (frontAt s L Q)) r₂)).length =
    (sendingAt p (frontAt s L Q)).answers
  loc : locOk (behindArgs (par9 p) (frontAt s L Q) (sentOf p s L Q r₁ r₂) r₂ (flat p gs)) c.logN =
    true
  readsOpens : AllOpen (readIn p s r₁ r₂ gs L Q).st (readIn p s r₁ r₂ gs L Q).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (readIn p s r₁ r₂ gs L Q).book
    (treesOf (readIn p s r₁ r₂ gs L Q)) (readIn p s r₁ r₂ gs L Q).opened
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (readIn p s r₁ r₂ gs L Q))
    (flat p gs) = []
  groups : gs.length = p.read.length

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **`LinkEight` gives `LinkLast`, and the entry's test holds.** -/
theorem linkLast_of_eight (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (E : LinkEight (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    planOk1 none n.sent (par9 (k2P Zp a nm .link n)).eSeed = true ∧
      LinkLast (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀ := by
  have he := link_entry_reached h O h23 hP hn hr a nm hL hQ
  obtain ⟨_, -, d1, -⟩ := link_draws_own h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr
    a nm r₁ r₂ he hrf
  have two := link_two_reached h h23 (reach_raw hr) Q hL
  exact ⟨he,
      { plain := two.1
        fits₁ := E.fits₁
        plan := link_plan_reached h h23 (reach_raw hr) _ L hQ
        vals := E.vals
        answers := E.answers
        trees := link_trees_reached h O h23 hP hn hr a nm hL hQ
        loc := E.loc
        readsOwn := E.readsOwn
        readsOpens := E.readsOpens
        inRange := link_inRange_reached h O h23 hP hn hr r₂ d1 L Q c₀
        own := two.2
        noneLeft := E.noneLeft
        groups := E.groups }⟩

theorem link_plain_eight (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hz : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (E : LinkEight (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ := by
  obtain ⟨he, E'⟩ := linkLast_of_eight h O h23 hP hn hr a nm r₁ r₂ gs hrf hL hQ E
  exact link_plain_last h.toAtMg O h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc hz E'

theorem link_returns_eight (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : LinkEight (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂] gs = .ok s' := by
  obtain ⟨he, E'⟩ := linkLast_of_eight h O h23 hP hn hr a nm r₁ r₂ gs hrf hL hQ E
  exact link_returns_last h.toAtMg O h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc E'

/-- **The law whole at every switch into a later group, from the seven.** -/
theorem link_plain_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hz : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (E : LinkSeven (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ :=
  link_plain_eight h O h23 hP hn hr a nm r₁ r₂ gs hrf hL hQ hc hz
    { fits₁ := E.fits₁
      vals := E.vals
      answers := E.answers
      loc := E.loc
      readsOwn := link_own_all h.scope h.reads O h23 hr L Q _ _ _ _
      readsOpens := E.readsOpens
      noneLeft := E.noneLeft
      groups := E.groups }

theorem link_returns_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : LinkSeven (k2P Zp a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂] gs = .ok s' :=
  link_returns_eight h O h23 hP hn hr a nm r₁ r₂ gs hrf hL hQ hc
    { fits₁ := E.fits₁
      vals := E.vals
      answers := E.answers
      loc := E.loc
      readsOwn := link_own_all h.scope h.reads O h23 hr L Q _ _ _ _
      readsOpens := E.readsOpens
      noneLeft := E.noneLeft
      groups := E.groups }

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.linkLast_of_eight
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_eight
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_eight
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_seven
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_seven
