-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TiedReached.lean: THE PREMISE ON THE TREES OF THE CODE SWITCH's OWN
DECISION's YES (`AllTied`, Returns/ColsFit.lean: seven things a tree, along the opened messages'
trees and the plan's list of read trees), AT A REACHED STATE, AT ALL 25 OF THE KIND's PLACES, UNDER
THE ONE HEAD `P5J.AtMg`, FROM ONE THING A TREE: `leafOk`. SIX OF THE SEVEN ARE PAID. A join of
Returns/FiveReached.lean (five) with Returns/UnopenedFirst.lean, UnopenedLinks.lean and
UnopenedFinish.lean ("a tree of one list has not been opened"). Statements with their proofs: calls.

  `allTied_of` `AllFive ft pos.logN B0 ts rd` · of each tree of ts that stands in the book: `leafOk`
                    and `lists` = 0 ⊢ `AllTied S ft pos B0 ts rd`
  `six_at_head` under the head: the six premises of Returns/FiveReached.lean, and that the codes are
                    the written ones
  `depth_written` the old main code's depth is the written one, where the state's codes and its
                    frame's shape are the public part's
  `link_tied_reached`, `head_tied_reached`, `fin_tied_reached` THE TOPS: every m < 23 | 339 | 353
                    behind the quiet front's yes: for all rounds, columns and draws: `leafOk` at the
                    front's statement of every tree among `treesOf` that stands in the book ⊢
                    `AllTied`, in the letters of the tops of the join over
                    Returns/LinkProver.lean and Returns/ArmsProver.lean

By, this folder's: `link_five_reached`, `head_five_reached`, `fin_five_reached`, `logW_of`
(Returns/FiveReached.lean) · `link_unopened_all` (Returns/UnopenedFirst.lean),
`head_unopened_reached` (Returns/UnopenedLinks.lean), `fin_unopened_reached`
(Returns/UnopenedFinish.lean) · `tests_at_head` (Returns/UnderHead.lean) · `AllTied`, `TreeTied`
(Returns/ColsFit.lean), `readIn` (Returns/LinkAtReached.lean), `callIn` (Returns/CallJoin.lean). The
library's: `written3` (Johnson/P1K2R/HT1Tight.lean) · `AtMg.laid_codes_at_head`
(Johnson/P5J/PlanSitsCore.lean) · `pub_firstTree` (Johnson/IMR/SeatKeeps.lean) · `recAll_reached`
(Johnson/IMR/AtReach.lean) · `finishFrontQ_codes` (Johnson/Top/H0/Tw/K2C/KeepsWhole.lean),
`finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) · `front_len` (Johnson/IMR/FinPin.lean) ·
`reach_raw` (Johnson/Top/H0/Walk/Reach.lean).

Limits. `leafOk` STAYS A PREMISE. No statement of it at a reached state of the first chain is
other houses' word to us and our own search of the two sealed libraries' texts for its name and
Johnson/Top/H0/Tw/K2C/Asks.lean; its text stands under another
name, `sharesOk` (Johnson/Prover/Link/ReadFront.lean), with laws on another road. THE HEAD IS SHOWN
MET BY NOBODY HERE: NO MEMBER. The tops over Returns/LinkProver.lean and Returns/ArmsProver.lean
stand under `P5J.AtMgA`, which asks more and gives this head. NOTHING OF ANOTHER HOUSE's UNSEALED
FILES IS IMPORTED;  Beneath: four closed tests by Lean's
kernel, each with a control (the files named above). THE FULL SIZE ALONE. At the format's second
hash function alone. "Reached" is: over the list of the wrapped sub-protocols. At the two arms `here`, the
group's look-up and the quiet front's yes are premises. This file's imports are heavy. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.FiveReached
import Johnson.Desc.K2.Honest.Returns.ColsFit
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.Desc.K2.Honest.Returns.CallJoin
import Johnson.P5J.PlanSitsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf finFrontOf finishFrontQ finishFrontQ_rest
  finishFrontQ_codes flat)
open VerifiableInference.Desc.First.K2Hands (shW csW)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull madeRow)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (recAll_reached front_len frontOf pub_firstTree)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Col leafOk)
open ProofFile (Cl)

/-- **Five, and the two others of each tree, give the seven.** -/
theorem allTied_of {T : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook} :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)), AllFive ft pos.logN B0 ts rd →
      (∀ t ∈ ts, ∀ tree, B0.trees[t]? = some tree → leafOk T tree = true ∧ tree.lists = 0) →
      AllTied T ft pos B0 ts rd
  | [], [], _, _ => trivial
  | t :: ts, r :: rd, h5, h2 => by
    obtain ⟨⟨tree, a, b, c, d, e⟩, rest⟩ := h5
    obtain ⟨l1, l2⟩ := h2 t List.mem_cons_self tree a
    exact ⟨⟨tree, a, l1, fun _ => l2, b, c, d, e⟩,
      allTied_of ts rd rest fun x hx => h2 x (List.mem_cons_of_mem _ hx)⟩
  | [], _ :: _, h5, _ => h5.elim
  | _ :: _, [], h5, _ => h5.elim

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}

/-- Under the head: what Returns/FiveReached.lean has in front. -/
theorem six_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (F0T OnBytes.secondHashFunction Zp Np cF).planOk = true ∧ cutOf cF.blocksInOrder = cutFirstFull ∧
      Zp.first.shape = shW ∧ madeRow Zp = true ∧
      sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true ∧
      laidAtCodes Zp.first.codes Zp.made.proof.1 = some LFull ∧ Zp.first.codes = csW := by
  obtain ⟨t1, t2, t3⟩ := tests_at_head h O
  obtain ⟨w1, w2, -⟩ := P1K2.written3 h.scope O.pub t1
  exact ⟨h.laid.planOk, t2, w2, h.pins.1, t3, h.laid_codes_at_head, w1⟩

/-- The old main code's depth is the written one. -/
theorem depth_written {cs : Codes} {sh : Params.ReqShape} (e1 : cs = csW) (e2 : sh = shW)
    {c₀ : Code} (hc : cs.base[sh.code]? = some c₀) : c₀.logN = logW := by
  subst e1 e2
  exact logW_of hc

/-- **At every switch into a later group.** -/
theorem link_tied_reached (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) {c₀ : Code}
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) (dr : List Nat)
    (hleaf : ∀ τ ∈ treesOf (readIn (k2P Zp a nm .link n) s r₁ r₂ gs L Q), ∀ tree,
      s.book.trees[τ]? = some tree → leafOk (frontAt s L Q).st tree = true) :
    AllTied (frontAt s L Q).st (k2P Zp a nm .link n).firstTree (Positions.ofDraws c₀.logN dr)
      s.book (treesOf (readIn (k2P Zp a nm .link n) s r₁ r₂ gs L Q)) n.read := by
  obtain ⟨hpl, hcut, hsh, hy, hB, hLd, hcs⟩ := six_at_head h O
  have hlen : 14 * (m + 1) + 2 ≤ (frontOf cF).length := by
    rw [front_len h.scope h.reads O]
    omega
  have RA := recAll_reached h.scope h.reads O (reach_raw hr) (by omega) hlen
  have e0 : (k2P Zp a nm .link n).firstTree = 0 := pub_firstTree O.pub
  have el : (Positions.ofDraws c₀.logN dr).logN = logW :=
    depth_written (RA.codes.trans hcs) (RA.walk.shape.trans hsh) hc
  rw [e0]
  refine allTied_of _ _ ?_ fun τ hτ tree ht => ⟨hleaf τ hτ tree ht,
    link_unopened_all h.scope h.reads O hpl hcut hsh h23 hr L Q _ _ _ _ τ hτ tree ht⟩
  rw [el]
  exact link_five_reached h.scope h.reads O hpl hcut hsh hy hB hLd h23 hP hn hr L Q _ _ _ _

/-- **At the output head's switch.** -/
theorem head_tied_reached (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) {c₀ : Code}
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) (dr : List Nat)
    (hleaf : ∀ τ ∈ treesOf (callIn (k2P Zp a' nm .head n) (headFrontOf s a Q.target) s.book
        s.roots r₁ r₂ cols), ∀ tree,
      s.book.trees[τ]? = some tree → leafOk (headFrontOf s a Q.target).st tree = true) :
    AllTied (headFrontOf s a Q.target).st (k2P Zp a' nm .head n).firstTree
      (Positions.ofDraws c₀.logN dr) s.book
      (treesOf (callIn (k2P Zp a' nm .head n) (headFrontOf s a Q.target) s.book s.roots r₁ r₂
        cols)) n.read := by
  obtain ⟨hpl, hcut, hsh, hy, hB, hLd, hcs⟩ := six_at_head h O
  have hlen : 339 ≤ (frontOf cF).length := by
    rw [front_len h.scope h.reads O]
    omega
  have RA := recAll_reached h.scope h.reads O (reach_raw hr) (by omega) hlen
  have e0 : (k2P Zp a' nm .head n).firstTree = 0 := pub_firstTree O.pub
  have el : (Positions.ofDraws c₀.logN dr).logN = logW :=
    depth_written (RA.codes.trans hcs) (RA.walk.shape.trans hsh) hc
  rw [e0]
  refine allTied_of _ _ ?_ fun τ hτ tree ht => ⟨hleaf τ hτ tree ht,
    head_unopened_reached h.scope h.reads O hpl hcut hsh hr here group _ _ _ _ _ τ hτ tree ht⟩
  rw [el]
  exact head_five_reached h.scope h.reads O hpl hcut hsh hy hB hLd hP hn hr here group _ _ _ _ _

/-- **Behind the last segment.** -/
theorem fin_tied_reached (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn)
    {a : FinOwn} (Q : ReqGroup) (here : t.here = .fin a) {c₀ : Code}
    (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀) (dr : List Nat)
    (hleaf : ∀ τ ∈ treesOf (callIn (k2P Zp a' nm .finish n) (finFrontOf t a Q) t.book t.roots
        r₁ r₂ cols), ∀ tree,
      t.book.trees[τ]? = some tree → leafOk (finFrontOf t a Q).st tree = true) :
    AllTied (finFrontOf t a Q).st (k2P Zp a' nm .finish n).firstTree
      (Positions.ofDraws c₀.logN dr) t.book
      (treesOf (callIn (k2P Zp a' nm .finish n) (finFrontOf t a Q) t.book t.roots r₁ r₂ cols))
      n.read := by
  obtain ⟨hpl, hcut, hsh, hy, hB, hLd, hcs⟩ := six_at_head h O
  have hlen : 353 ≤ (frontOf cF).length := le_of_eq (front_len h.scope h.reads O).symm
  have RA := recAll_reached h.scope h.reads O (reach_raw hr) (by omega) hlen
  have e0 : (k2P Zp a' nm .finish n).firstTree = 0 := pub_firstTree O.pub
  have ec : t.check = s.check := (finishFrontQ_rest hq).2.2.2.2.1
  have el : (Positions.ofDraws c₀.logN dr).logN = logW :=
    depth_written ((finishFrontQ_codes hq).trans (RA.codes.trans hcs))
      ((by rw [ec] : t.check.frame.shape = s.check.frame.shape).trans
        (RA.walk.shape.trans hsh)) hc
  rw [e0]
  refine allTied_of _ _ ?_ fun τ hτ tree ht => ⟨hleaf τ hτ tree ht,
    fin_unopened_reached h.scope h.reads O hpl hcut hsh hr hq here Q _ _ _ _ τ hτ tree ht⟩
  rw [el]
  exact fin_five_reached h.scope h.reads O hpl hcut hsh hy hB hLd hP hn hr hq here Q _ _ _ _

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.allTied_of
#print axioms VerifiableInference.Desc.K2.Honest.Returns.six_at_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.depth_written
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_tied_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_tied_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_tied_reached
