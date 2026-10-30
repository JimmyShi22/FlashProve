-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TiedWhole.lean: THE PREMISE ON THE TREES OF THE CODE SWITCH's OWN
DECISION's YES (`AllTied`, Returns/ColsFit.lean: seven things a tree, along the opened messages'
trees and the plan's list of read trees), WHOLE, AT A REACHED STATE, AT ALL 25 OF THE KIND's PLACES,
UNDER THE ONE HEAD `P5J.AtMg`: NO PREMISE ON A TREE IS LEFT. A join of Returns/TiedReached.lean (six
of the seven) with two files of another house (the seventh: `leafOk`). Three statements with their
proofs: one call each.

  `link_tied_whole`, `head_tied_whole`, `fin_tied_whole` every m < 23 | 339 | 353 behind the quiet
                    front's yes: for all rounds, columns and draws: `AllTied`, in the letters of
                    Returns/TiedReached.lean's tops, with their premise on `leafOk` struck

By, this folder's: `link_tied_reached`, `head_tied_reached`, `fin_tied_reached`
(Returns/TiedReached.lean). ANOTHER HOUSE's, CALLED: `link_leafOk_all`
(Johnson/AtFull/Shape/LeafOkLinks.lean) · `head_leafOk`, `fin_leafOk`
(Johnson/AtFull/Shape/LeafOkArms.lean): `leafOk` at the front's statement of each tree that the
switch opens, in the goals' scope, at an opening, under no head. They fit the struck premise to the
letter: `inFront`'s statement is the front's (Returns/SentRead.lean). BY THAT HOUSE's OWN PAPER:
these two and four more of its files beneath them (ListsTidy.lean, ListsReached.lean,
MarksReached.lean, LeafOkReached.lean, the same folder) were compiled on a working lane, with no
ride of record; all six read whole, proofs too, by one reader of that house who is not their pen:
five of them at other bytes, without some controls, docstrings and asks, which were read by
difference; one at these bytes; no `decide +kernel` in them; the plain tactic `decide` twice (a
control; a comparison of two numerals); NONE OF THE SIX IS IN A SEALED LIBRARY OR ON A LINE FOR ONE.
WE HAVE READ THE THREE STATEMENTS THAT WE CALL, NOT THE PROOFS.

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE: NO MEMBER. THAT A STATE IS REACHED IS NOT SAID. 
Where a tree had no sampled part `leafOk` would accept for nothing; that the
carried rows' layout has a sampled member at the written sizes rests on an evaluation alone.
 All Limits of Returns/TiedReached.lean stand: four closed tests by Lean's kernel
beneath, each with a control; the full size alone; the format's second hash function alone; "reached" is:
over the list of the wrapped sub-protocols; at the two arms `here`, the group's look-up and the
quiet front's yes are premises. This file's imports are heavy. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.TiedReached
import Johnson.AtFull.Shape.LeafOkLinks
import Johnson.AtFull.Shape.LeafOkArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf finFrontOf finishFrontQ)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.AtFull.Shape (link_leafOk_all head_leafOk fin_leafOk)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Col)
open ProofFile (Cl)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}

/-- **At every switch into a later group.** -/
theorem link_tied_whole (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) {c₀ : Code}
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) (dr : List Nat) :
    AllTied (frontAt s L Q).st (k2P Zp a nm .link n).firstTree (Positions.ofDraws c₀.logN dr)
      s.book (treesOf (readIn (k2P Zp a nm .link n) s r₁ r₂ gs L Q)) n.read :=
  link_tied_reached h O h23 hP hn hr a nm r₁ r₂ gs L Q hc dr
    (link_leafOk_all h.scope h.reads O h23 hr L Q _ _ _ _)

/-- **At the output head's switch.** -/
theorem head_tied_whole (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) {c₀ : Code}
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) (dr : List Nat) :
    AllTied (headFrontOf s a Q.target).st (k2P Zp a' nm .head n).firstTree
      (Positions.ofDraws c₀.logN dr) s.book
      (treesOf (callIn (k2P Zp a' nm .head n) (headFrontOf s a Q.target) s.book s.roots r₁ r₂
        cols)) n.read :=
  head_tied_reached h O hP hn hr a' nm r₁ r₂ cols here group hc dr
    (head_leafOk h.scope h.reads O hr here group _ _ _ _ _)

/-- **Behind the last segment.** -/
theorem fin_tied_whole (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn)
    {a : FinOwn} (Q : ReqGroup) (here : t.here = .fin a) {c₀ : Code}
    (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀) (dr : List Nat) :
    AllTied (finFrontOf t a Q).st (k2P Zp a' nm .finish n).firstTree
      (Positions.ofDraws c₀.logN dr) t.book
      (treesOf (callIn (k2P Zp a' nm .finish n) (finFrontOf t a Q) t.book t.roots r₁ r₂ cols))
      n.read :=
  fin_tied_reached h O hP hn hr hq a' nm r₁ r₂ cols Q here hc dr
    (fin_leafOk h.scope h.reads O hr hq here Q _ _ _ _)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_tied_whole
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_tied_whole
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_tied_whole
