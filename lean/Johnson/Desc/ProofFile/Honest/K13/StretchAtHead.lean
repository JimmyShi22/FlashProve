-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/StretchAtHead.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h, AND WHERE THE MAKER `bookWhole` RETURNS THE THREAD's BOOK AT THE SEATED
DESCRIPTION: hS, THE PREMISE ON THE BOOK OF `k13_coinsTie_of_msgTxt` (CoinsTieAtHead.lean of this
folder), TO THE LETTER. IT SHOWS hS AT NO BOOK: IT PAYS NOTHING OF THAT DEBT BY ITSELF: hW
(`bookWhole` RETURNS THE THREAD's BOOK) IS A PREMISE. Three statements with their proofs; no
definition. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `k13_front_written`: by the kernel: in the library's written list of places
(`P5J.At.ps`), of those without a link in front of the kind's place none is of the kind K13.
`k13_none_in_front_at_head`: so of the first chain's sub-protocols, under h. `k13_hS_of_whole`:
**hS.**

What it does. hS is one test on a book: the entries for the kind's row are one stretch of the
sender's, from maskStart + 13 on, 2 kCol + 1 long. Here it follows from "the book is the maker's"
(hW) and two public sentences that name no book: h1 (at whichever message the maker's `ownerOf`
returns for the index masks: its owner is part 0 of the sender's place, and its entries begin at the
sender's `maskStart`) · h3 (at that message, at whichever list `linksWants` returns: the links leave
the entry number 13 free). NONE OF THE THREE IS SHOWN HERE. h1 and h3 speak of every value that the
maker's own calls may return: none is picked for it. That the description's places pass `placesOk`,
which the law beneath asks too, is had under h.

What is had of them elsewhere. At the written description a closed fact on the maker's list of
stretches (`rawWantsAtK13_written`, AtFullSide/K14/RawWantsAtSpenders.lean) has, at the kind's
spender, the message's owner and first entry as written values, the number 13 and the count 37: h3's
number and h1's two left sides there: it is not carried to the hypothesis's description, and nothing
ties its values to J. Of hW: under h the maker does return a book at the three written lists of
sendings (`bookWhole_returns_at_head_ahead`, AtFullSide/K14/WholeAheadAtHead.lean); that it returns
the same book at the public part's own three lists has one premise more, that it returns that book
at the written description (`bookWhole_same_at_made`, Honest/K14/BookForAtPure.lean), which
`bookWhole_returns_written_ahead` (AtFullSide/K14/BookWholeWritten.lean) gives; no theorem named
here joins the two; what is left is that the thread's book is that book. The
verifier's own count of 13 takes at the border 355 is `k13_state_facts` (CoinsTieAtHead.lean). THE
TWO COUNTS ARE TWO TEXTS: that they agree is what h3 asks. UNDER h, AT THE LIBRARY's WRITTEN
SENDINGS, h3 and h1's two left sides are had: `k13_h3_at_head`, `k13_idx_at_head`
(AtFullSide/K13/WantsAtHead.lean), from two other closed facts.

How. `k13_stretch_of_whole` (PlanPartsListed.lean of this folder) at the member number 355, whose
place and rounds are the kind's under h (`m3_member_place`, `m3_member_fields`, FromThreadAt.lean);
`placesOk` from the hypothesis's field on the plan's tests by the library's `placesOk_of_planOk`
(Johnson/RunOne/Sound/KeyListsAtFK.lean); its premise that no listed sumcheck stands in front:
`k13_none_in_front_at_head`: under h the sub-protocols' places are the written list (the library's
`P5J.At.places_paid`), and the closed fact: over it alone the depth of recursion is raised (the
option maxRecDepth).

Limits. CONDITIONAL ON h AND THE THREE PREMISES: that they hold together is not shown. h has a
member at each of the goals' two named sets of public files (`headMember_named`,
AtFullSide/Top/HeadMemberAtGap.lean). J and n are free letters: h1 ties them. So are p0, p1, p2, the
three chains' sendings: hW, h1 and h3 share p0; p1 and p2 stand in hW alone; nothing here ties the
three to the library's own list of sendings. `k13_hS_of_whole` is called by CoinsTieOfSeated.lean of
this folder and by AtFullSide/K13/CoinsTieWritten.lean alone: there Lean takes it as the premise hS.
Nothing on what an entry is for. One closed fact by evaluation in Lean's kernel, which no
independent checker has replayed. This file's imports reach Johnson/Goal/, by the hypothesis h
(`P5J.AtMgA`).

What is not claimed. That any premise holds. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PlanPartsListed
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.P5J.PlacesPaid
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

set_option maxRecDepth 1000000 in
/-- **By the kernel**: in the library's written list of places, of those without a link in front
of the kind's place none is of the kind K13. -/
theorem k13_front_written :
    ((P5J.At.ps.filter fun a => a.link.isNone).takeWhile
      fun a => a != ⟨1, none, 3, .K13⟩).all (fun a => a.kind != .K13) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- **Under h: of the first chain's sub-protocols without a link in front of the kind's place none
is of the kind K13.** -/
theorem k13_none_in_front_at_head :
    ∀ c ∈ (cF.blocksInOrder.filter fun x => x.place.link.isNone).takeWhile
      fun x => x.place != ⟨1, none, 3, .K13⟩, c.place.kind ≠ .K13 := by
  intro c hc
  have e : cF.blocksInOrder.map (·.place) = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have hm : c.place ∈ ((cF.blocksInOrder.map (·.place)).filter fun a => a.link.isNone).takeWhile
      fun a => a != ⟨1, none, 3, .K13⟩ := by
    rw [List.filter_map, List.takeWhile_map]
    exact List.mem_map_of_mem hc
  rw [e] at hm
  have q := List.all_eq_true.1 k13_front_written _ hm
  exact fun hk => by rw [hk] at q; exact absurd q (by decide)

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **hS, THE PREMISE ON THE BOOK OF `k13_coinsTie_of_msgTxt`, TO THE LETTER, AT THE BOOK THAT
`bookWhole` RETURNS AT THE SEATED DESCRIPTION.** IT SHOWS hS AT NO BOOK: IT PAYS NOTHING OF THAT
DEBT BY ITSELF: hW (`bookWhole` RETURNS THE THREAD's BOOK) IS A PREMISE; so are h1 and h3: public
sentences that name no book; none is shown here. h1 and h3 speak of every value that the maker's own
calls may return. CONDITIONAL on h. -/
theorem k13_hS_of_whole {p0 p1 p2 : Johnson.G.ChainSends} {W' Y' : Type} (J : K1.SendJob W' Y')
    (n : ℕ)
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 (mergesByName cF.blocksInOrder) = .ok Bk)
    (h1 : ∀ idx, ownerOf indexMaskRun cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx →
      idx.owner = ⟨J.P.place, 0⟩ ∧ idx.base.e = K1.maskStart J.P J.ride n)
    (h3 : ∀ idx a, ownerOf indexMaskRun cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx →
      linksWants cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
        (mergesByName cF.blocksInOrder).ends (cF.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a →
      a.2 = 13) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[355]? =
        some blk →
      oneStretch (rowEntries Bk blk.place 2 0) =
        some (⟨J.P.place, 0⟩, K1.maskStart J.P J.ride n + 13, 2 * h.𝔇.P13.lin.kCol + 1) := by
  intro blk hb
  have hb' : cF.blocksInOrder[355]? = some blk := hb
  have hp := m3_member_place h hb'
  obtain ⟨idx, a, hi, ha, e⟩ := k13_stretch_of_whole (F := P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    (p := whereOf Zp) hW (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk)
    (List.mem_of_getElem? hb') (m3_member_fields h hb').1 hp
    (by rw [hp]; exact k13_none_in_front_at_head h)
  rw [(h1 idx hi).1, (h1 idx hi).2, h3 idx a hi ha] at e
  exact e

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_front_written
#print axioms ProofFile.Honest.K13.k13_none_in_front_at_head
#print axioms ProofFile.Honest.K13.k13_hS_of_whole
