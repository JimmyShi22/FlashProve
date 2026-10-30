-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsPaid.lean: AT THE CODE SWITCH's TWO ARMS (339, the output head's
switch; 353, behind the last segment) THE TOP ON THE TREES ASKS NO MORE THAN THESE THREE: THE HEAD
`P5J.AtMg`, THE OPENING IN ITS LETTERS, AND "s IS REACHED THERE". A join of Returns/TiedWhole.lean
with two other files, which pay the arms' premises on the state. Statements with their proofs:
calls.

  `code_look_reached` in scope, at an opening: at every state reached at a border from 2 to 353 the
                    old main code's look-up returns
  `head_tied_paid` the head · the opening · s reached at 339 ⊢ there are the plan's numbers, a, Q,
                    c₀ with: s stands in the head's segment at a · the group's look-up returns Q ·
                    the code's returns c₀ · `AllTied` at s, for all rounds, columns and draws
  `fin_tied_paid` the head · the opening · s reached at 353 ⊢ there are the plan's numbers, t, a, c₀
                    with: the quiet front returns t at s · t stands behind the last segment at a ·
                    the code's look-up at t returns c₀ · `AllTied` at t, at every group Q, for all
                    rounds, columns and draws

By, this folder's: `head_tied_whole`, `fin_tied_whole` (Returns/TiedWhole.lean) · `tests_at_head`
(Returns/UnderHead.lean), `h25_of_hy` (Returns/FinAtReached.lean) · `codes_of_reqOk`
(Returns/LinkReached.lean). The library's: `t3_nums_head`, `t3_nums_fin`
(Johnson/P1K2R/TieThreeConst.lean) · `recAll_reached` (Johnson/IMR/AtReach.lean), `RecAll`,
`FramePub` (Johnson/Goal/Meaning/RecAll.lean), `front_len` (Johnson/IMR/FinPin.lean), `reach_raw`
(Johnson/Top/H0/Walk/Reach.lean) · `finishFrontQ_st`, `finishFrontQ_rest`
(Johnson/Top/H0/Tw/K2C/FinFront.lean). A NEAR RELATIVE OF `code_look_reached`, THIS FOLDER's, NOT
CALLED: `link_fields_reached` (Returns/LinkReached.lean) has the same look-up as one clause of its
end, at the 23 links, by the same road. OTHER FILES', CALLED: `head_looks_reached`
(Johnson/AtFull/Shape/HeadLooksReached.lean) · `fin_looks_reached`
(Johnson/AtFull/Shape/FinFrontReached.lean): in scope, at an opening, where the shape has 25 links,
at every state reached at the place: what the switch looks up is there; at 353 the quiet front
returns. BY THAT HOUSE's OWN PAPERS: compiled on a working lane, with no ride of record; no `decide
+kernel`; on no line for a sealed library; ITS LETTER says that each was read whole, proofs too, by
one reader of that house who is not the pen; THE PACK's OWN TWO PAGES, a few minutes elder, say:
read by the pen alone. WE HAVE READ THE TWO STATEMENTS THAT WE CALL, NOT THE PROOFS.

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE; THAT A STATE IS REACHED IS NOT SAID. All Limits of
Returns/TiedWhole.lean stand, six other
files beneath it among them. "Reached" is: over the list of the wrapped sub-protocols. The
full size alone; the format's second hash function alone. This file's imports are heavy. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Returns.TiedWhole
import Johnson.Desc.K2.Honest.Returns.FinAtReached
import Johnson.AtFull.Shape.HeadLooksReached
import Johnson.AtFull.Shape.FinFrontReached
import Johnson.P1K2R.TieThreeConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf finFrontOf finishFrontQ finishFrontQ_st
  finishFrontQ_rest)
open VerifiableInference.Desc.First.K2Caller (t3_nums_head t3_nums_fin)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.AtFull.Shape (head_looks_reached fin_looks_reached)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Col)
open ProofFile (Cl)

/-- **The old main code's look-up returns at every state reached at a border from 2 to 353.** -/
theorem code_look_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : Nat} (h2 : 2 ≤ k)
    (hk : k ≤ 353) {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) :
    ∃ c₀, s.st.codes.base[s.check.frame.shape.code]? = some c₀ := by
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) h2
    (by rw [Meaning.K2.front_len hS hR O]; exact hk)
  have hok : reqOk s.st.codes s.check.frame.shape = true := by
    rw [RA.codes, RA.walk.shape]
    exact RA.ok
  obtain ⟨c₀, -, hc, -⟩ := codes_of_reqOk hok
  exact ⟨c₀, hc⟩

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}

/-- **At the output head's switch: the head, the opening, "reached": no more.** -/
theorem head_tied_paid (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s)) :
    ∃ (Pp : Prep) (n : Nums) (a : HeadOwn) (Q : ReqGroup) (c₀ : Code),
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp (some 24) = some n ∧ s.here = .head a ∧
      s.check.frame.groups[s.check.frame.link]? = some Q ∧
      s.st.codes.base[s.check.frame.shape.code]? = some c₀ ∧
      ∀ (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn) (dr : List Nat),
        AllTied (headFrontOf s a Q.target).st (k2P Zp a' nm .head n).firstTree
          (Positions.ofDraws c₀.logN dr) s.book
          (treesOf (callIn (k2P Zp a' nm .head n) (headFrontOf s a Q.target) s.book s.roots r₁ r₂
            cols)) n.read := by
  obtain ⟨Pp, n, hP, hn⟩ := t3_nums_head h.scope h.reads O h.laid.planOk
  have h25 := h25_of_hy h.scope O (tests_at_head h O).1
  obtain ⟨a, Q, here, group⟩ := head_looks_reached h.scope h.reads O h25 hr
  obtain ⟨c₀, hc⟩ := code_look_reached h.scope h.reads O (by omega) (by omega) hr
  exact ⟨Pp, n, a, Q, c₀, hP, hn, here, group, hc, fun a' nm r₁ r₂ cols dr =>
    head_tied_whole h O hP hn hr a' nm r₁ r₂ cols here group hc dr⟩

/-- **Behind the last segment: the head, the opening, "reached": no more.** -/
theorem fin_tied_paid (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s)) :
    ∃ (Pp : Prep) (n : Nums) (t : S) (a : FinOwn) (c₀ : Code),
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧ finishFrontQ s = .ok t ∧
      t.here = .fin a ∧ t.st.codes.base[t.check.frame.shape.code]? = some c₀ ∧
      ∀ (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn) (Q : ReqGroup)
        (dr : List Nat),
        AllTied (finFrontOf t a Q).st (k2P Zp a' nm .finish n).firstTree
          (Positions.ofDraws c₀.logN dr) t.book
          (treesOf (callIn (k2P Zp a' nm .finish n) (finFrontOf t a Q) t.book t.roots r₁ r₂
            cols)) n.read := by
  obtain ⟨Pp, n, hP, hn⟩ := t3_nums_fin O h.laid.planOk
  have h25 := h25_of_hy h.scope O (tests_at_head h O).1
  obtain ⟨t, a, -, hq, here, -⟩ := fin_looks_reached h.scope h.reads O h25 hr
  obtain ⟨c₀, hc₀⟩ := code_look_reached h.scope h.reads O (by omega) (by omega) hr
  have hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀ := by
    rw [finishFrontQ_st hq, (finishFrontQ_rest hq).2.2.2.2.1]
    exact hc₀
  exact ⟨Pp, n, t, a, c₀, hP, hn, hq, here, hc, fun a' nm r₁ r₂ cols Q dr =>
    fin_tied_whole h O hP hn hr hq a' nm r₁ r₂ cols Q here hc dr⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.code_look_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_tied_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_tied_paid
