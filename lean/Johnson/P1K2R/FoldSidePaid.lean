-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/FoldSidePaid.lean: THE BORDER-WISE PREMISES OF THE FOLD's SIDE OF THE CODE SWITCH's FIRST AND FOURTH TIE (FoldSide.lean: Hn | Hn2: the counts of messages · He: each message has the listed shape, in front of the switch · He0: the like at the kept old messages, in front of the last closing) PAID BY CALLS OF OTHER FILES' THEOREMS; and the four tops with these premises gone: foldSide_one_paid · foldSide_link_paid · foldSide_head_paid · foldSide_fin_paid.
WHAT THEN STANDS IN THE HEAD, IN ONE STRUCTURE, Owed Z Bs c p: SIX NAMED DEBTS OF OTHER FILES:
  cut     the chain's blocks have the written cut (cut_of_row, from its row's accept: the Lean
          verifier's entry test 10 asks that row: Johnson/Desc/Laid/ProofAsks.lean)
          (Where this and lean/THEOREM.md differ, the
          page holds.)
  sends   SendDebts (Johnson/IMR/SendsJoin.lean: six fields on the book along the chain)
  shapes  ShapeDebts (Johnson/IMR/ShapesJoin.lean: first · hear · back: the shares of the kinds that send, K1, K2, K12; grows)
  areB    the test sendsAreB (Johnson/Desc/K12/Door/LaidOfLists.lean) at 358 says yes (a test on the plan; evaluated at three sets of public files by report)
  noMark  the first state bears no mark
  written the planner's sendings of the proof file are the written ones (sends_in_scope, Johnson/Goal/Numbers/MadeInScope.lean, under the verifier's test on the plan)
PAID HERE, NO DEBT: «every block of the chain passes its own test on the plan» (plan_of: from F.planOk, by ProofFile's planOk_blocksOk, Johnson/Desc/ProofFile/Law/OrderStated.lean, and the opening's field desc).
BESIDE THEM STAY, AS IN FoldSide.lean: in scope · the files read · the opening · onlineDescription returns F · F.planOk · hcs hsh (the written codes and shape) · Reach at the switch's number · at the finish: the quiet step accepts.
THE CIRCLE, BOOKED: «shapes» HOLDS THE CODE SWITCH's OWN SHARE AT EVERY ONE OF ITS 25 NUMBERS, each under «reached at that number». It is asked WHOLE here. Whoever pays that share at the switch number j out of the code switch's law may spend these tops at the switches BEFORE j alone: AN INDUCTION ALONG THE SWITCHES IS OWED BY WHOEVER CLOSES IT. Not by this file.
PAYERS CALLED: Meaning.Carry.n0_at_link_paid | n0_at_head_paid | n0_at_finish_paid | counts_at_cut_paid | toldBefore_eq (Johnson/IMR/ToldPaid.lean · N0AtCut.lean) · IM.shapes_start (Johnson/IMR/ShapesJoin.lean) · K2Hands.shapes_of_test | olds_of_test | mw_of_sends (Johnson/Top/H0/K2Hands/FoldSideOf.lean), over the closed fact told_closing_written (by Lean's kernel).
No soundness. That the six can be met together is not shown.
-/
import Johnson.P1K2R.FoldSide
import Johnson.IMR.ToldPaid
import Johnson.IMR.ShapesJoin
import Johnson.Top.H0.K2Hands.FoldSideOf

set_option autoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First.K2Hands (frontB2 placeFrame Tied csW MW shapes_of_test
  olds_of_test mw_of_sends)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (fxAt storedB proofSendsFull)
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

/-- **The six named debts.** -/
structure Owed (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (c : Chain S Cl) (p : ProofFile.InstPub) : Prop where
  cut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull
  sends : IM.SendDebts 0 Z.first.codes (snAt Z Bs.G₀ IM.placesW) Z Bs.G₀ c (ProofFile.startS Z p)
  shapes : IM.ShapeDebts 0 (snAt Z Bs.G₀ IM.placesW) Z Bs.G₀ c (ProofFile.startS Z p)
  areB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true
  noMark : (ProofFile.startS Z p).failed = none
  written : Z.made.proof = proofSendsFull

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {p : ProofFile.InstPub}

/-- Every block of the chain passes its own test on the plan. -/
theorem plan_of (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  have h := ProofFile.Law.planOk_blocksOk hpl
  rw [O.desc] at h
  intro b hb
  have k := (List.all_eq_true.1 h) b hb
  rw [Bool.and_eq_true] at k
  exact k.1

/-- Hn: the count in front of the switch into group g, 1 ≤ g ≤ 23. -/
theorem paid_n (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c p) {g : ℕ}
    (h1 : 1 ≤ g) (h2 : g ≤ 23) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S)
    (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take (14 * g + 2)) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    t.st.oracles.size = K2.n0At g :=
  Meaning.Carry.n0_at_link_paid hS hR O W.cut h1 h2
    (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) p R C (t, R', C') h

theorem paid_n_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c p) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S)
    (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    t.st.oracles.size = K2.n0At 24 :=
  Meaning.Carry.n0_at_head_paid hS hR O W.cut
    (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) p R C (t, R', C') h

theorem paid_n_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c p) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S)
    (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    t.st.oracles.size = K2.n0At 25 :=
  Meaning.Carry.n0_at_finish_paid hS hR O W.cut
    (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) p R C (t, R', C') h

/-- He: each message has the listed shape, at every border k ≤ 358. -/
theorem paid_e (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (W : Owed Z Bs c p) {k : ℕ}
    (hk : k ≤ 358) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S)
    (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]? :=
  shapes_of_test (IM.shapes_start hS hR O p W.sends W.shapes W.areB W.noMark hk h)
    (mw_of_sends W.written)

/-- He0: the like at the kept old messages, in front of link l's closing, l < 24. -/
theorem paid_e0 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c p) {l : ℕ} (hl : l < 24) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S)
    (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12)) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    ∀ o ∈ K2.oldsAt (l + 1), (t.st.oracles[o]?).map (·.shape) = MW[o]? :=
  olds_of_test hl W.cut
    ((Meaning.Carry.counts_at_cut_paid hS hR O p R C (14 * l + 12) (by omega)
      (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) (t, R', C') h).1.trans
        (Meaning.Carry.toldBefore_eq c.blocksInOrder (14 * l + 12)).symm)
    (IM.shapes_start hS hR O p W.sends W.shapes W.areB W.noMark (by omega) h)
    (mw_of_sends W.written)

/-! ### The four tops, with the border-wise premises gone -/

theorem foldSide_one_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) (W : Owed Z Bs c p) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 16 (p, s))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[0]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 1 0 (K2.n0At 1) (K2.oldsAt 1) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 1) (K2.oldsAt 1)) fx = true ∧
        s.st.oracles = fx.st.oracles) :=
  foldSide_one hS hR O hF hpl hcs hsh hr
    (paid_n hS hR O hpl W (g := 1) (by omega) (by omega))
    (paid_e hS hR O W (k := 16) (by omega))
    (paid_e0 hS hR O hpl W (l := 0) (by omega)) hq h hrw

theorem foldSide_link_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {l : ℕ}
    (h1 : 1 ≤ l) (h23 : l < 23) (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW)
    (W : Owed Z Bs c p) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (l + 1) + 2) (p, s))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[l]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ (l + 1) 0 (K2.n0At (l + 1)) (K2.oldsAt (l + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At (l + 1)) (K2.oldsAt (l + 1))) fx = true ∧
        s.st.oracles = fx.st.oracles) :=
  foldSide_link hS hR O hF hpl h1 h23 hcs hsh hr
    (fun _ g1 g2 => paid_n hS hR O hpl W g1 g2)
    (paid_e hS hR O W (by omega))
    (paid_e0 hS hR O hpl W (by omega)) hq h hrw

theorem foldSide_head_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) (W : Owed Z Bs c p) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (p, s))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[23]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 24 0 (K2.n0At 24) (K2.oldsAt 24) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 24) (K2.oldsAt 24)) fx = true ∧
        s.st.oracles = fx.st.oracles) :=
  foldSide_head hS hR O hF hpl hcs hsh hr
    (paid_n hS hR O hpl W (g := 23) (by omega) (by omega))
    (paid_n_head hS hR O hpl W)
    (paid_e hS hR O W (k := 339) (by omega))
    (paid_e0 hS hR O hpl W (l := 23) (by omega)) hq h hrw

theorem foldSide_fin_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) (W : Owed Z Bs c p) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (p, s))
    (hQ : K2.finishFrontQ s = .ok t) {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (h : K2.frontAt q t = some fx) {r : SwRow}
    (hrw : tableFullLit[24]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 25 0 (K2.n0At 25) (K2.oldsAt 25) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 25) (K2.oldsAt 25)) fx = true ∧
        s.st.oracles = fx.st.oracles) :=
  foldSide_fin hS hR O hF hpl hcs hsh hr
    (paid_n_fin hS hR O hpl W)
    (paid_e hS hR O W (k := 353) (by omega)) hQ hq h hrw

end

end P1K2

#print axioms P1K2.foldSide_one_paid
#print axioms P1K2.foldSide_link_paid
#print axioms P1K2.foldSide_head_paid
#print axioms P1K2.foldSide_fin_paid
