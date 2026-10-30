-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ArmsLeftNums.lean: THE CODE SWITCH AT THE OUTPUT HEAD's PLACE (339) AND BEHIND
THE LAST SEGMENT (353) OF THE PROOF FILE's OWN FIRST CHAIN: FOUR PREMISES OF THE LAW "THE KIND's OWN
DECISION SAYS YES" AT A REACHED STATE, AT EACH OF THE TWO PLACES: plan · trees · inRange (fields of
CallLast, Johnson/Desc/K2/Honest/Returns/LeftAtReached.lean) AND THE ENTRY's TEST. Under the head
P5J.AtMgA. The counterpart of LinkLeftPlan.lean and LinkLeftNums.lean, which have the 23 links.

How. One law at a front x, general in the place (call_of_ties): where x's notices are the plan's
list n.sent and a named list N, x's codes are n.codes and the written ones, x's carried rows stand
under the written shape's main code, the place's two entries are a written row's (P2At), and one
closed test accepts at that row and N: the four. The ties are the library's: sw_head, sw_finish
(Johnson/P1K2R/HstReached.lean); front_pin_head (Johnson/IMR/FrontPin.lean), front_pin_fin
(Johnson/IMR/FinPin.lean); written_of_head; p2At_table.

  `armB m N`: the closed test at the written row m and a list of notices N: the shared sending's own
    test on its plan · the entry's count of draws that must not be 0 · the range of positions.
    `sentHeadW`, `sentFinW`: the two lists, on the written shape (targetAt, othersAt, frameAtLink,
    Johnson/Goal/Meaning/K2Share/FrontNotices.lean). `armB_full`, `armB_can_fail`.
  **`call_of_ties`**: the law at a front.
  `armNumsB m N`, `armNumsB_full`, `armNumsB_can_fail`; **`nums_of_ties`**: FOUR TIES OF NUMBERS at
    a front, by the same road: round 1 draws as many elements as the seeds take · the sending's
    answers are the plan's · the plan's range of positions is the old main code's (paid by armB's
    clause on the range, not by armNumsB) · a position is drawn. **`head_nums_reached`**,
    **`fin_nums_reached`**: at the two places.
  `p2At_fin`: P2At at the finish's numbers (numsAt Pp none).
  **`head_four_reached`**, **`fin_four_reached`**: the four at headFrontOf s a Q.target, s reached
    at 339; at finFrontOf t a Q, t behind the quiet front of a state reached at 353.

THE DEVICE. The four closed facts on armB and armNumsB are closed by "decide +kernel" under a raised
maxRecDepth; so are two counts of the written shape's links (25), inside two proofs.

Limits. inRange keeps its premise "every position drawn is below 2 ^ n.logN". At 339 that the chain
stands in the head's link and the frame's group is there, at 353 that the quiet front returns, that
the chain then stands in the finish and that its group is laid, are premises, as in head_behind_last
and fin_behind_last (LeftAtReached.lean). Of a reached state: that anything is reached is not said.
Of the premises: an O follows from the head (h.laid.opened); hP and hn have the library's
t3_nums_head and t3_nums_fin (Johnson/P1K2R/TieThreeConst.lean); at 353, where the quiet front
returns, "here" and "laid" have the library's finishFrontQ_group (Johnson/IMR/K2ShareAt.lean); none
of these is joined here. That the quiet front returns at a state reached at 353, and "here" and
"group" at a state reached at 339, are shown neither way here (behind the yes of the place "H:1" the
library has h1_headFr, Johnson/IMR/ListsEnds.lean; it is not joined to "reached at 339" here).
"Reached" is over the list of the wrapped sub-protocols. The full size alone. armB_can_fail and
armNumsB_can_fail show that each conjunction can fail at a row that is there; which clause says no
is not told. Both stand at row 23 and at no notice: the clause that reads no notice (armB: the
range; armNumsB: a position is drawn) is shown no failing case, and row 24 has no control. That the
head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkPlanNums
import Johnson.IMR.FrontPin
import Johnson.IMR.FinPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (par9 headFrontOf finFrontOf finishFrontQ targetAt othersAt
  frameAtLink frontAt_of)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit P2At tableWritten_is)
open VerifiableInference.Desc.K2.Honest.Returns (sendingAt sendingAt_sent)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf sw_head sw_finish p2At_table prepOf_request)
open IM (k2P)
open _root_.Tw.K2 (Front switchNotices)
open _root_.Desc.K14.Law (secondAt seatZ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 The closed test -/

/-- The closed test at the written row m and a list of notices. -/
def armB (m : Nat) (N : Array OracleNotice) : Bool :=
  (tableFullLit[m]?).any fun r =>
    VerifiableInference.Desc.K1.planOkOwn (sendW proofSizedFull.codes N) &&
      (entry0 r).drawNZ == _root_.Desc.Plain.answersMax N &&
      r.g.main.logN == (proofSizedFull.codes.base.getD proofSizedFull.request.code default).logN

/-- What the switch at the output head's place announces, on the written shape. -/
def sentHeadW : Array OracleNotice :=
  switchNotices (targetAt proofSizedFull.request 24) (othersAt proofSizedFull.request 24)

/-- What the switch behind the last segment announces, on the written shape. -/
def sentFinW : Array OracleNotice :=
  switchNotices (targetAt proofSizedFull.request 25)
    #[foldMaskNotice ((frameAtLink proofSizedFull.request 25).foldShape 25 {})]

set_option maxRecDepth 1000000 in
/-- Lean's kernel says yes at the two rows. -/
theorem armB_full : armB 23 sentHeadW = true ∧ armB 24 sentFinW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail at a row that is there: at no notice. -/
theorem armB_can_fail : armB 23 #[] = false ∧ (tableFullLit[23]?).isSome = true := by
  decide +kernel

/-! ## 2 The law at a front -/

/-- **THE FOUR AT A FRONT**, from the ties. -/
theorem call_of_ties {Zp : ProofFile.Pub} {Pp : Prep} {link : Option Nat} {n : Nums}
    (hn : numsAt Pp link = some n) {m : Nat} {N : Array OracleNotice} (k : armB m N = true)
    (a : Place) (nm : String) (st : VerifiableInference.Desc.First.K2.At)
    (H2 : ∀ r, tableFullLit[m]? = some r → P2At r (k2P Zp a nm st n)) {x : Front}
    (t1 : switchNotices x.T x.others = n.sent) (t2 : x.st.codes = n.codes)
    (t3 : x.st.codes = proofSizedFull.codes) (t4 : switchNotices x.T x.others = N)
    (t5 : x.f.rows.code = proofSizedFull.request.code) :
    VerifiableInference.Desc.K1.planOkOwn (sendingAt (k2P Zp a nm st n) x) = true ∧
      ((layTrees (sendingAt (k2P Zp a nm st n) x).codes
        (sendingAt (k2P Zp a nm st n) x).sent).getD {}).shapes.size =
        (par9 (k2P Zp a nm st n)).eSeed.roots ∧
      planOk1 none n.sent (par9 (k2P Zp a nm st n)).eSeed = true ∧
      ∀ (r₂ : Fmt.RoundView) (c : Code), (∀ q ∈ r₂.drawn.poss, q < 2 ^ n.logN) →
        ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
          v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN := by
  unfold armB at k
  cases hrw : tableFullLit[m]? with
  | none =>
    rw [hrw] at k
    cases k
  | some r =>
    rw [hrw] at k
    have k' : (VerifiableInference.Desc.K1.planOkOwn (sendW proofSizedFull.codes N) &&
      (entry0 r).drawNZ == _root_.Desc.Plain.answersMax N &&
      r.g.main.logN ==
        (proofSizedFull.codes.base.getD proofSizedFull.request.code default).logN) = true := k
    simp only [Bool.and_eq_true, beq_iff_eq] at k'
    obtain ⟨⟨k1, k2⟩, k3⟩ := k'
    have P2 := H2 r hrw
    refine ⟨?_, ?_, ?_, ?_⟩
    · show VerifiableInference.Desc.K1.planOkOwn
        (sendW x.st.codes (switchNotices x.T x.others)) = true
      rw [t3, t4]
      exact k1
    · obtain ⟨lay, hl, er⟩ := numsAt_roots hn
      rw [sendingAt_sent, t1]
      show ((layTrees x.st.codes n.sent).getD {}).shapes.size = n.roots
      rw [t2, hl, er]
      rfl
    · have eN : n.nonZero = (entry0 r).drawNZ :=
        congrArg (fun l : List Fmt.Entry => (l.getD 0 { name := "" }).drawNZ) P2
      have kk : (n.nonZero == _root_.Desc.Plain.answersMax n.sent) = true := by
        rw [eN, k2, ← t4, t1]
        exact beq_self_eq_true _
      show ((none : Option Nat).all (· == 0) && ("SEND seed" == "SEND seed") &&
        (n.nonZero == _root_.Desc.Plain.answersMax n.sent) && ((0 : Nat) == 0)) = true
      rw [kk]
      rfl
    · intro r₂ c range v hv
      have hv' : v ∈ listOfT r₂.drawn.poss := by simpa [Positions.ofDraws] using hv
      rw [listOfT_eq, Fmt.listOf_mem] at hv'
      have eL : n.logN = r.g.main.logN := P2.logN
      rw [t3, t5, ← k3, ← eL]
      exact range v hv'

/-- The written row m's two entries against the sending at a list of notices. -/
def armNumsB (m : Nat) (N : Array OracleNotice) : Bool :=
  (tableFullLit[m]?).any fun r =>
    (entry0 r).drawE == (sendW proofSizedFull.codes N).seeds *
        ((sendW proofSizedFull.codes N).coordinates + 1) &&
      (entry1 r).answers == (sendW proofSizedFull.codes N).answers && decide (0 < (entry1 r).poss)

set_option maxRecDepth 1000000 in
/-- Lean's kernel says yes at the two rows. -/
theorem armNumsB_full : armNumsB 23 sentHeadW = true ∧ armNumsB 24 sentFinW = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail at a row that is there: at no notice. -/
theorem armNumsB_can_fail : armNumsB 23 #[] = false ∧ (tableFullLit[23]?).isSome = true := by
  decide +kernel

/-- **FOUR TIES OF NUMBERS AT A FRONT**: round 1 draws as many elements as the seeds take · the
sending's answers are the plan's · the plan's range of positions is the old main code's · a position
is drawn. k0, armB's yes, is spent for the third alone: by its clause on the range. -/
theorem nums_of_ties {Zp : ProofFile.Pub} {n : Nums} {m : Nat} {N : Array OracleNotice}
    (k : armNumsB m N = true) (k0 : armB m N = true) (a : Place) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At)
    (H2 : ∀ r, tableFullLit[m]? = some r → P2At r (k2P Zp a nm st n)) {x : Front}
    (t3 : x.st.codes = proofSizedFull.codes) (t4 : switchNotices x.T x.others = N)
    (t5 : x.f.rows.code = proofSizedFull.request.code) :
    n.seeds = (sendingAt (k2P Zp a nm st n) x).seeds *
        ((sendingAt (k2P Zp a nm st n) x).coordinates + 1) ∧
      (sendingAt (k2P Zp a nm st n) x).answers = n.answers ∧
      n.logN = (x.st.codes.base.getD x.f.rows.code default).logN ∧ 0 < n.positions := by
  unfold armNumsB at k
  unfold armB at k0
  cases hrw : tableFullLit[m]? with
  | none =>
    rw [hrw] at k
    cases k
  | some r =>
    rw [hrw] at k k0
    have k' : ((entry0 r).drawE == (sendW proofSizedFull.codes N).seeds *
        ((sendW proofSizedFull.codes N).coordinates + 1) &&
      (entry1 r).answers == (sendW proofSizedFull.codes N).answers &&
      decide (0 < (entry1 r).poss)) = true := k
    have k0' : (VerifiableInference.Desc.K1.planOkOwn (sendW proofSizedFull.codes N) &&
      (entry0 r).drawNZ == _root_.Desc.Plain.answersMax N &&
      r.g.main.logN ==
        (proofSizedFull.codes.base.getD proofSizedFull.request.code default).logN) = true := k0
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at k' k0'
    obtain ⟨⟨k1, k2⟩, k3⟩ := k'
    have P2 := H2 r hrw
    have a1 : n.seeds = (entry0 r).drawE :=
      congrArg (fun l : List Fmt.Entry => (l.getD 0 { name := "" }).drawE) P2
    have a2 : n.answers = (entry1 r).answers :=
      congrArg (fun l : List Fmt.Entry => (l.getD 1 { name := "" }).answers) P2
    have a3 : n.positions = (entry1 r).poss :=
      congrArg (fun l : List Fmt.Entry => (l.getD 1 { name := "" }).poss) P2
    have eS : sendW x.st.codes (switchNotices x.T x.others) = sendW proofSizedFull.codes N := by
      rw [t3, t4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show n.seeds = (sendW x.st.codes (switchNotices x.T x.others)).seeds *
        ((sendW x.st.codes (switchNotices x.T x.others)).coordinates + 1)
      rw [eS, a1, k1]
    · show (sendW x.st.codes (switchNotices x.T x.others)).answers = n.answers
      rw [eS, a2, k2]
    · rw [t3, t5, ← k0'.2]
      exact P2.logN
    · rw [a3]
      exact k3

/-! ## 3 At the two places -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {z : ProofFile.InstPub}

/-- Under the head the finish's two entries are the last written row's. -/
theorem p2At_fin (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {r : SwRow} (hr : tableFullLit[24]? = some r) (a : Place) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At) : P2At r (k2P Zp a nm st n) := by
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have e25 : Pp.z.request.link.length = 25 := by
    rw [(prepOf_request hP).2, O.first, W.shape, OnBytes.Road.K4.shape_one]
    decide +kernel
  exact p2At_table
    (tableWritten_is (VerifiableInference.Desc.First.K2Ties.tableWrittenB_head h)) h.laid.pub
    O.blank hP hr (a := ⟨1, none, 0, .K2⟩) (nm := nm) (st := st) e25 hn

/-- **THE FOUR AT THE OUTPUT HEAD's PLACE.** -/
theorem head_four_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s)) (a' : Place) (nm : String)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    VerifiableInference.Desc.K1.planOkOwn
        (sendingAt (k2P Zp a' nm .head n) (headFrontOf s a Q.target)) = true ∧
      ((layTrees (sendingAt (k2P Zp a' nm .head n) (headFrontOf s a Q.target)).codes
        (sendingAt (k2P Zp a' nm .head n) (headFrontOf s a Q.target)).sent).getD {}).shapes.size =
        (par9 (k2P Zp a' nm .head n)).eSeed.roots ∧
      planOk1 none n.sent (par9 (k2P Zp a' nm .head n)).eSeed = true ∧
      ∀ (r₂ : Fmt.RoundView) (c : Code), (∀ q ∈ r₂.drawn.poss, q < 2 ^ n.logN) →
        ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
          v < 2 ^ ((headFrontOf s a Q.target).st.codes.base.getD
            (headFrontOf s a Q.target).f.rows.code default).logN := by
  have hfx : VerifiableInference.Desc.First.K2.frontAt (k2P Zp a' nm .head n) s =
      some (headFrontOf s a Q.target) := frontAt_of (Or.inr (Or.inl ⟨rfl, a, Q, here, group, rfl⟩))
  have SW := sw_head h.scope h.reads O h.laid.value h.laid.planOk a' nm hP hn hr
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  obtain ⟨p1, -, p3, p4, -, p6, -⟩ :=
    Meaning.K2.front_pin_head h.scope h.reads O f₀ (q := k2P Zp a' nm .head n) rfl hfx
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : Zp.first.shape = proofSizedFull.request := W.shape.trans OnBytes.Road.K4.shape_one
  exact call_of_ties hn armB_full.1 a' nm .head
    (fun r hrw => p2At_head h O hP hn hrw a' nm .head) (SW.2 _ hfx) SW.1.codes
    (p1.trans W.codes) (by rw [p3, p4, esh]; rfl) (by rw [p6, esh])

/-- **THE FOUR BEHIND THE LAST SEGMENT.** t: the state behind the quiet front. -/
theorem fin_four_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) {a : FinOwn} {Q : ReqGroup}
    (here : t.here = .fin a) (laid : a.G = some Q) :
    VerifiableInference.Desc.K1.planOkOwn
        (sendingAt (k2P Zp a' nm .finish n) (finFrontOf t a Q)) = true ∧
      ((layTrees (sendingAt (k2P Zp a' nm .finish n) (finFrontOf t a Q)).codes
        (sendingAt (k2P Zp a' nm .finish n) (finFrontOf t a Q)).sent).getD {}).shapes.size =
        (par9 (k2P Zp a' nm .finish n)).eSeed.roots ∧
      planOk1 none n.sent (par9 (k2P Zp a' nm .finish n)).eSeed = true ∧
      ∀ (r₂ : Fmt.RoundView) (c : Code), (∀ q ∈ r₂.drawn.poss, q < 2 ^ n.logN) →
        ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
          v < 2 ^ ((finFrontOf t a Q).st.codes.base.getD
            (finFrontOf t a Q).f.rows.code default).logN := by
  have hfx : VerifiableInference.Desc.First.K2.frontAt (k2P Zp a' nm .finish n) t =
      some (finFrontOf t a Q) := frontAt_of (Or.inr (Or.inr ⟨rfl, a, Q, here, laid, rfl⟩))
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : Zp.first.shape = proofSizedFull.request := W.shape.trans OnBytes.Road.K4.shape_one
  have h25 : Zp.first.shape.link.length = 25 := by
    rw [esh]
    decide +kernel
  have SW := sw_finish h.scope h.reads O h.laid.value h.laid.planOk h25 a' nm hP hn hr hq
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  obtain ⟨p1, -, p3, p4, -, p6, -⟩ :=
    Meaning.K2.front_pin_fin h.scope h.reads O f₀ hq (q := k2P Zp a' nm .finish n) rfl hfx
  have hu : s.failed = none := by
    refine IM.noMark_reach h.scope h.reads O (reach_raw hr) (by omega) fun l' _ => ?_
    unfold IM.nAt
    split <;> omega
  have A : s.st.codes = Zp.first.codes :=
    (Meaning.K2.recAll_all h.scope h.reads O (plans_at h) (reach_raw hr) hu).codes
  exact call_of_ties hn armB_full.2 a' nm .finish
    (fun r hrw => p2At_fin h O hP hn hrw a' nm .finish) (SW.2 _ hfx)
    (p1.trans (A.symm.trans SW.1.codes)) (p1.trans W.codes) (by rw [p3, p4, esh]; rfl)
    (by rw [p6, esh])

/-- **THE FOUR TIES OF NUMBERS AT THE OUTPUT HEAD's PLACE.** -/
theorem head_nums_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s)) (a' : Place) (nm : String)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    n.seeds = (sendingAt (k2P Zp a' nm .head n) (headFrontOf s a Q.target)).seeds *
        ((sendingAt (k2P Zp a' nm .head n) (headFrontOf s a Q.target)).coordinates + 1) ∧
      (sendingAt (k2P Zp a' nm .head n) (headFrontOf s a Q.target)).answers = n.answers ∧
      n.logN = ((headFrontOf s a Q.target).st.codes.base.getD
        (headFrontOf s a Q.target).f.rows.code default).logN ∧ 0 < n.positions := by
  have hfx : VerifiableInference.Desc.First.K2.frontAt (k2P Zp a' nm .head n) s =
      some (headFrontOf s a Q.target) := frontAt_of (Or.inr (Or.inl ⟨rfl, a, Q, here, group, rfl⟩))
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  obtain ⟨p1, -, p3, p4, -, p6, -⟩ :=
    Meaning.K2.front_pin_head h.scope h.reads O f₀ (q := k2P Zp a' nm .head n) rfl hfx
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : Zp.first.shape = proofSizedFull.request := W.shape.trans OnBytes.Road.K4.shape_one
  exact nums_of_ties armNumsB_full.1 armB_full.1 a' nm .head
    (fun r hrw => p2At_head h O hP hn hrw a' nm .head) (p1.trans W.codes)
    (by rw [p3, p4, esh]; rfl) (by rw [p6, esh])

/-- **THE FOUR TIES OF NUMBERS BEHIND THE LAST SEGMENT.** -/
theorem fin_nums_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) {a : FinOwn} {Q : ReqGroup}
    (here : t.here = .fin a) (laid : a.G = some Q) :
    n.seeds = (sendingAt (k2P Zp a' nm .finish n) (finFrontOf t a Q)).seeds *
        ((sendingAt (k2P Zp a' nm .finish n) (finFrontOf t a Q)).coordinates + 1) ∧
      (sendingAt (k2P Zp a' nm .finish n) (finFrontOf t a Q)).answers = n.answers ∧
      n.logN = ((finFrontOf t a Q).st.codes.base.getD
        (finFrontOf t a Q).f.rows.code default).logN ∧ 0 < n.positions := by
  have hfx : VerifiableInference.Desc.First.K2.frontAt (k2P Zp a' nm .finish n) t =
      some (finFrontOf t a Q) := frontAt_of (Or.inr (Or.inr ⟨rfl, a, Q, here, laid, rfl⟩))
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : Zp.first.shape = proofSizedFull.request := W.shape.trans OnBytes.Road.K4.shape_one
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  obtain ⟨p1, -, p3, p4, -, p6, -⟩ :=
    Meaning.K2.front_pin_fin h.scope h.reads O f₀ hq (q := k2P Zp a' nm .finish n) rfl hfx
  exact nums_of_ties armNumsB_full.2 armB_full.2 a' nm .finish
    (fun r hrw => p2At_fin h O hP hn hrw a' nm .finish) (p1.trans W.codes)
    (by rw [p3, p4, esh]; rfl) (by rw [p6, esh])

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.armNumsB_full
#print axioms Johnson.AtFull.Shape.armNumsB_can_fail
#print axioms Johnson.AtFull.Shape.nums_of_ties
#print axioms Johnson.AtFull.Shape.head_nums_reached
#print axioms Johnson.AtFull.Shape.fin_nums_reached
#print axioms Johnson.AtFull.Shape.armB_full
#print axioms Johnson.AtFull.Shape.armB_can_fail
#print axioms Johnson.AtFull.Shape.call_of_ties
#print axioms Johnson.AtFull.Shape.p2At_fin
#print axioms Johnson.AtFull.Shape.head_four_reached
#print axioms Johnson.AtFull.Shape.fin_four_reached
