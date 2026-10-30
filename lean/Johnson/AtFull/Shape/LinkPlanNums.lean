-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkPlanNums.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: FOUR
TIES BETWEEN THE PLAN's NUMBERS AT THE PLACE AND WHAT THE FRAME HOLDS, AT EVERY STATE THAT IS
REACHED THERE: the first four clauses of the further test on the plan and the shape (linkP,
Johnson/Desc/First/Shape/SwitchLinkFits.lean), in the letters of the front's term: round 1 draws as
many elements as the seeds take · round 2 holds as many answers as the sending takes · the
positions' range is the old main code's · a position is drawn. Under the head P5J.AtMgA.

How. The place's two entries are the written row's (p2At_head, LinkLeftNums.lean); the front's
notices are a closed term on the written shape, and the state's codes are the written ones
(sent_reached; atSwitch_reached): so each is a closed test at the first 23 written rows.

  `sendW cs N`: the shared sending's public letter at codes cs and notices N. `entry1 r`: a written
    row's second entry.
  `numsAtB m l`, `numsB`, `numsB_full`, `numsB_can_fail`: the closed test, that it accepts at the
    23, and that it can fail at a row that is there.
  **`link_nums_reached`**: the four. **`link_ties_reached`**: three of them in a second form:
    (sendingAt (k2P …) (frontAt s L Q)).answers = n.answers · n.logN = c₀.logN at the look-up of the
    frame's shape's code · 0 < n.positions.

THE DEVICE. The two closed facts are closed by "decide +kernel" under a raised maxRecDepth.

Limits. linkP's two last clauses, on the trees in the book, are not touched. The four are stated on
the state, not yet on its shape. "Reached" is over the list of the wrapped sub-protocols. Of a
reached state: that anything is reached is not said. Of the other premises: an O follows from the
head (h.laid.opened); hP and hn have the library's t3_nums_link, at 1 ≤ l < 24
(Johnson/P1K2R/TieThreeConst.lean); neither is joined here. That the look-ups hL, hQ and hc return
at such a state is not shown here. The links' places alone; the full size alone. That the head has a
member is shown at named sets of public files alone, in a side library. At the format's second
hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkLeftNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit P2At)
open VerifiableInference.Desc.K2.Honest.Returns (frontAt sendingAt)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open _root_.Tw.K2 (switchNotices)
open _root_.Desc.K14.Law (secondAt seatZ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- The shared sending's public letter at codes cs and notices N. -/
def sendW (cs : Codes) (N : Array OracleNotice) : VerifiableInference.Desc.K1.Par :=
  { place := default, codes := cs, gp := ⟨0, 0⟩, work := 0, parts := [("", N)] }

/-- A written row's second entry. -/
def entry1 (r : SwRow) : Fmt.Entry :=
  ((r.specs.map fun y => (y.round r.set .request).entry : List Fmt.Entry).getD 1 { name := "" })

/-- The written row m's two entries against the sending at link l's notices. -/
def numsAtB (m l : Nat) : Bool :=
  let P := sendW proofSizedFull.codes
    (sentAt proofSizedFull.request (reqGroups proofSizedFull.request) l)
  (tableFullLit[m]?).any fun r =>
    (entry0 r).drawE == P.seeds * (P.coordinates + 1) && (entry1 r).answers == P.answers &&
      decide (0 < (entry1 r).poss)

/-- At the row's own link. -/
def numsB (m : Nat) : Bool := numsAtB m (m + 1)

set_option maxRecDepth 1000000 in
/-- Lean's kernel says yes at the first 23 written rows. -/
theorem numsB_full : (List.range 23).all numsB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail at a row that is there: the first written row against a link that is not
there, where no notice is laid. Which of the first two comparisons says no is not told; the third
clause reads no link, and is shown no failing case. -/
theorem numsB_can_fail : numsAtB 0 99 = false ∧ (tableFullLit[0]?).isSome = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {z : ProofFile.InstPub}

/-- **THE FOUR AT A REACHED STATE.** q: any numbers of a place; the sending's three numbers do not
read them. -/
theorem link_nums_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (q : VerifiableInference.Desc.First.K2.P2) {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    n.seeds =
        (sendingAt q (frontAt s L Q)).seeds * ((sendingAt q (frontAt s L Q)).coordinates + 1) ∧
      n.answers = (sendingAt q (frontAt s L Q)).answers ∧
      n.logN = (s.st.codes.base.getD s.check.frame.rows.code default).logN ∧ 0 < n.positions := by
  obtain ⟨e1, -, e3⟩ := sent_reached h O h23 hP hn hr hL hQ
  have A := atSwitch_reached h (by omega : m + 1 < 25) (reach_raw hr)
    (noMark_at_switch h (reach_raw hr))
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have k := List.all_eq_true.1 numsB_full m (List.mem_range.2 h23)
  have kl := List.all_eq_true.1 logB_full m (List.mem_range.2 h23)
  unfold numsB numsAtB at k
  unfold logB logAtB at kl
  cases hrw : tableFullLit[m]? with
  | none =>
    rw [hrw] at k
    cases k
  | some r =>
    rw [hrw] at k kl
    have k' : ((entry0 r).drawE ==
        (sendW proofSizedFull.codes (sentAt proofSizedFull.request
          (reqGroups proofSizedFull.request) (m + 1))).seeds *
        ((sendW proofSizedFull.codes (sentAt proofSizedFull.request
          (reqGroups proofSizedFull.request) (m + 1))).coordinates + 1) &&
      (entry1 r).answers == (sendW proofSizedFull.codes (sentAt proofSizedFull.request
          (reqGroups proofSizedFull.request) (m + 1))).answers &&
      decide (0 < (entry1 r).poss)) = true := k
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at k'
    obtain ⟨⟨k1, k2⟩, k3⟩ := k'
    have kl' : r.g.main.logN =
      (proofSizedFull.codes.base.getD proofSizedFull.request.code default).logN := beq_iff_eq.1 kl
    have H2 := p2At_head h O hP hn hrw ⟨1, none, 0, .K2⟩ "" .link
    have a1 : n.seeds = (entry0 r).drawE :=
      congrArg (fun l : List Fmt.Entry => (l.getD 0 { name := "" }).drawE) H2
    have a2 : n.answers = (entry1 r).answers :=
      congrArg (fun l : List Fmt.Entry => (l.getD 1 { name := "" }).answers) H2
    have a3 : n.positions = (entry1 r).poss :=
      congrArg (fun l : List Fmt.Entry => (l.getD 1 { name := "" }).poss) H2
    have eS : sendW s.st.codes (switchNotices (frontAt s L Q).T (frontAt s L Q).others) =
        sendW proofSizedFull.codes (sentAt proofSizedFull.request
          (reqGroups proofSizedFull.request) (m + 1)) := by
      rw [e1, e3, A.codes, W.codes]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show n.seeds = (sendW s.st.codes (switchNotices (frontAt s L Q).T
        (frontAt s L Q).others)).seeds * ((sendW s.st.codes (switchNotices (frontAt s L Q).T
        (frontAt s L Q).others)).coordinates + 1)
      rw [eS, a1, k1]
    · show n.answers = (sendW s.st.codes (switchNotices (frontAt s L Q).T
        (frontAt s L Q).others)).answers
      rw [eS, a2, k2]
    · rw [A.codes, (A.rows (by omega)).1, W.codes, W.shape, OnBytes.Road.K4.shape_one, ← kl']
      exact H2.logN
    · rw [a3]
      exact k3

/-- **THREE OF THE TIES IN A SECOND FORM**: the sending's answers are the plan's · the plan's range
of positions is the code's that the frame's shape names, at that code's own look-up · a position is
drawn. -/
theorem link_ties_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) :
    (sendingAt (k2P Zp a nm .link n) (frontAt s L Q)).answers = n.answers ∧ n.logN = c₀.logN ∧
      0 < n.positions := by
  obtain ⟨-, e2, e3, e4⟩ := link_nums_reached h O h23 hP hn hr (k2P Zp a nm .link n) hL hQ
  have A := atSwitch_reached h (by omega : m + 1 < 25) (reach_raw hr)
    (noMark_at_switch h (reach_raw hr))
  refine ⟨e2.symm, ?_, e4⟩
  rw [e3, (A.rows (by omega)).1, ← A.shape, Array.getD_eq_getD_getElem?, hc]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.link_ties_reached
#print axioms Johnson.AtFull.Shape.numsB_full
#print axioms Johnson.AtFull.Shape.numsB_can_fail
#print axioms Johnson.AtFull.Shape.link_nums_reached
