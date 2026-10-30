-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkLeftNums.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: THREE
MORE PREMISES OF THE LAW "THE KIND's OWN DECISION SAYS YES" AT A REACHED STATE (LinkLeft and he,
Johnson/Desc/K2/Honest/Returns/LinkAtReached.lean) THAT TIE THE PLAN's NUMBERS AT THE PLACE TO WHAT
THE FRAME HOLDS: trees · the entry's test · FrontCore.inRange. Under the head P5J.AtMgA.

How. The plan's maker lays the number of roots as the number of trees of its own list of notices at
its own codes (numsAt's text, Johnson/Desc/ProofFile/Lot/K2OfPlan.lean); at a reached state that
list is the front's and these codes are the state's (sw_link, Johnson/P1K2R/HstReached.lean): so
"trees" holds with nothing evaluated. For the other two the place's two entries are the written
row's (p2At_table, Johnson/P1K2R/P2AtTable.lean; tableWrittenB_head,
Johnson/Top/H0/K2Ties/AtHead3.lean), and the front's notices and the old code are closed terms on
the written shape and codes (LinkLeftPlan.lean's road): two closed tests.

  `numsAt_roots`: what numsAt lays as roots. `sentAt sh G l`, `sent_is`: the front's notices as a
    term on the frame's shape, groups and link's number. `entry0 r`: a written row's first entry.
  `p2At_head`: under the head: P2At r (IM.k2P Zp a nm st n) at the written row r of the place, at
    every a, nm, st.
  `sent_reached`: at a reached state the front's notices are the plan's list n.sent, the state's
    codes are n.codes, and n.sent is sentAt at the written shape.
  **`link_trees_reached`**. (It and the next ask the two look-ups hL, hQ of the frame's own segment
    and group, to call sent_reached.)
  `entryAtB m l`, `entryB`, `entryB_full`, `entryB_can_fail`; **`link_entry_reached`**: planOk1 none
    n.sent (par9 …).eSeed = true.
  `logAtB m c`, `logB`, `logB_full`, `logB_can_fail`; **`link_inRange_reached`**: from "every
    position drawn is below 2 ^ n.logN" (LinkPlain.range).

THE DEVICE. The four closed facts are closed by "decide +kernel" under a raised maxRecDepth.

Limits. "Reached" is over the list of the wrapped sub-protocols. Of a reached state: that anything
is reached is not said. inRange keeps one premise on the second round's draws. The links' places
alone; the full size alone. It stands over another group's files that are not of the library
(Returns/PinReached.lean, Returns/FirstReached.lean). That the head has a member is shown in scope,
where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that
these three hold together, at two named sets of public files, in a side library. At the format's
second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkLeftPlan
import Johnson.Desc.K2.Honest.Returns.FirstReached
import Johnson.P1K2R.P2AtTable
import Johnson.Top.H0.K2Ties.AtHead3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (par9)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit P2At tableWritten_is)
open VerifiableInference.Desc.K2.Honest.Returns (frontAt sendingAt sendingAt_sent link_front_at
  link_first_reached)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf sw_link p2At_table)
open IM (k2P)
open _root_.Tw.K2 (switchNotices)
open _root_.Desc.K14.Law (secondAt seatZ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 Tools -/

/-- What the plan's maker lays as the number of roots. The library has the same sentence under the
name P1K2.numsAt_roots (Johnson/Top/H0/Tw/K2C/PieceTrees.lean), in a module that this file does not
import. -/
theorem numsAt_roots {Pp : Prep} {link : Option Nat} {n : Nums} (h : numsAt Pp link = some n) :
    ∃ lay, layTrees n.codes n.sent = some lay ∧ n.roots = lay.shapes.size := by
  unfold numsAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, _, lay, hl, rd, _, rfl⟩ := h
    exact ⟨lay, hl, rfl⟩

/-- The front's notices, as a term on the frame's shape, groups and link's number. -/
def sentAt (sh : Params.ReqShape) (G : Array ReqGroup) (l : Nat) : Array OracleNotice :=
  let f : ReqFrame := { shape := sh, groups := G, link := l }
  match G[l]? with
  | some Q => switchNotices Q.target
      (ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape l {})])
  | none => #[]

/-- The front's notices are that term at the frame's own three. -/
theorem sent_is {s : S} (L : Params.ReqLink) {Q : ReqGroup}
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    switchNotices (frontAt s L Q).T (frontAt s L Q).others =
      sentAt s.check.frame.shape s.check.frame.groups s.check.frame.link := by
  unfold sentAt
  rw [hQ]
  rfl

/-- A written row's first entry. -/
def entry0 (r : SwRow) : Fmt.Entry :=
  ((r.specs.map fun y => (y.round r.set .request).entry : List Fmt.Entry).getD 0 { name := "" })

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {z : ProofFile.InstPub}

/-- **Under the head the place's two entries are the written row's.** -/
theorem p2At_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {r : SwRow} (hr : tableFullLit[m]? = some r)
    (a : Place) (nm : String) (st : VerifiableInference.Desc.First.K2.At) :
    P2At r (k2P Zp a nm st n) :=
  p2At_table (tableWritten_is (VerifiableInference.Desc.First.K2Ties.tableWrittenB_head h))
    h.laid.pub O.blank hP hr (a := ⟨1, some (m + 1), 1, .K2⟩) (nm := nm) (st := st) rfl hn

/-- The front's notices at a reached state are the plan's list, and the closed term. -/
theorem sent_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    switchNotices (frontAt s L Q).T (frontAt s L Q).others = n.sent ∧ s.st.codes = n.codes ∧
      n.sent = sentAt proofSizedFull.request (reqGroups proofSizedFull.request) (m + 1) := by
  have SW := sw_link h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr
  have hx := link_front_at h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr
    (link_first_reached h.scope h.reads O h23 hr) hL hQ
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : s.check.frame.shape = proofSizedFull.request :=
    SW.1.shape.trans (W.shape.trans OnBytes.Road.K4.shape_one)
  have e1 := SW.2 _ hx
  refine ⟨e1, SW.1.codes, ?_⟩
  rw [← e1, sent_is L hQ, SW.1.groups, SW.1.link, esh]

/-! ## 2 "trees" -/

/-- **THE CLAUSE "trees" AT A REACHED STATE**: nothing is evaluated. -/
theorem link_trees_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    ((layTrees (sendingAt (k2P Zp a nm .link n) (frontAt s L Q)).codes
      (sendingAt (k2P Zp a nm .link n) (frontAt s L Q)).sent).getD {}).shapes.size =
      (par9 (k2P Zp a nm .link n)).eSeed.roots := by
  obtain ⟨e1, e2, -⟩ := sent_reached h O h23 hP hn hr hL hQ
  obtain ⟨lay, hl, er⟩ := numsAt_roots hn
  rw [sendingAt_sent, e1]
  show ((layTrees s.st.codes n.sent).getD {}).shapes.size = n.roots
  rw [e2, hl, er]
  rfl

/-! ## 3 The entry's test -/

/-- The written row m's first entry draws as many elements that must not be 0 as the most answers of
a notice of the front at link l. -/
def entryAtB (m l : Nat) : Bool :=
  (tableFullLit[m]?).any fun r => (entry0 r).drawNZ ==
    _root_.Desc.Plain.answersMax
      (sentAt proofSizedFull.request (reqGroups proofSizedFull.request) l)

/-- At the row's own link. -/
def entryB (m : Nat) : Bool := entryAtB m (m + 1)

set_option maxRecDepth 1000000 in
/-- Lean's kernel says yes at the first 23 written rows. -/
theorem entryB_full : (List.range 23).all entryB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail: the first written row against a link that is not there, where no notice
is laid. -/
theorem entryB_can_fail : entryAtB 0 99 = false ∧ (tableFullLit[0]?).isSome = true := by
  decide +kernel

/-- **THE ENTRY's TEST AT THE PLAN's OWN LIST.** -/
theorem link_entry_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    planOk1 none n.sent (par9 (k2P Zp a nm .link n)).eSeed = true := by
  obtain ⟨-, -, e3⟩ := sent_reached h O h23 hP hn hr hL hQ
  have k := List.all_eq_true.1 entryB_full m (List.mem_range.2 h23)
  unfold entryB entryAtB at k
  cases hrw : tableFullLit[m]? with
  | none =>
    rw [hrw] at k
    cases k
  | some r =>
    rw [hrw] at k
    have k' : ((entry0 r).drawNZ == _root_.Desc.Plain.answersMax
      (sentAt proofSizedFull.request (reqGroups proofSizedFull.request) (m + 1))) = true := k
    have eN : n.nonZero = (entry0 r).drawNZ :=
      congrArg (fun l : List Fmt.Entry => (l.getD 0 { name := "" }).drawNZ)
        (p2At_head h O hP hn hrw a nm .link)
    rw [← eN, ← e3] at k'
    show ((none : Option Nat).all (· == 0) && ("SEND seed" == "SEND seed") &&
      (n.nonZero == _root_.Desc.Plain.answersMax n.sent) && ((0 : Nat) == 0)) = true
    rw [k']
    rfl

/-! ## 4 "inRange" -/

/-- The written row m's range of positions is that of the written code number c. -/
def logAtB (m c : Nat) : Bool :=
  (tableFullLit[m]?).any fun r => r.g.main.logN == (proofSizedFull.codes.base.getD c default).logN

/-- At the written shape's main code. -/
def logB (m : Nat) : Bool := logAtB m proofSizedFull.request.code

set_option maxRecDepth 1000000 in
/-- Lean's kernel says yes at the first 23 written rows. -/
theorem logB_full : (List.range 23).all logB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail: the first written row against a code that is not there. -/
theorem logB_can_fail : logAtB 0 99 = false ∧ (tableFullLit[0]?).isSome = true := by
  decide +kernel

/-- **THE CLAUSE "inRange"**, from the clause "range" on the second round's draws. -/
theorem link_inRange_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (r₂ : Fmt.RoundView) (range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ n.logN) (L : Params.ReqLink)
    (Q : ReqGroup) (c : Code) :
    ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
      v < 2 ^ ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logN := by
  have A := atSwitch_reached h (by omega : m + 1 < 25) (reach_raw hr)
    (noMark_at_switch h (reach_raw hr))
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have k := List.all_eq_true.1 logB_full m (List.mem_range.2 h23)
  unfold logB logAtB at k
  cases hrw : tableFullLit[m]? with
  | none =>
    rw [hrw] at k
    cases k
  | some r =>
    rw [hrw] at k
    have k' : r.g.main.logN =
      (proofSizedFull.codes.base.getD proofSizedFull.request.code default).logN := beq_iff_eq.1 k
    have eL : n.logN = r.g.main.logN := (p2At_head h O hP hn hrw ⟨1, none, 0, .K2⟩ "" .link).logN
    intro v hv
    have hv' : v ∈ listOfT r₂.drawn.poss := by simpa [Positions.ofDraws] using hv
    rw [listOfT_eq, Fmt.listOf_mem] at hv'
    show v < 2 ^ (s.st.codes.base.getD s.check.frame.rows.code default).logN
    rw [A.codes, (A.rows (by omega)).1, W.codes, W.shape, OnBytes.Road.K4.shape_one, ← k', ← eL]
    exact range v hv'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sent_reached
#print axioms Johnson.AtFull.Shape.link_trees_reached
#print axioms Johnson.AtFull.Shape.entryB_full
#print axioms Johnson.AtFull.Shape.entryB_can_fail
#print axioms Johnson.AtFull.Shape.link_entry_reached
#print axioms Johnson.AtFull.Shape.logB_full
#print axioms Johnson.AtFull.Shape.logB_can_fail
#print axioms Johnson.AtFull.Shape.link_inRange_reached
#print axioms Johnson.AtFull.Shape.numsAt_roots
#print axioms Johnson.AtFull.Shape.sent_is
#print axioms Johnson.AtFull.Shape.p2At_head
