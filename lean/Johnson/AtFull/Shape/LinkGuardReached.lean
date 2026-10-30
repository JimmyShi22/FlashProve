-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkGuardReached.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: THE
GUARD ON THE PLAN's NUMBERS AND THE CHAIN's SHAPE (linkB, Johnson/Desc/First/Shape/SwitchLinkB.lean;
linkP, SwitchLinkFits.lean) AND THE TEST ON THE ONES (onesV) AT EVERY STATE THAT IS REACHED THERE,
WHOEVER PLAYS: FROM THREE FACTS ON THE BOOK's TREES, WHICH STAY PREMISES HERE. Under the head
P5J.AtMgA, at an opening O in the head's letters, and where the plan's numbers at the place return
(hP, hn). A joining of laws; nothing is evaluated here.

What it is for. The frame of the switch in the table of steps returns under that guard. Its clauses
read the state and the plan alone, so they are meant to hold at every reached state. Here each is
laid in by its payer: another group's files on the kind's law at a reached state
(Johnson/Desc/K2/Honest/Returns/), and LinkLeftPlan.lean, LinkLeftNums.lean, LinkPlanNums.lean. The
way from the clauses to the two Bools is SwitchLinkBack.lean's.

  `noRound`, `dummyIn p s L Q`: a round in which nothing is sent or drawn; what the reading of the
    old rows is handed at two such rounds and no column: a letter for the clauses of ReadFits that
    read no round. Its carried rows are s.check.frame.rows and its book is s.book, by unfolding: so
    idsOf and treesOf at it read s alone, and hOwn's "for all L, Q", its p, a, nm and the two empty
    rounds cost a payer nothing.
  **`linkB_reached`**: linkB (k2P Zp a nm .link n) (chainF s) and onesV s.st s.check.frame.rows
    accept, from hOwn: each tree that holds one of the old messages holds old messages alone
    (ReadFits.own).
  **`linkP_reached`**: linkP (k2P Zp a nm .link n) (chainF s) accepts, from hShapes (treesShapeB:
    each such tree is in the book, its sampled parts fit, it has not been opened where it may be
    opened once, it is no deeper than the range) and hRead (the plan's list of trees read is, tree
    for tree: the tree's number less the first tree's, cut off at 0; its depth; its width). hShapes
    is asked at the code that the frame's shape names; linkP looks up the carried rows' code: the
    two meet because link_fields_reached gives one code at both.
  **`linkGd_reached`**: THE TABLE's OWN GUARD AT A LINK's SWITCH (linkGd, SwitchReturns.lean: no
    mark · linkB · linkP) accepts, from the three; no mark by noMark_at_switch (LinkLeftPlan.lean).

Limits. THE THREE FACTS ON THE BOOK ARE PREMISES HERE; LinkGuardLeaf.lean pays the first, and one
clause of the second's four. "Reached" is over the list of the wrapped sub-protocols. The links'
places alone: nothing at 339 or 353. The full size alone. It stands over another house's files
Johnson/Desc/K2/Honest/Returns/. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkPlanNums
import Johnson.Desc.First.Shape.SwitchLinkBack
import Johnson.Desc.K2.Honest.Returns.LinkRest
import Johnson.Desc.K2.Honest.Returns.TargetReached
import Johnson.AtFull.Shape.SwitchReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K2 (P2 par9)
open VerifiableInference.Desc.K2.Honest.Returns
open VerifiableInference.Desc.Ground.Sh (stSh bookSh)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf sw_link)
open IM (k2P)
open _root_.Tw.K2 (SwIn switchNotices)
open _root_.Desc.K14.Law (secondAt seatZ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- A round in which nothing is sent and nothing is drawn. -/
def noRound : Fmt.RoundView := ⟨[], ⟨[], [], [], none⟩⟩

/-- What the reading of the old rows is handed at two empty rounds and no column. -/
def dummyIn (p : P2) (s : S) (L : Params.ReqLink) (Q : ReqGroup) : SwIn :=
  inFront (par9 p) (frontAt s L Q) s.book (sentOf p s L Q noRound noRound) noRound []

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {z : ProofFile.InstPub}

/-- **THE TEST ON THE PLAN AND THE SHAPE, AND THE TEST ON THE ONES, AT A REACHED STATE.** -/
theorem linkB_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String)
    (hOwn : ∀ L Q, ∀ t ∈ treesOf (dummyIn (k2P Zp a nm .link n) s L Q), ∀ tree,
      (dummyIn (k2P Zp a nm .link n) s L Q).book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList, q ∈ (idsOf (dummyIn (k2P Zp a nm .link n) s L Q)).toList) :
    linkB (k2P Zp a nm .link n) (chainF s) = true ∧ onesV s.st s.check.frame.rows = true := by
  have hS := h.scope
  have hR := h.reads
  have hF := h.laid.value
  have hpl := h.laid.planOk
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h.toAtMg O
  obtain ⟨L, Q, c₀, z₀, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ :=
    link_fields_reached hS hR O hF hpl h23 hP hn hr a nm
  have hfirst := link_first_reached hS hR O h23 hr
  have hx := link_front_at hS hR O hF hpl h23 hP hn hr hfirst f4 f5
  have SH := link_shape_reached hS hR O hF hpl hy hcut hB h23 hr hx
  have PB := link_public_reached hS hR O hF hpl hy hcut hB h23 hr hx
  obtain ⟨m1, m2, m3⟩ := link_members_reached hS hR O h23 hr L Q
  obtain ⟨b1, b2⟩ := link_book_reached hS hR O h23 hr L Q (par9 (k2P Zp a nm .link n))
    (sentOf (k2P Zp a nm .link n) s L Q noRound noRound) noRound []
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := (link_lay_reached hS hR O h23 hr L Q).reads
    (i := dummyIn (k2P Zp a nm .link n) s L Q) rfl rfl
  obtain ⟨-, -, g, k⟩ := link_target_reached hS hR O hF hpl h23 hP hn hr L f5
  have hN := (sw_link hS hR O hF hpl h23 hP hn hr).2 _ hx
  obtain ⟨pl, ow⟩ := link_two_reached h h23 (reach_raw hr) Q f4
  have hIn : ∀ v ∈ (Positions.ofDraws c₀.logN []).all.toList,
      v < 2 ^ ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logN := by
    intro v hv
    have e : (Positions.ofDraws c₀.logN []).all.toList = [] := rfl
    rw [e] at hv
    cases hv
  exact linkB_of_state (p := k2P Zp a nm .link n) (c := c₀) rfl f1 f2
    (link_waits_reached hS hR O h23 hr) hfirst f3 f4 f5 f6 f7 f8 pl f9
    (by rw [hN]; exact link_entry_reached h O h23 hP hn hr a nm f4 f5)
    (link_plan_reached h h23 (reach_raw hr) _ L f5) f10
    (link_trees_reached h O h23 hP hn hr a nm f4 f5) f11
    (readFitsB_of (dummyIn (k2P Zp a nm .link n) s L Q) (f12 _ _ _) l1 l2 l3 l4 l5 b1 b2
      (hOwn L Q) l6 l7 l8)
    { check := SH.check, restMain := PB.restMain
      fits :=
        { mainVars := SH.mainVars, d0 := SH.d0, d1 := SH.d1, rows := m1, named := m2
          once := SH.once, keptCode := SH.keptCode
          stored := link_stored_reached hS hR O hF hpl h23 hP hn hr L Q }
      keptPos := f13, keptAnswers := PB.keptAnswers, lengths := PB.lengths, logC := PB.logC
      logZ := PB.logZ, inRange := hIn, groupCode := g, copiesCode := k
      tables :=
        { bitsG := PB.bitsG, bitsKept := SH.bitsKept
          claimMain := link_claimMain_reached hS hR O h23 hr L Q, claimKept := m3
          stored := link_tables_paid hS hR O hF hpl hy hcut hB h23 hr hx f13 }
      reads := link_reads_paid hS hR O hF hpl hy hcut hB h23 hr hx }
    ow

/-- **THE FURTHER TEST ON THE PLAN AND THE SHAPE AT A REACHED STATE.** -/
theorem linkP_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String)
    (hShapes : ∀ c : Code, s.st.codes.base[s.check.frame.shape.code]? = some c → treesShapeB
      (withGroupS (stSh s.st) s.check.frame.shape.code s.check.frame.shape.maskCode)
      (bookSh s.book) c.logN (treesOfS (bookSh s.book) (singleSh s.check.frame.rows)) = true)
    (hRead : readsOfS (bookSh s.book) Zp.P.firstTree
      (treesOfS (bookSh s.book) (singleSh s.check.frame.rows)) = some n.read) :
    linkP (k2P Zp a nm .link n) (chainF s) = true := by
  obtain ⟨L, Q, c₀, z₀, -, -, -, f4, f5, f6, -, -, -, -, f11, -, -⟩ :=
    link_fields_reached h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr a nm
  obtain ⟨e1, -, -, -⟩ := link_nums_reached h O h23 hP hn hr (k2P Zp a nm .link n) f4 f5
  obtain ⟨t1, t2, t3⟩ := link_ties_reached h O h23 hP hn hr a nm f4 f5 f6
  exact linkP_of_state (p := k2P Zp a nm .link n) (L := L) f5 f11 e1 t1.symm t2 t3 (hShapes c₀ f6)
    hRead

/-- **THE TABLE's OWN GUARD AT A LINK's SWITCH** (linkGd, SwitchReturns.lean: no mark · linkB ·
linkP) at a reached state, from the three facts on the book. -/
theorem linkGd_reached (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String)
    (hOwn : ∀ L Q, ∀ t ∈ treesOf (dummyIn (k2P Zp a nm .link n) s L Q), ∀ tree,
      (dummyIn (k2P Zp a nm .link n) s L Q).book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList, q ∈ (idsOf (dummyIn (k2P Zp a nm .link n) s L Q)).toList)
    (hShapes : ∀ c : Code, s.st.codes.base[s.check.frame.shape.code]? = some c → treesShapeB
      (withGroupS (stSh s.st) s.check.frame.shape.code s.check.frame.shape.maskCode)
      (bookSh s.book) c.logN (treesOfS (bookSh s.book) (singleSh s.check.frame.rows)) = true)
    (hRead : readsOfS (bookSh s.book) Zp.P.firstTree
      (treesOfS (bookSh s.book) (singleSh s.check.frame.rows)) = some n.read) :
    linkGd (k2P Zp a nm .link n) (chainF s) = true := by
  have hu := noMark_at_switch h (reach_raw hr)
  have e : (chainF s).1.marked = false := by
    show s.failed.isSome = false
    rw [hu]
    rfl
  unfold linkGd
  rw [e, (linkB_reached h O h23 hP hn hr a nm hOwn).1,
    linkP_reached h O h23 hP hn hr a nm hShapes hRead]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.noRound
#print axioms Johnson.AtFull.Shape.dummyIn
#print axioms Johnson.AtFull.Shape.linkB_reached
#print axioms Johnson.AtFull.Shape.linkP_reached
#print axioms Johnson.AtFull.Shape.linkGd_reached
