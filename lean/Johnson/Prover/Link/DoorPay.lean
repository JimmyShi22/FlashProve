-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorPay.lean: THE FORM's HALF AT THE LINK: FROM THE SIX FRONT BLOCKS' YES TO THE
PREMISES OF THE DOOR INTO THE PROXIMITY TEST: TestFront (Johnson/Prover/Link/FormFirst.lean),
BatOwes (FormBat.lean) and FrontOwes (FormDoor.lean), which door_yes (FormDoorLaws.lean) asks, at
the record that the test's block makes of the record behind "LINK phi".

The road. The yes of the format's fold over the link's blocks 0 to 5, at the chain's start, gives
the library's record of facts on a link's five rounds (LinkRanR, OnBytes/Slice/BlkLinkRanRec.lean),
by K15's law (k15_ran, Johnson/Desc/K15/K15Law.lean): the statement and the book behind in closed
form. The door's clauses are read off that form. What they leave on the plan's public numbers is one
record of premises, DoorPlan.

Main names (namespace Johnson.Prover.Link).
  enter_t12Of   the record that the test's block makes (enter, Johnson/Desc/Link/LinkDesc.lean) is
      the library's t12Of (Johnson/Desc/K15/HsemOf.lean).
  fold6, ran_of_front   THE ROAD.
  linkSt_size   how many oracle messages stand behind the steps. (On the book:
      Johnson/Prover/Link/BookLaid.lean.)
  ran_group, ran_oracle0, ran_oracle1, ran_oracle2, ran_layout, ran_count, ran_size, ran_place,
  ran_tree   the record of facts, looked up.
  DoorPlan S K p cur nxt i n   THE PLAN's SHARE: facts on the link's public shape, the codes and the
      place's numbers alone.
  testFront_of_ran   TestFront's twenty clauses; "in order" is a premise.
  batOwes_of_ran   BatOwes' six; the count and the two tests behind the batching are premises.
  front_of_ran, frontOwes_of_ran   the front's nineteen clauses; FrontOwes' four; the roots and the
      open rows' clauses are premises.
  door_premises   THE THREE AT THE CHAIN's START, and LinkRanR with them.

By calls: k15_ran; sendK1_under, sendPOfDecide, foldBlocks_mono (Johnson/Desc/K15/SendOwnLaw.lean,
SendOwnPaid.lean); linkSt_groupR, linkSt_oracle0, linkSt_oracle1, linkSent_oracles, LinkRanR.plain,
runRows_eq, codes, rows_pos (OnBytes/Slice/BlkLinkRan.lean, BlkLinkRanRec.lean,
BlkLinkHeadRec.lean); linkSt_oracle2 (BlkLinkSeat.lean); linkSt_layout, linkLay_k (BlkLinkLay.lean);
layout_eq (Johnson/Desc/Means/Layout.lean); padMade_eq (Johnson/Desc/Own/SendAgree.lean);
bookSent_sizes, stSent_size (BlkProxKeeps.lean); treesSent_at, partsLaid_keep
(Johnson/Prover/Link/BookLaid.lean); layTrees_fits (Johnson/Desc/Book/BookFits.lean);
denseRow_of_plain (OnBytes/Slice/BlkProxDense.lean).

Limits. door_premises HAS FIVE PREMISES. AT THE FULL SIZE EACH IS PAID, IN link_yes' OWN PROOF:
DoorPlan: doorPlan_full (Johnson/Prover/Link/DoorPlanFull.lean) · THE TWO TESTS ON THE RECORD BEHIND
THE BATCHING (gpOk, labelsOk: Johnson/Desc/K12/Law/FirstOk.lean, FirstCut.lean): door_premises'
(DoorPayGp.lean) takes the public test gpPlanOk in their place; gpPlan_full (DoorGpMembers.lean) ·
LinkSeats, whose field "rows" is FrontOwes' (Johnson/Prover/Link/FormSeats.lean), "in order" and the
count of the group's open rows: front6_walks_full (FormWalks.lean), with the six blocks' yes; the
count reaches the premise's form by rows_count_of (DoorFull.lean). The road: door_full
(DoorFull.lean), bodyInv0_full (BodyInv0Full.lean), inv0_full (LinkJoinF.lean), linkYes_of
(LinkJoinE.lean). AT OTHER SIZES THE FIVE STAY PREMISES AND THE STATEMENTS MAY BE IDLE (a member of
DoorPlan at a toy: doorPlan_toy, DoorPlanToy.lean). NO MEMBER IS PROVED IN THIS FILE. That the six
blocks say yes is not proved here (at the full size: front6_walks_full; under premises, with
LinkSeats: front6_whole, FormSendGave.lean). Nothing on values. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormDoorLaws
import Johnson.Prover.Link.FormSeats
import Johnson.Desc.K15.SendOwnPaid
import Johnson.Desc.K15.K15Law
import Johnson.Desc.K15.HsemOf
import OnBytes.Slice.BlkLinkHeadRec
import OnBytes.Slice.BlkLinkLay
import Johnson.Prover.Link.BookLaid
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Slice.BlkProxKeeps
import OnBytes.Slice.BlkSentSeat
import Johnson.Desc.Book.BookFits
import Johnson.Desc.Own.SendAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 (St P15 frontBlock blocksOr blocksOrV first entries ctxOf parK1 t12Of)
open OnBytes.Slice.ProxRun (denseRow_of_plain)

/-! ## 1 The road to the library's record of facts -/

/-- The record that the test's block makes of the link's carried record (enter,
Johnson/Desc/Link/LinkDesc.lean) is the library's t12Of (Johnson/Desc/K15/HsemOf.lean). -/
theorem enter_t12Of (d : St) : Desc.K15.enter d = .ok (t12Of d) := rfl

/-- The fold over the six seated blocks says yes: so does the fold over the blocks that the laws
speak of, with the same end. (foldV, Johnson/Desc/K15/SendOwnLaw.lean, without the tail.) -/
theorem fold6 (P : P15) (hl : P.codes.lengthsOk = true)
    (hpl : VerifiableInference.Desc.K1.planOkOwn (parK1 P) = true) (s : St) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (out : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (frontBlock P :: blocksOrV P) s rs cols = .ok out) :
    foldBlocks 0 (frontBlock P :: blocksOr P) s rs cols = .ok out := by
  cases he : entries P with
  | none => rw [Desc.K15.blocksV_none P he] at h; exact h
  | some es =>
    obtain ⟨_, _, rfl⟩ := Desc.K15.entries_inv P es he
    rw [Desc.K15.blocksV_eq P _ he] at h
    rw [Desc.K15.blocks_eq P _ he]
    refine foldBlocks_mono 0 _ _ ?_ s rs cols out h
    refine .cons (StepUnder.refl 0 _) (.cons (StepUnder.refl 0 _)
      (.cons (Desc.K15.sendK1_under Desc.K15.sendPOfDecide P hl hpl) ?_))
    exact Desc.K15.forall₂_refl _ (StepUnder.refl 0) _

/-- **THE ROAD**: from the six front blocks' yes at the chain's start to LinkRanR
(OnBytes/Slice/BlkLinkRanRec.lean). -/
theorem ran_of_front (P : P15) (x : TableKey × TableKey) (hl : P.codes.lengthsOk = true)
    (hpl : VerifiableInference.Desc.K1.planOkOwn (parK1 P) = true) (hs : P.set.samples = 1)
    (es5 : List Fmt.Entry) (he : entries P = some es5) (es : List Fmt.Entry) (d' : St)
    (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn) (hi0 : x.1.item = 0) (hi1 : x.2.item = 1)
    (kok : linkOk P.codes P.S 1 = true)
    (h : foldBlocks 0 (frontBlock P :: blocksOrV P) (first P.codes x) rs cols =
      .ok (d', rest, cols')) :
    ∃ X D, LinkRanR P.S x.1 x.2 (ctxOf es (first P.codes x) rs cols)
        (ctxOf (es.drop 5) d' rest cols') X D ∧
      X.group = d'.loc.g ∧ X.mask = d'.loc.firstMask :=
  Desc.K15.k15_ran P hs es5 he es (first P.codes x) d' rs rest cols cols' hi0 hi1 kok
    (fold6 P hl hpl _ _ _ _ h)

/-! ## 2 The statement behind the steps, looked up: how many messages -/

section
variable (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
  (rows0 rows1 : List Row) (rE : Row)

/-- The steps make no oracle message beside the one message's. -/
theorem linkSt_size :
    (linkSt S T places s0 s1 rows0 rows1 rE).oracles.size =
      T.oracles.size + (linkMessage S 1).size := by
  unfold linkSt
  rw [(withRow_oracles _ _ _).1, (withRows_oracles _ _ _).1, (withRows_oracles _ _ _).1]
  unfold Slice.withMessageInGroup admitted
  simp only [Array.size_modify]
  exact ProxRun.stSent_size _ _

end

/-! ## 3 The record of facts, looked up -/

section Ran
variable {S : LinkShape} {first further : TableKey} {c c1 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D)

include hR

theorem ran_group : c1.st.groups[x.group]? =
    some (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) := by
  rw [hR.st, hR.group]
  exact linkSt_groupR S c.st D.places _ _ D.rec0 D.rec1 D.rows0 D.rows1 D.rE

theorem ran_oracle0 : c1.st.oracles[c.st.oracles.size]? =
    some (linkOracle S c.st D.places c.st.groups.size { D.row0 with target := D.y0 }) := by
  rw [hR.st]
  exact linkSt_oracle0 S c.st D.places _ _ _ D.rows1 D.rE

theorem ran_oracle1 : c1.st.oracles[c.st.oracles.size + 1]? =
    some (linkOracle S c.st D.places c.st.groups.size { D.row1 with target := D.y1 }) := by
  rw [hR.st]
  exact linkSt_oracle1 S c.st D.places _ _ _ D.rows1 D.rE

theorem ran_oracle2 (hm : S.masksAhead = true) : c1.st.oracles[c.st.oracles.size + 2]? =
    some { shape := (foldMaskNotice (linkFoldShape S)).shape } := by
  rw [hR.st]
  exact linkSt_oracle2 S c.st D.places _ _ _ D.rows1 D.rE hm

/-- The layout that the description's laws speak of is the library's closed form. -/
theorem ran_layout :
    layoutOf c1.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) =
      linkLay S c.st := by
  have h1 := layout_eq c1.st x.group _ (ran_group hR)
  have h2 : c1.st.layout x.group = some (linkLay S c.st) := by
    rw [hR.st, hR.group]
    exact linkSt_layout S c.st D.places _ _ _ D.rows1 D.rE hR.rows_pos
  exact Option.some.inj (h1.symm.trans h2)

/-- The test takes in the group's open rows and the two members' sample rows. -/
theorem ran_count :
    (runRows c1.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)).size =
      (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size).rows.size + 2 := by
  rw [hR.st, hR.runRows_eq, List.size_toArray]
  simp [LinkDataR.rowsR, linkGrpR, linkGrp]
  omega

theorem ran_size : c1.st.oracles.size = c.st.oracles.size + (linkMessage S 1).size := by
  rw [hR.st]
  exact linkSt_size S c.st D.places _ _ _ D.rows1 D.rE

/-- Where the book has the i-th oracle message of the one message. -/
theorem ran_place (i : Nat) (hi : i < (linkMessage S 1).size) :
    c1.book.place[c.st.oracles.size + i]? =
      some (c.book.trees.size + D.lay.tree.getD i 0, D.lay.part.getD i 0) := by
  rw [hR.book, hR.placed]
  show (c.book.place ++ (Array.range (linkMessage S 1).size).map _)[c.book.place.size + i]? = _
  rw [Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Array.getElem?_map, Array.getElem?_range, if_pos hi]
  rfl

/-- The tree in which it lies: one of the message's own: its shape, its number; opened at no
list. -/
theorem ran_tree (i : Nat) (hi : i < (linkMessage S 1).size) :
    ∃ (T : Tree) (sh : TreeShape),
      c1.book.trees[c.book.trees.size + D.lay.tree.getD i 0]? = some T ∧
      D.lay.shapes[D.lay.tree.getD i 0]? = some sh ∧ T.shape = sh ∧
      T.number = c.ch.firstTree + (c.ch.roots + D.lay.tree.getD i 0) ∧ T.lists = 0 := by
  have hlt := (VerifiableInference.Desc.Book.layTrees_fits hR.laid i hi).1
  have hk := partsLaid_keep (linkMessage S 1) D.lay c.st.oracles.size c.book.trees.size
    (treesSent c.ch.firstTree D.lay.shapes.toList c.ch.roots c.book.trees)
    (c.book.trees.size + D.lay.tree.getD i 0)
  rw [treesSent_at, Array.getElem?_toList, Array.getElem?_eq_getElem hlt] at hk
  rw [hR.book]
  show ∃ (T : Tree) (sh : TreeShape), (partsLaid _ _ _ _ _)[_]? = some T ∧ _
  cases hT : (partsLaid (linkMessage S 1) D.lay c.st.oracles.size c.book.trees.size
      (treesSent c.ch.firstTree D.lay.shapes.toList c.ch.roots c.book.trees))[c.book.trees.size +
        D.lay.tree.getD i 0]? with
  | none => rw [hT] at hk; cases hk
  | some T =>
    rw [hT] at hk
    have e := Option.some.inj hk
    exact ⟨T, _, rfl, Array.getElem?_eq_getElem hlt, congrArg (·.1) e, congrArg (·.2.1) e,
      congrArg (·.2.2) e⟩

end Ran

/-! ## 4 The plan's share, and the door's premises -/

/-- **THE PLAN's SHARE OF THE DOOR's PREMISES**: facts on the link's public shape S, the codes K and
the place's numbers p alone. -/
structure DoorPlan (S : LinkShape) (K : Codes) (p : P12) (cur nxt : Fmt.M1.Stage)
    (i n : Nat × Nat) : Prop where
  ahead : S.masksAhead = true
  idx0 : p.idx[0]? = some i
  idx1 : p.idx[1]? = some n
  code : S.code = i.1
  maskCode : S.maskCode = i.2
  base : K.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩
  maskC : K.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩
  base1 : K.base[n.1]? = some ⟨nxt.C.a, nxt.C.l, nxt.C.r⟩
  mask1 : K.mask[n.2]? = some ⟨nxt.Z.a, nxt.Z.l, nxt.Z.r⟩
  layK : ceilLog2 S.rows + 1 = cur.k
  layH : cur.h = 0
  freshRows : (foldMaskNotice (linkFoldShape S)).shape.maskRows = 2 ^ cur.h
  freshCode : (foldMaskNotice (linkFoldShape S)).shape.maskCode = i.2
  stage : K12.stageOk false cur = true
  stage1 : nxt.Z.a ≤ nxt.C.a
  vars : cur.k + ceilLog2 cur.C.l ≤ 63
  early : p.early = true
  codes : codesFit p { codes := K } = true
  pub : H2K.Pub.pubOk p K = true
  free : p.nums.free = 1
  one : ∀ l, layTrees K (linkMessage S 1) = some l → l.shapes.size = 1

/-- Guard (w) reads the statement's codes alone. -/
theorem codesFit_congr (p : P12) (st st' : Statement) (h : st.codes = st'.codes) :
    codesFit p st = codesFit p st' := by
  unfold codesFit
  rw [h]

section Door
variable {S : LinkShape} {first further : TableKey} {c c1 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D) {p : P12} {cur nxt : Fmt.M1.Stage} {i n : Nat × Nat}
  (Pl : DoorPlan S c.st.codes p cur nxt i n) {t : T12} (hst : t.st = c1.st)
  (hg : t.g = x.group) (hm : t.mask = x.mask)

include hR Pl hst hg hm

/-- **TestFront BEHIND THE LINK's STEPS**, from the library's record of facts, the plan's share and
"in order". -/
theorem testFront_of_ran (ho : InOrder t.st) :
    TestFront p cur nxt t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) i n
      (c.st.oracles.size + 2) where
  group := by rw [hst, hg]; exact ran_group hR
  order := ho
  dense := fun r hr => denseRow_of_plain (hR.plain r (by
    rw [hst, hR.st, hR.runRows_eq] at hr
    exact hr))
  idx0 := Pl.idx0
  idx1 := Pl.idx1
  code := Pl.code
  maskCode := Pl.maskCode
  base := by rw [hst, hR.codes]; exact Pl.base
  maskC := by rw [hst, hR.codes]; exact Pl.maskC
  base1 := by rw [hst, hR.codes]; exact Pl.base1
  mask1 := by rw [hst, hR.codes]; exact Pl.mask1
  layK := by rw [hst, ran_layout hR, (linkLay_k S c.st).1]; exact Pl.layK
  layH := by rw [hst, ran_layout hR, (linkLay_k S c.st).2]; exact Pl.layH.symm
  main := ⟨0, Nat.zero_lt_two, _, by rw [hst]; exact ran_oracle0 hR, hR.rows_pos⟩
  noKept := fun j => match j with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  mask := by rw [hm, hR.mask, if_pos Pl.ahead]
  fresh := ⟨_, by rw [hst]; exact ran_oracle2 hR Pl.ahead, rfl, Pl.freshRows, Pl.freshCode, rfl,
    rfl, rfl, by simp [linkGrpR, linkGrp]⟩
  stage := Pl.stage
  stage1 := Pl.stage1
  vars := Pl.vars

/-- **BatOwes BEHIND THE LINK's STEPS**; the count of the batched rows and the two tests on the
record behind the batching stay premises here. -/
theorem batOwes_of_ran (cut : List Fmt.DeclaredRound) (hp : t.pass = .nothing)
    (hcount : ∀ d ∈ cut, d.entry.rows = (runRows t.st
      (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)).size)
    (hgp : ∀ row : GroupRow, row.kept = #[] →
      H2K.First.gpOk p (batT t
        (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row) = true ∧
      H2K.First.labelsOk p (batT t
        (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row) = true) :
    BatOwes p cut t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) where
  pass := hp
  early := Pl.early
  codes := (codesFit_congr p t.st { codes := c.st.codes } (by rw [hst, hR.codes])).trans Pl.codes
  idle := rfl
  count := hcount
  gp := hgp

/-- The front's nineteen clauses behind the link's steps. -/
theorem front_of_ran (hb : t.book = c1.book) :
    ∀ cl ∈ frontL t.st t.book t.g t.mask, cl.2 = true := by
  have hG : t.st.groups[t.g]? =
      some (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) := by
    rw [hst, hg]; exact ran_group hR
  have h0 := ran_oracle0 hR
  have h1 := ran_oracle1 hR
  have h2 := ran_oracle2 hR Pl.ahead
  rw [← hst] at h0 h1 h2
  have hmk : t.mask = some (c.st.oracles.size + 2) := by rw [hm, hR.mask, if_pos Pl.ahead]
  have hsz : (linkMessage S 1).size = 3 := by simp [linkMessage, Pl.ahead]
  have hK : t.st.codes = c.st.codes := by rw [hst, hR.codes]
  have hgg : t.g = c.st.groups.size := hg.trans hR.group
  have hans : (rowShape S).answers = 1 := rfl
  have hfa : (foldMaskNotice (linkFoldShape S)).shape.answers = 0 := rfl
  have hpad : Own.padMade t.st.codes (rowShape S) = some D.places := by
    rw [hK, Own.padMade_eq]; exact hR.pad
  have hkind : ∀ r ∈ (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size).rows.toList,
      r.kind ≠ .sample := by
    intro r hr
    have hr' : r ∈ (D.rec0 ++ (D.rec1 ++ D.rows0)) ++ D.rows1 ++ [D.rE] := by
      simpa [linkGrpR, linkGrp] using hr
    rcases List.mem_append.1 hr' with hr' | hr'
    · rcases List.mem_append.1 hr' with hr' | hr'
      · rcases List.mem_append.1 hr' with hr' | hr'
        · rw [recRowsR_kind _ _ _ _ _ hR.rec0 r hr']; decide
        · rcases List.mem_append.1 hr' with hr' | hr'
          · rw [recRowsR_kind _ _ _ _ _ hR.rec1 r hr']; decide
          · rw [columnRows_kind _ _ _ _ _ _ _ _ hR.rows0 r hr']; decide
      · rw [columnRows_kind _ _ _ _ _ _ _ _ hR.rows1 r hr']; decide
    · rw [List.mem_singleton.1 hr', (eqRow_target _ _ _ _ _ _ hR.eqRow).2]; decide
  have hstep : t.st.oracles.size = t.book.place.size := by
    rw [hst, hb, ran_size hR, hR.book, (ProxRun.bookSent_sizes c _ _).2, hR.placed]
  have htree : ∀ i, i < 3 → ∃ T : Tree,
      ((t.book.place[c.st.oracles.size + i]?).bind fun q => t.book.trees[q.1]?) = some T ∧
        T.lists = 0 := by
    intro i hi
    obtain ⟨T, sh, a, -, -, -, e⟩ := ran_tree hR i (by rw [hsz]; exact hi)
    refine ⟨T, ?_, e⟩
    rw [hb, ran_place hR i (by rw [hsz]; exact hi)]
    exact a
  obtain ⟨T0, a0, l0⟩ := htree 0 (by decide)
  obtain ⟨T1, a1, l1⟩ := htree 1 (by decide)
  obtain ⟨T2, a2, l2⟩ := htree 2 (by decide)
  rw [Nat.add_zero] at a0
  intro cl hcl
  unfold frontL at hcl
  simp only [hG, hmk, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 1
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 2
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 3
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 4
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 5
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 6
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 7
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 8
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 9
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 10
  · show (Ground.on (some _) fun G : Group => G.rows.all fun r => r.kind != RowKind.sample) = true
    show ((linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size).rows.all
      fun r => r.kind != RowKind.sample) = true
    rw [← Array.all_toList]
    exact List.all_eq_true.2 fun r hr => bne_iff_ne.2 (hkind r hr) -- 11
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 12
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 13
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 14
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 15
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 16
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 17
  · clear htree hkind
    first
      | rfl
      | (simp [Ground.on, linkGrpR, linkGrp, h0, h1, h2, linkOracle, hpad, hstep, hgg, hans, hfa,
           a0, a1, a2, l0, l1, l2]
         done) -- 18
  · show (([c.st.oracles.size, c.st.oracles.size + 1] ++ [c.st.oracles.size + 2]).all fun o =>
      Ground.on ((t.book.place[o]?).bind fun q => t.book.trees[q.1]?)
        fun T => !T.oneList || T.lists == 0) = true
    refine List.all_eq_true.2 fun o ho => ?_
    have ho' : o = c.st.oracles.size ∨ o = c.st.oracles.size + 1 ∨ o = c.st.oracles.size + 2 := by
      simpa using ho
    rcases ho' with rfl | rfl | rfl
    · rw [a0]; simp [Ground.on, l0]
    · rw [a1]; simp [Ground.on, l1]
    · rw [a2]; simp [Ground.on, l2] -- 19

/-- **FrontOwes BEHIND THE LINK's STEPS**; the open rows' clauses stay a premise here. -/
theorem frontOwes_of_ran (hb : t.book = c1.book) (hroots : p.nums.free = t.roots)
    (hrows : ∀ row ∈
      (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size).rows.toList,
      K9L.RowClauses t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row) :
    FrontOwes p t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) where
  roots := hroots
  front := front_of_ran hR Pl hst hg hm hb
  rows := hrows
  pub := by rw [hst, hR.codes]; exact Pl.pub

end Door

/-! ## 5 At the chain's start -/

/-- **FROM THE SIX FRONT BLOCKS' YES TO THE DOOR's PREMISES**, at the record that the test's block
makes of the record behind "LINK phi". With them the library's record of facts itself. -/
theorem door_premises (P : P15) (x : TableKey × TableKey) {p : P12} {cur nxt : Fmt.M1.Stage}
    {i n : Nat × Nat} (Pl : DoorPlan P.S P.codes p cur nxt i n) (hl : P.codes.lengthsOk = true)
    (hpl : VerifiableInference.Desc.K1.planOkOwn (parK1 P) = true) (hs : P.set.samples = 1)
    (es5 : List Fmt.Entry) (he : entries P = some es5) (es : List Fmt.Entry)
    (hi0 : x.1.item = 0) (hi1 : x.2.item = 1) (kok : linkOk P.codes P.S 1 = true) (d' : St)
    (G' : Group) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
    (h : foldBlocks 0 (frontBlock P :: blocksOrV P) (first P.codes x) rs cols =
      .ok (d', rest, cols'))
    (hS : LinkSeats P.par d' G') (ho : InOrder d'.st) (cut : List Fmt.DeclaredRound)
    (hcount : ∀ d ∈ cut, d.entry.rows = G'.rows.size + 2)
    (hgp : ∀ row : GroupRow, row.kept = #[] →
      H2K.First.gpOk p (batT (t12Of d') G' row) = true ∧
        H2K.First.labelsOk p (batT (t12Of d') G' row) = true) :
    TestFront p cur nxt (t12Of d') G' i n 2 ∧ BatOwes p cut (t12Of d') G' ∧
      FrontOwes p (t12Of d') G' ∧
      ∃ X D, LinkRanR P.S x.1 x.2 (ctxOf es (first P.codes x) rs cols)
        (ctxOf (es.drop 5) d' rest cols') X D ∧ X.group = d'.loc.g ∧
        X.mask = d'.loc.firstMask := by
  obtain ⟨X, D, hR, e1, e2⟩ :=
    ran_of_front P x hl hpl hs es5 he es d' rs rest cols cols' hi0 hi1 kok h
  have hG : G' = linkGrpR P.S D.rec0 D.rec1 D.rows0 D.rows1 D.rE 0 := by
    have a := hS.group
    have b := ran_group hR
    rw [e1] at b
    exact Option.some.inj (a.symm.trans b)
  subst hG
  have hroots : p.nums.free = (t12Of d').roots := by
    rw [Pl.free]
    have a : d'.roots = 0 + D.lay.shapes.size := hR.roots
    rw [Pl.one D.lay hR.laid] at a
    exact a.symm
  exact ⟨testFront_of_ran hR Pl rfl e1.symm e2.symm ho,
    batOwes_of_ran hR Pl rfl e1.symm e2.symm cut rfl
      (fun d hd => (hcount d hd).trans (ran_count hR).symm) hgp,
    frontOwes_of_ran hR Pl rfl e1.symm e2.symm rfl hroots hS.rows, X, D, hR, e1, e2⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.enter_t12Of
#print axioms Johnson.Prover.Link.fold6
#print axioms Johnson.Prover.Link.ran_of_front
#print axioms Johnson.Prover.Link.linkSt_size
#print axioms Johnson.Prover.Link.ran_count
#print axioms Johnson.Prover.Link.ran_size
#print axioms Johnson.Prover.Link.ran_place
#print axioms Johnson.Prover.Link.ran_tree
#print axioms Johnson.Prover.Link.ran_group
#print axioms Johnson.Prover.Link.ran_oracle0
#print axioms Johnson.Prover.Link.ran_oracle1
#print axioms Johnson.Prover.Link.ran_oracle2
#print axioms Johnson.Prover.Link.ran_layout
#print axioms Johnson.Prover.Link.testFront_of_ran
#print axioms Johnson.Prover.Link.codesFit_congr
#print axioms Johnson.Prover.Link.batOwes_of_ran
#print axioms Johnson.Prover.Link.front_of_ran
#print axioms Johnson.Prover.Link.frontOwes_of_ran
#print axioms Johnson.Prover.Link.door_premises
