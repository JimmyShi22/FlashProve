-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Base.lean: THE DECISION OF THE CLOSING OF A SEGMENT SAYS YES AT EVERY LIST OF
ITS CHALLENGES, FROM FACTS ON THE RECORD IN FRONT OF IT THAT NAME NONE OF THEM. Theorems on the
verifier's own text (the kind's block, `Close.kind`, Johnson/Desc/First/Close/Kind.lean). It names no
frame of an honest side.

What is said. `CloseBase P s D` lists facts on the record s in front of the block and on the plan. NONE
NAMES AN ELEMENT THAT IS DRAWN OR SENT IN THE BLOCK's OWN ROUNDS. (`termsOk` and `rowsIn` ask of the
record's own coefficients, which earlier rounds' draws have made, that a written-out variable has the
pair (1, 1).) From them `CloseFront P s x _` (Johnson/Desc/K10/Honest/Front.lean) holds at EVERY element
x that "BAT" may draw (`closeFront_all`), and so the block's decision says yes at every list of 2 + k
rounds of the kind's shape (`close_yes_all`): under these facts there is no list of the block's own
challenges at which the decision refuses rounds of the kind's shape, whatever they show.

  `BaseData`        the link's shape and the group's record in the frame; the mask's number; the group
                    in the statement
  `CloseBase`       the facts. Of the statement: the group is there and in order (`GroupOk`); every row
                    that the test takes in (`runRows`: open rows and the members' sample rows) meets
                    what the adding of a row tests (`RowIn`), and each of its terms on a main table
                    is in order (`Tensor.ok`); the group has the frame's two codes; the mask code's
                    message length is a power of two; the group's main table has at most 63 index
                    bits. The rest: the guards that read no element, each under its name; three of
                    them (`shape`, `maskfits`, `spendAsMask`) at the statement behind the beginning of
                    the test, which is a function of the record in front
  `closeFront_all`, `close_yes_all`   the two theorems

By: `batch_returns`, `batch_rowfits` (Johnson/Desc/K10/Honest/RowFits.lean); `close_yes` (Front.lean);
`extends_begun`, `begun_group`, `GroupOk.extends`, `RowIn.extends`, `layoutOf_extends`, `layout_eq`
(Johnson/Desc/Means/Keeps.lean, Layout.lean); `spent_extends`
(Johnson/Desc/First/Close/Law/StBehind.lean); `layout_of_group` (Johnson/Desc/Own/LayoutAgree.lean).

Limits. OF THE BLOCK's DECISION (`Block.decide`) ALONE. The two tests that a block's step asks in front
of the decision (`Block.step`: the rounds' format; the columns): Johnson/Desc/K10/Honest/Step.lean. The
block's test on the plan (`planOk`) and what must have been sent before (`before`) are not spoken of;
the plan's h is read by no fact.
Whether the record that an honest run leaves in front of the block meets the facts is not said. What
the decision hands on is not said. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Front
import Johnson.Desc.K10.Honest.RowFits
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.Desc.Own.LayoutAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- What the facts speak of. -/
structure BaseData where
  L : Params.ReqLink
  Gq : ReqGroup
  /-- the fresh mask's number -/
  m : Nat
  /-- the segment's group in the statement -/
  G : Group

/-- The statement behind the beginning of the test. -/
def BaseData.S1 (D : BaseData) (s : Rec) : Statement := Slice.begun s.st s.frame.group D.G

/-- The shape of the fold, as `closeFrame` makes it. -/
def BaseData.F (D : BaseData) (s : Rec) : FoldShape :=
  ioppFoldShape { code := s.frame.shape.code, maskCode := s.frame.shape.maskCode, k := D.Gq.k,
                  h := D.Gq.h } (Own.layoutOf s.st D.G)

/-- **The facts in front of the closing that name none of its challenges.** -/
structure CloseBase (P : Par) (s : Rec) (D : BaseData) : Prop where
  owed : s.owed = none
  link : s.frame.shape.link[s.frame.link]? = some D.L
  group : s.frame.groups[s.frame.link]? = some D.Gq
  due : s.frame.next = .laterOrClose ∧ s.frame.moment = reqMoments D.L
  mask : s.frame.mask = some D.m
  beginRun : Ground.ok (Ground.beginRunL s.st s.frame.group) = true
  there : s.st.groups[s.frame.group]? = some D.G
  inOrder : GroupOk s.st D.G
  rowsIn : ∀ r ∈ (Slice.runRows s.st D.G).toList, RowIn s.st D.G r
  termsOk : ∀ r ∈ (Slice.runRows s.st D.G).toList, ∀ t ∈ r.terms.toList, t.part = .main →
    t.v.ok = true
  rows : P.rows = (Slice.runRows s.st D.G).size
  kh : (Own.layoutOf s.st D.G).k = D.Gq.k ∧ (Own.layoutOf s.st D.G).h = D.Gq.h
  stretch : P.k = D.Gq.k
  code : D.G.code = s.frame.shape.code
  maskCode : D.G.maskCode = s.frame.shape.maskCode
  power : (s.st.codes.mask.getD s.frame.shape.maskCode default).ell =
    2 ^ ceilLog2 (s.st.codes.mask.getD s.frame.shape.maskCode default).ell
  bits : (Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll ≤ 63
  shape : Own.foldShapeFits (D.S1 s) (D.F s) = true
  maskfits : Own.foldMaskFits (D.S1 s) (D.F s) D.m = true
  spendAsMask : Ground.ok (Ground.spendAsMaskL (D.S1 s) D.m) = true

theorem all_of_ok {l : Ground.Clauses} (h : Ground.ok l = true) : ∀ c ∈ l, c.2 = true :=
  fun c hc => List.all_eq_true.1 h c hc

/-- The two texts of a group's layout are one. -/
theorem layoutOf_same {S : Statement} {g : Nat} {G : Group} (hG : S.groups[g]? = some G) :
    Own.layoutOf S G = layoutOf S G :=
  Option.some.inj ((Own.layout_of_group hG).symm.trans (layout_eq S g G hG))

/-- **AT EVERY ELEMENT THAT "BAT" MAY DRAW THE FACTS IN FRONT HOLD.** -/
theorem closeFront_all {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (x : E) :
    ∃ D', CloseFront P s x D' := by
  have hE := extends_begun s.st s.frame.group D.G
  have hc : (D.S1 s).codes = s.st.codes := hE.codes
  have hG' := begun_group s.st s.frame.group D.G H.there
  have hOk' : GroupOk (D.S1 s) { D.G with inRun := true, rows := #[] } :=
    H.inOrder.extends hE rfl rfl rfl rfl
  have eL := layoutOf_same H.there
  have hL' : (D.S1 s).layout s.frame.group = some (Own.layoutOf s.st D.G) := by
    show (Slice.begun s.st s.frame.group D.G).layout s.frame.group = _
    rw [layout_eq _ _ _ hG', eL,
      layoutOf_extends (G' := { D.G with inRun := true, rows := #[] }) hE H.inOrder rfl rfl rfl rfl]
  have hr' : ∀ r ∈ (Slice.runRows s.st D.G).toList,
      RowIn (D.S1 s) { D.G with inRun := true, rows := #[] } r :=
    fun r h => RowIn.extends (G := D.G) hE (fun _ c => c) (H.rowsIn r h)
  obtain ⟨row, hrow⟩ := RowFit.batch_returns s.frame.group (Slice.runRows s.st D.G) x hG' hL' hOk' hr'
  have hfit : Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row = true :=
    RowFit.batch_rowfits hG' hL' hOk' hr' H.termsOk hrow (spent (D.S1 s) D.m) rfl
      (fun o ho => (spent_extends D.m (D.S1 s)).tableBits (hOk'.there o ho) .main) (D.F s) rfl rfl
      H.kh.1.symm H.kh.2.symm
      (by
        show ceilLog2 ((D.S1 s).codes.base.getD s.frame.shape.code default).ell = _
        rw [hc, ← H.code]
        rfl)
      (by
        show ((D.S1 s).codes.mask.getD s.frame.shape.maskCode default).ell = _
        rw [hc, H.power, ← H.maskCode]
        rfl) H.bits
  refine ⟨⟨D.L, D.Gq, D.m, ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩,
    { onSt s.st with st := D.S1 s }, { onSt (D.S1 s) with st := spent (D.S1 s) D.m }, row⟩,
    H.owed, H.link, H.group, H.due, H.mask, all_of_ok H.beginRun, ?_, H.rows, hrow, H.kh, H.stretch,
    H.shape, H.maskfits, all_of_ok H.spendAsMask, ?_, hfit⟩
  · show Ground.beginRunP (onSt s.st) s.frame.group = _
    unfold Ground.beginRunP
    have hb : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true := H.beginRun
    have ht : (onSt s.st).st.groups[s.frame.group]? = some D.G := H.there
    rw [if_pos hb, ht]
    rfl
  · show Ground.spendAsMaskP (onSt (D.S1 s)) D.m = _
    unfold Ground.spendAsMaskP
    have hb : Ground.ok (Ground.spendAsMaskL (onSt (D.S1 s)).st D.m) = true := H.spendAsMask
    rw [if_pos hb]
    rfl

/-- **FROM FACTS THAT NAME NONE OF ITS CHALLENGES THE BLOCK's DECISION SAYS YES AT EVERY LIST OF 2 + k
ROUNDS OF THE KIND's SHAPE.** -/
theorem close_yes_all {Cl : Type} {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) : ∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s' := by
  match rs, hl, hs with
  | rB :: rE :: rR, hl, hs =>
    obtain ⟨t, ht⟩ := hs.1.2.1
    obtain ⟨D', H'⟩ := closeFront_all H (E.ofTriple t)
    exact close_yes H' (rB :: rE :: rR) gs hl hs t (by simp [batDraw, ht]) rfl

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closeFront_all
#print axioms ProofFile.Honest.K10.YesFree.close_yes_all
