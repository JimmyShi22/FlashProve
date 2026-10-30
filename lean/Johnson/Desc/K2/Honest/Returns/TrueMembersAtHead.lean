-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/TrueMembersAtHead.lean: UNDER THE HEAD's PREMISE, AT A STATE REACHED
IN FRONT OF A CODE SWITCH, AT ALL THREE SORTS OF THE KIND's PLACES: THE CLOSED GROUP's MEMBERS AT
THEIR TRUE SHAPES (`membersTrue`, Carry/OfRows.lean) ARE THE WRITTEN LIST's, WITH THE WRITTEN FLAGS.
Statements with their proofs: calls; no definition.

The written list's members, as members:
  `(membersOf (loAt l)).map fun i => ⟨((loAt l).get i).1, kbW l i⟩`
(`loAt`, `kbW`: Johnson/LPFE1R/RowPubAt.lean: link l's written list and flags).

  `membersTrue_of_oracles` `membersTrue` reads of a statement its oracle messages alone
  `membersTrue_of_closing` THE CORE: `AtMgA` (the head's premise, Johnson/P5J/) · l < 25 · the
                    public part is a typed instance's · w is reached at the number of link l's
                    closing kind's own sub-protocol (`ixK10 l`) · a segment Lw is open at w ·
                    `closeFrame`, at Lw's frame and w's statement, returns u · T has grown out of
                    u.2 ⊢ `membersTrue T u.1.rows` is link l's written list's
  `link_membersTrue` m < 24, at a reached, in the head's own sense (`AtMg.rch`), at number 14 (m +
                    1) + 2: at a's statement and its walk's frame's carried rows: link m's
  `link_membersTrue_front` m < 23: the same at the front that the switch's block takes off that
                    state (`K2.frontAt p s = some fx`, where p stands at a segment's first place)
  `head_membersTrue_front` at the output head's front (339): link 23's
  `fin_membersTrue_front` at the front behind the last segment (353, behind its quiet step in
                    front): link 24's

The core's road: `closeFrame_groups` (Johnson/Desc/First/Close/Law/GroupsStay.lean): the carried
rows' layout names the members and flags of w's group · no mark stands at w (`noMark_reach_below`,
Johnson/IMR/NoMarkReach.lean; `number_is`, Johnson/Desc/K10/Honest/KeepsSeat.lean) ·
`AtMg.hinge_all` (Johnson/P5J/K10HXAt.lean) with `AtMgA.fold_full`
(Johnson/P5J/MaskLettersAtMg.lean): `ShapesAre` at w; `live_open` (Johnson/IMR/ListsAtDraw.lean) ·
`closeFrame_grows` (Johnson/Goal/Meaning/GrowsSeated.lean) · `shapesAre_grown`,
`membersTrue_of_shapes` (Carry/TrueOfShapes.lean). The ends' road: one run, several borders
(`reach_cuts_below`, Johnson/Top/H0/Walk/ReachCut.lean) · the closing is taken at w:
`closing_behind_laid` (Returns/SeatsWalk.lean), `closing_behind_cleared` (Returns/HeadSegment.lean)
· the front's carried rows and oracle messages: `front_pin_link`, `front_pin_head`
(Johnson/IMR/FrontPin.lean), `front_nums_head` (Johnson/IMR/HeadFront.lean), `front_nums_fin`
(Johnson/IMR/FinCount.lean) · from 338 to 339: `grows_front` (Johnson/IMR/GrowsFlat.lean),
`fold_next`.

NEAR, NOT CALLED: `members_behind_laid` (Returns/SeatsWalk.lean), `members_behind_cleared`
(Returns/HeadSegment.lean), `members_public` (Johnson/Desc/First/Close/Law/MembersPublic.lean): the
members AS NUMBERS, in ranges off counts of messages: nothing on shapes or flags · `tail_rows`
(Johnson/IMR/GroupTail.lean), `tail_rows_head` (Johnson/IMR/FinKept.lean): the layout's two lists
are the group's at an earlier border than the one at which `ShapesAre` is had. · `behind_of_close`
(Johnson/Desc/First/Link/Law/BehindOfClose.lean): from a return of `closeFrame` with `ShapesAre` in
front of it, at the state s' right behind, at whatever front `doorZ` and `K2.frontAt` give there:
each member's message, at its number `no`, has the written shape in `skelOf fx'`: member by member
and by number; no flag; s' is a letter, tied to no run.

Limits. "Reached" is by the chain's sub-protocols in their wrapped form. No run is given at which
the head's premise and "reached" hold together: as far as this file goes, the five laws under the
head could hold of nothing. Nothing on a prover. Nothing on rows' entries. The imports are heavy
(some 10 GiB). Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.SeatsWalk
import Johnson.Desc.K2.Honest.Returns.HeadSegment
import Johnson.IMR.FrontPin
import Johnson.IMR.HeadFront
import Johnson.IMR.FinCount
import Johnson.IMR.GrowsFlat
import Johnson.Desc.K2.Honest.Carry.TrueOfShapes
import Johnson.P5J.K10HXAt
import Johnson.P5J.MaskLettersAtMg
import Johnson.P5J.RchAtMg
import Johnson.IMR.NoMarkReach
import Johnson.IMR.ListsAtDraw
import Johnson.Top.H0.Walk.ReachCut
import Johnson.Desc.First.Close.Law.GroupsStay
import Johnson.Desc.K10.Honest.KeepsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (ShapesAre closeFrame_groups)
open VerifiableInference.Desc.LinkJoin (loAt kbW)
open VerifiableInference.Desc.Sound (below allOf EAll)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw reach_cuts_below)
open Meaning.K2 (closeFrame_grows live_open)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- `membersTrue` reads of a statement its oracle messages alone. -/
theorem membersTrue_of_oracles {T T' : Statement} (h : T'.oracles = T.oracles) (old : SingleRows) :
    membersTrue T' old = membersTrue T old := by
  unfold membersTrue
  rw [h]

/-- **THE CORE.** Under the head: w is reached in front of the closing kind's own sub-protocol of
link l; a segment Lw is open there; the frame's closing, at Lw's frame and w's statement, returns u;
T has grown out of u.2 ⊢ the members of u's carried rows, at their true shapes in T, are link l's
written list's. y: any strings. -/
theorem membersTrue_of_closing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {z : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub} (hty : h.toAtMg.typed z)
    (y : (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    {w : S} (hw : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (ixK10 l) (z, w))
    {Lw : Model.LinkCtx} (hLw : w.link? = some Lw) {owed : Option Nat} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {u : ReqFrame × Statement}
    (hx : First.Close.closeFrame owed Lw.check.frame w.st es rs = .ok u) {T : Statement}
    (hg : Grows u.2 T) :
    membersTrue T u.1.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map fun i =>
        ⟨((loAt l).get i).1, kbW l i⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, G₀, hG₀, em, ek⟩ := closeFrame_groups hx
  have e := ProofFile.Honest.K10.YesFree.number_is l
  have hu : w.failed = none := IM.noMark_reach_below h.scope h.reads O hw
    (by rw [e]; omega) (fun l' hl' => by rw [e]; unfold IM.nAt; split <;> split <;> omega)
  have H := h.toAtMg.hinge_all h.fold_full rfl hl ((z, w), y) ⟨hw, hty⟩ hu G₀
    (by
      show w.st.groups[w.live.frame.group]? = some G₀
      rw [live_open hLw]
      exact hG₀)
  exact membersTrue_of_shapes (shapesAre_grown
    (Grows.trans (closeFrame_grows (f' := u.1) (T' := u.2) hx) hg) H) _ em ek

/-- **At a state reached at number 14 (m + 1) + 2**: at the state's own statement and its walk's
frame's carried rows. Below m = 23 a code switch stands at that number, the one that opens the next
group; for m = 23 (338) the sub-protocol that enters the output head does, and the code switch
stands at 339. -/
theorem link_membersTrue (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h24 : m < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) :
    membersTrue a.1.2.st a.1.2.check.frame.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt m)).map fun i =>
        ⟨((loAt m).get i).1, kbW m i⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts (14 * m + 12) (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, hg⟩ :=
    closing_behind_laid h.scope h.reads O (l := m) h24 f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 m = 14 * m + 12 := by
    rw [ProofFile.Honest.K10.YesFree.number_is m, if_neg (by omega)]
  rw [hf]
  exact membersTrue_of_closing h (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx hg

/-- **The same at the front that the switch's block takes off that state.** -/
theorem link_membersTrue_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat}
    (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : First.K2.P2} (hq : p.stands = .link)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx) :
    membersTrue fx.st fx.f.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt m)).map fun i =>
        ⟨((loAt m).get i).1, kbW m i⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -, -, -, a6, -⟩ :=
    Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega) (by omega) f hq hfx
  rw [a6, membersTrue_of_oracles a2]
  exact link_membersTrue h (by omega) a hr

/-- **At the output head's front** (339): the closed group is segment 23's. -/
theorem head_membersTrue_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : First.K2.P2} (hq : p.stands = .head)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx) :
    membersTrue fx.st fx.f.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt 23)).map fun i =>
        ⟨((loAt 23).get i).1, kbW 23 i⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨tm, rm, cm, hm, fm⟩ := cuts 338 (by omega)
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O f₀ hq hfx
  obtain ⟨-, -, a3, -⟩ := Meaning.K2.front_nums_head h.scope h.reads O fm f₀ hq hfx
  have hlen : 338 < cF.blocksInOrder.length := by
    have := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold.1
    omega
  obtain ⟨rs0, gs0, d0⟩ := Meaning.K2.fold_next (List.getElem?_eq_getElem hlen) fm f₀
  have hgr : Grows tm.st a.1.2.st :=
    IM.grows_front h.scope h.reads O (by omega) (List.getElem?_eq_getElem hlen) _ _ _ _ d0
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 334 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, hg⟩ :=
    closing_behind_laid h.scope h.reads O (l := 23) (by omega) fm
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 23 = 334 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 23, if_neg (by omega)]
  rw [a3, membersTrue_of_oracles a2, hf]
  exact membersTrue_of_closing h (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx
    (hg.trans hgr)

/-- **At the front behind the last segment** (353, behind its quiet step in front): the closed group
is segment 24's. -/
theorem fin_membersTrue_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S} (he : First.K2.finishFrontQ a.1.2 = .ok t)
    {p : First.K2.P2} (hq : p.stands = .finish) {fx : _root_.Tw.K2.Front}
    (hfx : First.K2.frontAt p t = some fx) :
    membersTrue fx.st fx.f.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt 24)).map fun i =>
        ⟨((loAt 24).get i).1, kbW 24 i⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨-, -, a3, a4, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f₀ he hq hfx
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 350 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, hg⟩ :=
    closing_behind_cleared h.scope h.reads O f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 24 = 350 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 24, if_pos rfl]
  rw [a3, membersTrue_of_oracles a4, hf]
  exact membersTrue_of_closing h (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx hg

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.membersTrue_of_oracles
#print axioms VerifiableInference.Desc.K2.Honest.Returns.membersTrue_of_closing
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_membersTrue
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_membersTrue_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_membersTrue_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_membersTrue_front
