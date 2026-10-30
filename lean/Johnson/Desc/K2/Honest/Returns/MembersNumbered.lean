-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/MembersNumbered.lean: THE NUMBERS OF THE MEMBERS OF THE GROUP THAT A
CODE SWITCH's CARRIED ROWS NAME ARE THE LIBRARY's OWN NUMBERS OF THE LINK's WRITTEN LIST (`noK10`,
Johnson/Desc/First/Close/Law/NoOfLink.lean: the place of the member's seat in the plan's list of
seats): under the head's premise, at a reached state, at all three sorts of the kind's places.
Statements with their proofs; no definition. Over the library alone.

  `membersNumbered_of_closing` THE CORE: `AtMgA` · l < 25 · the public part typed · w reached at
                    `ixK10 l` · a segment Lw open at w · `closeFrame` at Lw's frame and w's
                    statement returns u ⊢ `u.1.rows.layout.members.toList = (membersOf (loAt l)).map
                    (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l)`
  `link_membersNumbered` m < 24: the same of the walk's frame's carried rows at a state reached at
                    14 (m + 1) + 2
  `link_membersNumbered_front` m < 23: of `fx.f.rows`, at the front that the switch's block takes
                    off that state
  `head_membersNumbered_front` at the output head's front (339): link 23's list
  `fin_membersNumbered_front` at the front behind the last segment (353, behind its quiet step in
                    front): link 24's list

Why. A claim on the carried rows reads a witness's words at these numbers (`wordsFirst`,
Johnson/Desc/Sound/WordsAt.lean: from a message's number, through the state's book, to its seat, and
from the seat to the witness's own number of the message). `hs_k10` (NoOfLink.lean) gives the seat
at a number of the form `noK10 …`: so the numbers are wanted in that form.

By, all the library's: `AtMg.hinge_all` (Johnson/P5J/K10HXAt.lean): `ShapesAre` at K10's own number,
with that numbering; its field `members` is what is handed on · `closeFrame_groups`
(Johnson/Desc/First/Close/Law/GroupsStay.lean): the carried layout names the group's members ·
`closing_behind_laid` (Returns/SeatsWalk.lean), `closing_behind_cleared` (Returns/HeadSegment.lean)
· `noMark_reach_below` (Johnson/IMR/NoMarkReach.lean) · `number_is`
(Johnson/Desc/K10/Honest/KeepsSeat.lean) · `reach_cuts_below` (Johnson/Top/H0/Walk/ReachCut.lean) ·
`front_pin_link`, `front_nums_head`, `front_nums_fin`.

NEAR, NOT CALLED. `shapesAre_noK10` (Johnson/Desc/First/Close/Law/ShapesAtNoK10.lean),
`shapesAre_at_head` (Johnson/LPFK10R/ShapesAtHead.lean), `members_public_zero`
(Johnson/Desc/First/Close/Law/ShapesReachedZero.lean): of the statement's group IN FRONT OF the
closing, at K10's own place · `t3_at_cut` (Johnson/Desc/First/Close/Law/MembersAtFull.lean): the
public list of a link's members is this numbering, at links 1 to 23 · the field `member` of
`FrontFitsAt` (Johnson/Desc/First/Link/Law/CarryAtFull.lean): `fx.f.rows.layout.members[ix a]? =
some (no a)`: a field of a bundle that the laws on what stands behind the closing pay at a
transcript's stage · `members_behind_laid`, `members_behind_cleared`: the same members as stretches
of numbers from the count of oracle messages in front of the opening switch on.

Limits. No run is given at which the head's premise and "reached" hold together: the five laws could
hold of nothing. "Reached": by the sub-protocols in their wrapped form. Nothing on the fresh mask's
number. Nothing on a seat, a book or a witness: the numbers alone. THE FIVE PROOFS WALK AS THOSE OF
A SISTER FILE ON THE MEMBERS' SHAPES (Returns/TrueMembersAtHead.lean):
typed again, with another last line. The full size and the format's second hash function
alone. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.SeatsWalk
import Johnson.Desc.K2.Honest.Returns.HeadSegment
import Johnson.IMR.FrontPin
import Johnson.IMR.HeadFront
import Johnson.IMR.FinCount
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
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (ShapesAre closeFrame_groups noK10)
open VerifiableInference.Desc.LinkJoin (loAt kbW)
open VerifiableInference.Desc.Sound (below allOf EAll)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw reach_cuts_below)
open Meaning.K2 (live_open)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE CORE.** Under the head: w is reached in front of the closing kind's own sub-protocol of
link l; a segment Lw is open there; the frame's closing, at Lw's frame and w's statement, returns u
⊢ the numbers of the members of u's carried rows are the library's own numbers of link l's written
list: each the place of the member's seat in the plan's list of seats. y: any strings. -/
theorem membersNumbered_of_closing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (hl : l < 25) {z : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub} (hty : h.toAtMg.typed z)
    (y : (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    {w : S} (hw : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (ixK10 l) (z, w))
    {Lw : Model.LinkCtx} (hLw : w.link? = some Lw) {owed : Option Nat} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {u : ReqFrame × Statement}
    (hx : First.Close.closeFrame owed Lw.check.frame w.st es rs = .ok u) :
    u.1.rows.layout.members.toList =
      (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map
        (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, G₀, hG₀, em, -⟩ := closeFrame_groups hx
  have e := ProofFile.Honest.K10.YesFree.number_is l
  have hu : w.failed = none := IM.noMark_reach_below h.scope h.reads O hw
    (by rw [e]; omega) (fun l' hl' => by rw [e]; unfold IM.nAt; split <;> split <;> omega)
  have H := h.toAtMg.hinge_all h.fold_full rfl hl ((z, w), y) ⟨hw, hty⟩ hu G₀
    (by
      show w.st.groups[w.live.frame.group]? = some G₀
      rw [live_open hLw]
      exact hG₀)
  rw [em]
  exact H.members

/-- **At a state reached at number 14 (m + 1) + 2**: at its walk's frame's carried rows. -/
theorem link_membersNumbered (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h24 : m < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) :
    a.1.2.check.frame.rows.layout.members.toList =
      (VerifiableInference.Desc.First.Close.membersOf (loAt m)).map
        (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts (14 * m + 12) (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, -⟩ :=
    closing_behind_laid h.scope h.reads O (l := m) h24 f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 m = 14 * m + 12 := by
    rw [ProofFile.Honest.K10.YesFree.number_is m, if_neg (by omega)]
  rw [hf]
  exact membersNumbered_of_closing h (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx

/-- **The same at the front that the switch's block takes off that state.** -/
theorem link_membersNumbered_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat}
    (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : First.K2.P2} (hq : p.stands = .link)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx) :
    fx.f.rows.layout.members.toList =
      (VerifiableInference.Desc.First.Close.membersOf (loAt m)).map
        (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, -, -, -, -, a6, -⟩ :=
    Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega) (by omega) f hq hfx
  rw [a6]
  exact link_membersNumbered h (by omega) a hr

/-- **At the output head's front** (339): the closed group is segment 23's. -/
theorem head_membersNumbered_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : First.K2.P2} (hq : p.stands = .head)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx) :
    fx.f.rows.layout.members.toList =
      (VerifiableInference.Desc.First.Close.membersOf (loAt 23)).map
        (noK10 (P5J.At.seats Zp) (loAt 23) (P5J.At.pseats Zp) 23) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨tm, rm, cm, hm, fm⟩ := cuts 338 (by omega)
  obtain ⟨-, -, a3, -⟩ := Meaning.K2.front_nums_head h.scope h.reads O fm f₀ hq hfx
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 334 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, -⟩ :=
    closing_behind_laid h.scope h.reads O (l := 23) (by omega) fm
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 23 = 334 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 23, if_neg (by omega)]
  rw [a3, hf]
  exact membersNumbered_of_closing h (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx

/-- **At the front behind the last segment** (353, behind its quiet step in front): the closed group
is segment 24's. -/
theorem fin_membersNumbered_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S} (he : First.K2.finishFrontQ a.1.2 = .ok t)
    {p : First.K2.P2} (hq : p.stands = .finish) {fx : _root_.Tw.K2.Front}
    (hfx : First.K2.frontAt p t = some fx) :
    fx.f.rows.layout.members.toList =
      (VerifiableInference.Desc.First.Close.membersOf (loAt 24)).map
        (noK10 (P5J.At.seats Zp) (loAt 24) (P5J.At.pseats Zp) 24) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨-, -, a3, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f₀ he hq hfx
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 350 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, -⟩ :=
    closing_behind_cleared h.scope h.reads O f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 24 = 350 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 24, if_pos rfl]
  rw [a3, hf]
  exact membersNumbered_of_closing h (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.membersNumbered_of_closing
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_membersNumbered
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_membersNumbered_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_membersNumbered_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_membersNumbered_front
