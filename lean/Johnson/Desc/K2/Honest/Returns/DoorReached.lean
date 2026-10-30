-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/DoorReached.lean: UNDER THE HEAD's PREMISE, AT A STATE REACHED IN
FRONT OF A CODE SWITCH, AT ALL THREE SORTS OF THE KIND's PLACES: THE PLACE's OWN NUMBERS
(`ProofFile.pAtK2`) HAVE THE PLACE's SORT, AND THE WAY IN OF THE ITEM "carry" (`doorZ`,
Johnson/Top/H0/K2Caller/CarryClosed.lean) HANDS THE STATE OFF WHICH THE SWITCH's BLOCK TAKES ITS
FRONT. Statements with their proofs; no definition. On the verifier's side alone.

  `link_door` `AtMgA` · m < 23 · a reached at 14 (m + 1) + 2 ⊢ `(ProofFile.pAtK2 Zp m).stands = .link` and
                    `doorZ Zp m a.1.2 = some a.1.2`
  `head_door` a reached at 339 ⊢ `(ProofFile.pAtK2 Zp 23).stands = .head` and `doorZ Zp 23 a.1.2 = some
                    a.1.2`
  `fin_door` a reached at 353 · the quiet step in front returns t there (`finishFrontQ a.1.2 = .ok
                    t`) ⊢ `(ProofFile.pAtK2 Zp 24).stands = .finish` and `doorZ Zp 24 a.1.2 = some t`

Why. The laws of this folder on a switch's front (Returns/FrontTiesReached.lean,
Returns/MembersNumbered.lean, Returns/WordAtFront.lean and others) speak at `First.K2.frontAt p s =
some fx`, at any numbers p of the place's sort. The item reads `doorZ Zp m s = some t` and `frontAt
(ProofFile.pAtK2 Zp m) t = some fx`. By these three laws the two are one: p := `ProofFile.pAtK2 Zp m`, and t is
the state (behind the last segment: what the quiet step returns).

THE TABLE's PROMISE IS NOT SPENT. `hdoor_const` (Johnson/P1K2R/CarryAtConst.lean) has the way in
under the promise on the state (`onQ`), with the place's sort as a premise. Here where the state
stands comes off the walk.

By, the library's: the sort: `AtMgA.stands_link_atAll`, `AtMgA.stands_finish_atAll`
(Johnson/Desc/First/Link/Law/DressAtAll.lean), `hs_atAll` (Johnson/Loose/H2K12/HsAtAll.lean) · where
the state stands: `atSwitch_reached`, field `here` (Johnson/AtFull/Shape/AtSwitchReached.lean) ·
`fin_walk` (Johnson/AtFull/Shape/FinFrontReached.lean) · at 339: `k7_sits`, `k7_sits_yes`
(Johnson/IMR/FirstSeats.lean), `hear_at_flat` (Johnson/IMR/FlatIx.lean), `flatIx_scope`
(Johnson/IMR/FlatScope.lean), `fold_next`, `andThen_yes` (Johnson/IMR/FoldTools.lean),
`reply_record` (Johnson/Desc/Kinds/Law/ReplyPins.lean): the head's part of the state is there and
not opened: the road of `h1_shut` (Johnson/IMR/GroupHead.lean) · `out_of_between`
(Johnson/Top/H0/K2Caller/DoorOfPromise.lean) · `doorZ_at_switch`
(Johnson/Top/H0/K2Caller/CarryClosed.lean): where no link is open the way in is `ProofFile.doorAtK2`
(Johnson/Desc/ProofFile/CarryAt.lean). And `link_member_stated` (Returns/SeatReached.lean): no mark.

NEAR, NOT CALLED. `doorZ_of_promise` (Johnson/Top/H0/K2Caller/DoorOfPromise.lean): the way in under
the promise · `out_of_headFront` (the same file): where a state stands in the head's front no link
is open and the head's part is there · `doorZ_head`, `doorZ_finish`
(Johnson/Top/H0/Walk/FrameCarryEnds.lean): the way in's text at these two sorts · `stands_open`,
`stands23` (Johnson/Top/H0/K2Caller/StandsLow.lean): the sort, under premises on the public part.
THESE THREE TAKE "the way in hands t" AS A PREMISE: `book_at_reached`
(Johnson/P2LawR/SwitchNoticesAtHead.lean), `hDoor_at` (Johnson/P2LawR/CarriedDoorAtK10.lean),
`behind_of_close` (Johnson/Desc/First/Link/Law/BehindOfClose.lean).

Limits. No run is given at which the head's premise and "reached" hold together: the three laws
could hold of nothing. That a front is there (`frontAt … = some fx`), and behind the last segment
that the quiet step returns, is not shown here. The full size and the format's second hash function alone.
Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.SeatReached
import Johnson.AtFull.Shape.AtSwitchReached
import Johnson.Top.H0.K2Caller.CarryClosed
import Johnson.Top.H0.K2Caller.DoorOfPromise
import Johnson.Desc.First.Link.Law.DressAtAll
import Johnson.AtFull.Shape.FinFrontReached
import Johnson.IMR.GroupHead
import Johnson.Loose.H2K12.HsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (doorZ doorZ_at_switch out_of_between)
open VerifiableInference.Desc.Sound (allOf EAll)
open Johnson.Desc.First.Walk.Tied (reach_raw reach_cuts_below)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT A SEGMENT's FIRST PLACE** (14 (m + 1) + 2, m < 23): the place's own numbers stand as a
link's, and the item's way in hands the reached state itself. -/
theorem link_door (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) :
    (ProofFile.pAtK2 Zp m).stands = .link ∧ doorZ Zp m a.1.2 = some a.1.2 := by
  have hs := h.stands_link_atAll m h23
  have A := Johnson.AtFull.Shape.atSwitch_reached h (l := m + 1) (by omega)
    (reach_raw (h.toAtMg.rch_is_reach _ a hr)) (link_member_stated h h23 a hr).1
  have hb : VerifiableInference.Desc.First.standOf a.1.2 = .between := by
    unfold VerifiableInference.Desc.First.standOf
    rw [A.here]
  refine ⟨hs, ?_⟩
  rw [doorZ_at_switch Zp m a.1.2 (out_of_between a.1.2 hb).1 (fun c => by rw [hs] at c; cases c)]
  unfold ProofFile.doorAtK2
  rw [hs]
  rfl

/-- **AT THE OUTPUT HEAD's PLACE** (339): the place's own numbers stand as the head's, and the
item's way in hands the reached state itself. -/
theorem head_door (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) :
    (ProofFile.pAtK2 Zp 23).stands = .head ∧ doorZ Zp 23 a.1.2 = some a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := H2K12.hs_atAll h
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨tm, rm, cm, hm, fm⟩ := cuts 338 (by omega)
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits h.scope h.reads O
  have i0 : cF.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope h.scope h.reads O (by decide : 24 ≤ 24) 0).trans
      (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := Meaning.K2.fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes h.scope h.reads O hj d0).1
  obtain ⟨mm, -, a2⟩ := Meaning.K2.andThen_yes d0'
  obtain ⟨o, _, ho, hc, -, -, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.reply_record 24 _ a2
  have hh : a.1.2.here = .head o := by
    rw [e]
    exact ho
  have hin : a.1.2.inLink = false := by
    unfold S.inLink S.fork?
    rw [hh]
    simp [hc]
  refine ⟨hs, ?_⟩
  rw [doorZ_at_switch Zp 23 a.1.2 hin (fun _ => ⟨o, hh⟩)]
  unfold ProofFile.doorAtK2
  rw [hs]
  rfl

/-- **BEHIND THE LAST SEGMENT** (353): the place's own numbers stand as the finish's, and the item's
way in hands what the quiet step in front returns at the reached state. -/
theorem fin_door (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S} (he : First.K2.finishFrontQ a.1.2 = .ok t) :
    (ProofFile.pAtK2 Zp 24).stands = .finish ∧ doorZ Zp 24 a.1.2 = some t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := h.stands_finish_atAll
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  have hB := (Johnson.AtFull.Shape.fin_walk h.scope h.reads O f).1
  have hb : VerifiableInference.Desc.First.standOf a.1.2 = .between := by
    unfold S.atBetween at hB
    unfold VerifiableInference.Desc.First.standOf
    cases hh : a.1.2.here <;> rw [hh] at hB <;> first | rfl | cases hB
  refine ⟨hs, ?_⟩
  rw [doorZ_at_switch Zp 24 a.1.2 (out_of_between a.1.2 hb).1 (fun c => by rw [hs] at c; cases c)]
  unfold ProofFile.doorAtK2
  rw [hs]
  show (First.K2.finishFrontQ a.1.2).toOption = some t
  rw [he]
  rfl

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_door
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_door
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_door
