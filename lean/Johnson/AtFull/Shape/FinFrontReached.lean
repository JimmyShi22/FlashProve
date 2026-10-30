-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FinFrontReached.lean: the step finishFrontQ returns at the states that 353
accepting steps reach, the steps being those of the first 353 blocks of the proof file's first
chain, each wrapped by below (a narrower family than the blocks' own steps reach: see the limits).

Words. The chain c is the first chain of the description that ProofFile.onlineDescription makes of three public
files; the premise O : IM.Open ... (Johnson/IMR/SeatOpen.lean) names the description's parts, each
by the call that made it. c.blocksInOrder is the chain's list of blocks, numbered from 0: "the first 353
blocks" are the blocks 0 to 352. The chain has 25 sections, which the library calls links. A state s
has a field s.check, its record of the calls made so far; s.check.frame.link is a counter in it.
s.atBetween = true says s.here = .between: by its own docstring (S.atBetween,
Johnson/Desc/First/State.lean), in front of the first link or between two links. s.failed = none:
the state bears no mark of failure.
finishFrontQ (Johnson/Top/H0/Tw/K2C/Finish.lean) is a step on such states; the opening comment of
Johnson/Top/H0/Tw/K2C/FinFront.lean and the docstring of FinishFrontAsks
(Johnson/Top/H0/Tw/K2C/Asks.lean) call it "F.0.front".

What is shown.
  clear_between: wherever framesOf (Johnson/Top/H0/Walk/FrameLot.lean) returns a list of frames: if
    the step "clear" of one of them returns t, then t.atBetween = true.
  fin_walk: where the fold over the first 353 blocks returns a state t₂: t₂.atBetween = true,
    t₂.check.inLink = false and t₂.check.frame.next = .first.
  newGroup_returns: Tw.K2.newGroupG T code maskCode (Johnson/Top/H0/Tw/K2/First.lean) returns where
    T's list of base codes has an entry at code, its list of mask codes has an entry at maskCode,
    and the second entry's logN is at most the first's.
  fin_front_fold: where that fold returns t₂ and t₂.failed = none, finishFrontQ t₂ returns.
  fin_front_reached: finishFrontQ s returns at every s with
    Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s) (Reach, Johnson/Top/H0/Walk/Reach.lean):
    353 accepting steps from a first state, at whatever rounds and columns. THE STEPS ARE THOSE OF
    THE BLOCKS AS WRAPPED BY below, NOT OF THE CHAIN's OWN BLOCKS: see the limits.
  fin_looks_reached: at the same states, finishFrontQ s returns a state t for which there are a and
    Q with t.here = .fin a and a.G = some Q. Which group Q is, is not said.

How. finishFrontQ returns just where the two records FinishFrontAsks and FinishAsks can be filled
(finishFrontQ_iff, finishFront_iff, Johnson/Top/H0/Tw/K2C/Asks.lean). Their fields, and where each
comes from:
  between: block 352, "cleared", leaves atBetween = true (the last clause of clear_carries,
    Johnson/Top/H0/Walk/FrameLaw.lean).
  due (finishDue, Johnson/Desc/First/Walk/Quiet.lean: check.inLink is false, and the frame's link is
    the number of the shape's links) and last: block 351 sets inLink := false (K9.closed,
    Johnson/Desc/First/Batch/Text.lean), and "cleared" makes that record the state's check
    (framesOf_clear, Johnson/IMR/GroupTail.lean); the frame's link is 25 (fin_link,
    Johnson/IMR/FinPin.lean); the frame's shape is Z.first.shape (open_recAll,
    Johnson/IMR/ListsEnds.lean), which has 25 links by the premise h25.
  first: block 350 sets next := .first (closeFrame_lays, Johnson/Desc/First/Close/Law/Lays.lean).
  group: the frame's groups are those of the shape, one more than its links (reqGroups_size,
    Johnson/IMR/MsgsPlaces.lean).
  opened: newGroup_returns, with codes_of_reqOk (Johnson/Desc/K2/Honest/Returns/LinkReached.lean)
    and mask_le_main (Johnson/Goal/Meaning/MaskShort.lean).
  enters, entered: S.enterFin?'s own text (Johnson/Desc/First/State.lean), at a state with
    atBetween = true and failed = none; that failed = none at a reached state: noMark_late
    (Johnson/IMR/NoMarkReach.lean).
fin_looks_reached takes its two facts on t from finishFrontQ_fr
(Johnson/Top/H0/Tw/K2C/FinFront.lean).

Limits. WHICH STATES: below (Johnson/Desc/Sound/ChainRule.lean) is, by its own docstring, a device
of the proof that runs nowhere: the block that first tests that every word which it is handed is
below the field's prime, and then decides as the block does. What the wrapped blocks reach, the
chain's own blocks reach (reach_raw, Johnson/Top/H0/Walk/Reach.lean); the converse is not given. So
fin_front_reached and fin_looks_reached speak of the narrower family, and whoever holds Reach over
c.blocksInOrder itself cannot call them, though their proofs use the premise through reach_raw alone.
All but clear_between and newGroup_returns stand under: VerifierAndGoals.InScope P = true; VerifierAndGoals.readFiles P
returns; O, stated at the hash OnBytes.secondHashFunction alone, at any layout file lay. h25
(Z.first.shape.link.length = 25) is a premise of the last three. h25_of_hy
(Johnson/Desc/K2/Honest/Returns/FinAtReached.lean) gives it from VerifierAndGoals.InScope P = true and a yes
of the test madePinnedAt (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean), BUT FOR AN O AT
lay := P.lay ALONE; it is not called here. That any state is
reached at 353 is not said. THE STEP ALONE: finishPlace (Johnson/Top/H0/Tw/K2C/Finish.lean) builds
one block of three parts: a quiet block with finishFrontQ, the code switch's own block, a quiet
block with finishBehindQ. This file says that the first part's step returns and what two things its
value holds; of the two other parts, and of any later block, it says nothing. That block 353 of
c.blocksInOrder is such a finishPlace is not shown here. Nothing on soundness, completeness or hiding.
-/
import Johnson.IMR.FinPin
import Johnson.IMR.ListsEnds
import Johnson.IMR.NoMarkReach
import Johnson.IMR.MsgsPlaces
import Johnson.Goal.Meaning.MaskShort
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Desc.K2.Honest.Returns.LinkReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (finishFrontQ finishFrontQ_iff)
open VerifiableInference.Desc.K2.Honest.Returns (codes_of_reqOk)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (frontOf front_len fold_cut fold_next group_head closing_yes bindE there_some
  link_putLink live_open framesOf_clear fin_link open_recAll mask_le_main mem_of_mapM_ok)
open ProofFile (Cl)

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- Wherever framesOf returns a list of frames: if the step "clear" of one of them returns t, then
t.atBetween = true. -/
theorem clear_between {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, ∀ s t,
    f.clear s = .ok t → t.atBetween = true := by
  have clr : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
      (row : RowFn) (s t : S), clearWith X counts left row s = .ok t → t.atBetween = true :=
    fun X counts left row s t k => (Law.clear_carries k).2.2.2.2.2.2.2.2.2
  have th : ∀ (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (s t : S),
      VerifiableInference.Desc.First.Close.tailHead X lay lin s = .ok t → t.atBetween = true :=
    fun _ _ _ => clr _ _ _ _
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact th _ _ _
  · split at e
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
      · cases e
        exact clr _ _ _ _

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- Where the fold over the chain's first 353 blocks returns the state t₂: t₂.atBetween = true,
t₂.check.inLink = false and t₂.check.frame.next = .first. -/
theorem fin_walk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.atBetween = true ∧ t₂.check.inLink = false ∧ t₂.check.frame.next = .first := by
  obtain ⟨s, R₃, C₃, g3⟩ := fold_cut (k := 350) 3 f₂
  obtain ⟨L, hL, -, -⟩ := group_head hS hR O 10 (by omega) s R₃ C₃ g3
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  obtain ⟨s4, r4, q4, g4⟩ := fold_cut (k := 351) 2 f₂
  obtain ⟨s5, r5, q5, g5⟩ := fold_cut (k := 352) 1 f₂
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O 24 (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  -- the closing
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : 24 < 25) eL e1
  rw [hlen, show 14 * 24 + 9 + 4 + 1 = 350 by omega] at ib
  obtain ⟨rs, gs, d⟩ := fold_next ib g3 g4
  have dx : x.retype.decide s rs gs = .ok s4 :=
    ((IM.yes_alone la (by intro k; cases k) s s4 rs gs).1 d).1
  obtain rfl : VerifiableInference.Desc.K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy, hl4, -⟩ := closing_yes (C := Unit) dx hL
  -- the shutting
  obtain ⟨b5', x5, e15, e25, la5⟩ := hall 2 .K9 rfl
  have ib5 := IM.close_numbers hS hR O (by omega : 24 < 25) eL e15
  rw [hlen, show 14 * 24 + 9 + 4 + 2 = 351 by omega] at ib5
  obtain ⟨rs5, gs5, d5⟩ := fold_next ib5 g4 g5
  have dx5 : x5.retype.decide s4 rs5 gs5 = .ok s5 :=
    ((IM.yes_alone la5 (by intro k; cases k) s4 s5 rs5 gs5).1 d5).1
  obtain rfl : VerifiableInference.Desc.K9.shut pw (Q.piece + 1) = x5 := Option.some.inj e25
  obtain ⟨L₁, h1, h5⟩ := bindE dx5
  have e5 : s5 = s4.putLink (VerifiableInference.Desc.K9.closed L₁ L₁.check.frame) :=
    (Except.ok.inj h5).symm
  have hL₁ : s4.link? = some L₁ := there_some h1
  have hL5 : s5.link? = some (VerifiableInference.Desc.K9.closed L₁ L₁.check.frame) := by
    rw [e5]
    exact link_putLink hL₁ _
  have eL₁ : L₁.check.frame = y.1 := by
    have := Option.some.inj (hL₁.symm.trans hl4)
    rw [this]
  -- "cleared"
  have iC' : c.blocksInOrder[352]? = some bC := by
    rw [show 352 = 14 * 24 + 9 + 7 by omega]
    exact iC
  obtain ⟨rs6, gs6, d6⟩ := fold_next iC' g5 f₂
  rw [dC] at d6
  have hc6 := ((hClear s5 t₂).1 d6).1
  have k6 := framesOf_clear hfs f (List.mem_of_getElem? hf) s5 t₂ hc6
  have ec : t₂.check = (VerifiableInference.Desc.K9.closed L₁ L₁.check.frame).check := by
    rw [k6.1, live_open hL5]
  obtain ⟨Gc, rows, -, -, ey⟩ :=
    VerifiableInference.Desc.First.Close.closeFrame_lays (f' := y.1) (S' := y.2) hy
  refine ⟨clear_between hfs f (List.mem_of_getElem? hf) s5 t₂ hc6, by rw [ec]; rfl, ?_⟩
  rw [ec]
  show L₁.check.frame.next = .first
  rw [eL₁, ey]

/-- Tw.K2.newGroupG T code maskCode returns where T's base codes have an entry c₀ at code, its mask
codes have an entry z₀ at maskCode, and z₀.logN ≤ c₀.logN. -/
theorem newGroup_returns (T : Statement) {code maskCode : Nat} {c₀ z₀ : Code}
    (hc : T.codes.base[code]? = some c₀) (hz : T.codes.mask[maskCode]? = some z₀)
    (hle : z₀.logN ≤ c₀.logN) :
    ∃ v, _root_.Tw.K2.newGroupG T code maskCode = .ok v := by
  have hok : VerifiableInference.Desc.Ground.ok
      (VerifiableInference.Desc.Ground.newGroupL T code maskCode) = true := by
    simp [VerifiableInference.Desc.Ground.ok, VerifiableInference.Desc.Ground.newGroupL,
      VerifiableInference.Desc.Ground.groupL, VerifiableInference.Desc.Ground.has, hc, hz, hle]
  unfold _root_.Tw.K2.newGroupG VerifiableInference.Desc.Ground.newGroupP
  have hok' : VerifiableInference.Desc.Ground.ok
      (VerifiableInference.Desc.Ground.newGroupL (_root_.Tw.K2.dOf T).st code maskCode) = true :=
    hok
  rw [if_pos hok']
  exact ⟨_, rfl⟩

/-- **finishFrontQ returns** at the state t₂ that the fold over the chain's first 353 blocks
returns, if t₂.failed = none and the shape has 25 links. -/
theorem fin_front_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (h25 : Z.first.shape.link.length = 25) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hu : t₂.failed = none) : ∃ t, finishFrontQ t₂ = .ok t := by
  obtain ⟨a1, a2, a4⟩ := fin_walk hS hR O f₂
  have a3 := fin_link hS hR O f₂
  have RA := open_recAll hS hR O (by omega : 2 ≤ 353)
    (by rw [front_len hS hR O]) f₂
  have RA' : Meaning.K2.RecAll Z.first.codes Z.first.shape t₂ := RA
  have hsh := RA'.walk.shape
  have hlast : t₂.check.frame.link = t₂.check.frame.shape.link.length := by
    rw [a3, hsh, h25]
  have hgs : t₂.check.frame.link < t₂.check.frame.groups.size := by
    rw [RA'.walk.groups, Meaning.Carry.reqGroups_size, a3, h25]
    omega
  have hQ : t₂.check.frame.groups[t₂.check.frame.link]? =
      some t₂.check.frame.groups[t₂.check.frame.link] := Array.getElem?_eq_getElem hgs
  have hok : reqOk t₂.st.codes t₂.check.frame.shape = true := by
    rw [RA'.codes, hsh]
    exact RA'.ok
  obtain ⟨c₀, z₀, hc, hz⟩ := codes_of_reqOk hok
  obtain ⟨⟨T', g⟩, hv⟩ := newGroup_returns t₂.st hc hz (mask_le_main hok hc hz)
  have hdue : Johnson.Desc.First.Walk.finishDue t₂.check = true := by
    unfold Johnson.Desc.First.Walk.finishDue
    rw [a2, hlast]
    simp
  have hen : t₂.enterFin? = .ok t₂.enterFin := by
    unfold VerifiableInference.Desc.First.S.enterFin?
    refine (VerifiableInference.Desc.First.S.unmarked_ok _ _).2 ⟨rfl, ?_⟩
    unfold VerifiableInference.Desc.First.S.enterFin
    rw [if_pos a1]
    exact hu
  obtain ⟨a, hhere⟩ : ∃ a, t₂.enterFin.here = .fin a := by
    unfold VerifiableInference.Desc.First.S.enterFin
    rw [if_pos a1]
    exact ⟨_, rfl⟩
  exact ⟨_, (finishFrontQ_iff t₂ _).2 ⟨_, _, _, _,
    { between := a1, due := hdue, group := hQ
      front := (_root_.Tw.K2.finishFront_iff _ _ _).2 ⟨_, T', g,
        { first := a4, last := hlast, group := hQ, opened := hv, out := rfl }⟩
      enters := hen, entered := hhere, out := rfl }⟩⟩

/-- **finishFrontQ returns at every state that 353 accepting steps reach**, the steps being those of
the chain's blocks as wrapped by below; if the shape has 25 links. -/
theorem fin_front_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (h25 : Z.first.shape.link.length = 25) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) :
    ∃ t, finishFrontQ s = .ok t := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact fin_front_fold hS hR O h25 f (IM.noMark_late hS hR O (reach_raw hr) (by omega))

/-- At the same states s, if the shape has 25 links: finishFrontQ s returns a state t, and there are
a and Q with t.here = .fin a and a.G = some Q. -/
theorem fin_looks_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (h25 : Z.first.shape.link.length = 25) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) :
    ∃ t a Q, finishFrontQ s = .ok t ∧ t.here = .fin a ∧ a.G = some Q := by
  obtain ⟨t, ht⟩ := fin_front_reached hS hR O h25 hr
  obtain ⟨a, Q, h1, h2, -⟩ := VerifiableInference.Desc.First.K2.finishFrontQ_fr ht
  exact ⟨t, a, Q, ht, h1, h2⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.clear_between
#print axioms Johnson.AtFull.Shape.fin_walk
#print axioms Johnson.AtFull.Shape.newGroup_returns
#print axioms Johnson.AtFull.Shape.fin_front_fold
#print axioms Johnson.AtFull.Shape.fin_front_reached
#print axioms Johnson.AtFull.Shape.fin_looks_reached
