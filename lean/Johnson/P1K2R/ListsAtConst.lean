-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/ListsAtConst.lean: code switching (K2): THE THREE LISTS OF WHAT IS LEFT
(T14Left · T23More · T3More: Johnson/P1K2R/TiesOneFour.lean | TiesTwoThree.lean |
TieThreeConst.lean) AT THE CLOSED CONSTANT, AT EVERY PLACE OF THE KIND, FROM THE HEAD
(P5J.AtMgA at the second hash function) AND ONE STRUCTURE OF NAMED TESTS (K2Tests).
  k02_sits7_pAt_at  ONE DOOR, SEVEN PROPERTIES: Sits · LeftDoor · EndsUnmarked · BookDoor · WayAt,
               with two more: KeepsOut leave · WayOut (mOf i) leave
  pAt_nums     at every place of the kind: the sentence's numbers ProofFile.pAtK2 Zp (mOf k) are the
               kind's at the plan's numbers n of the place's link (seated_is_pAt)
  P2At.roots · k2LogN_full · rootsLay_full  the place's count of roots is the typed structure's ·
               CLOSED FACTS BY LEAN's KERNEL at the 25 written rows: logN ≤ 32 · the written
               notices' lay has as many trees as the row's first round has roots; with negative
               tests
  hp_const     THE FIELD hp OF K2Short (P2At r (ProofFile.pAtK2 Zp (mOf k))) AT EVERY PLACE OF THE KIND:
               hp_written (Johnson/P1K2R/P2AtConst.lean) at the lot's own sub-protocol;
               its premise on the table is paid at each call by tableWrittenB_head
  t14_laidL    T14Left's laidL at L := K2Ties.laidFull: from the pin
  K2Tests      THE NAMED TESTS, each by name (below)
  t14Left_const · t3More_const · t23More_const  the three lists at the constant's terms
  shown_const  T23More's shownAll at every piece of the row Hd.toAtMg.row L₀
  lists_at_const  ALL THREE, AT EVERY PLACE OF THE KIND, with the door and the written rounds
K2Tests, BY NAME (FIVE). pinned: madePinnedAt accepts · cut: the chain's sub-protocols have the
written cut · sendsB: sendsAreB accepts at 358, at the opening's ground · spots: spotsFitB Zp
accepts · links25: the first state's shape has 25 segments.
NO FIELD tableW (tableWrittenB accepts) AND NO FIELD live (FlashProve.protocolDataWellFormed
accepts) IS AMONG THEM: tableWrittenB_head and membersPlan_ofHead
(Johnson/Top/H0/K2Ties/AtHead3.lean) have both under the head.
NOTHING ELSE IS LEFT BESIDE THE HEAD. Four of the five are tests on public data outright; sendsB is
such a test behind «∀ Bs bs A' B', IM.Open … →»: it would be idle where nothing opens; the head's
own «opened» shuts that out.
PAID HERE, OF THE THREE LISTS: T14Left: scope · reads · laid · opened · seatsFit (the head) ·
laidL · keptSeats (KeptSeatsLeft.lean) · members (membersPlan_ofHead) · trees83 (t1_t2_at) ·
dN · dcs · darr · dms · named (by the constant's own text) · frameAll ·
frameKey (wholeAt_of_laid) · row · frameW · way · firstTree (ft_at_switch) ·
place · reach. T23More: frameFt · blockAt · sits · keepsOut · w2 (k2Wr_of) ·
baseIs · treesLen (piece_base_trees_at) · shownAll (shown_const: shownAll_at_row,
Johnson/P1K2R/ShownAtRow.lean, at seats_at_row). T3More: wayOut · logN · posIs.
LIMITS. Joins, and two closed facts by the kernel. NO TEST OF K2Tests IS SHOWN TO ACCEPT AT A REAL
VALUE: no example. A MEMBER OF THE HEAD IS PROVED AT THE SECOND HASH FUNCTION OnBytes.secondHashFunction, AT THE
TWO WRITTEN SETS OF PUBLIC FILES VerifierAndGoals.storedPublicFiles AND VerifierAndGoals.zGap, IN THE SIDE LIBRARY (AtFullSide/Top/:
headMember_zFull, headMember_zGap); AT OTHER FILES OR ANOTHER HASH NONE IS SHOWN. The full size
alone. No probability; no soundness is claimed.
-/
import Johnson.P1K2R.LastJoin
import Johnson.P1K2R.TieThreeConst
import Johnson.P1K2R.KeptSeatsLeft
import Johnson.P1K2R.PieceBaseTrees
import Johnson.P1L20R.FtAtSwitch
import Johnson.Top.H0.Tw.K2C.TieThreeDoors
import Johnson.P1K2R.P2AtConst
import Johnson.Top.H0.K2Ties.AtHead3
import Johnson.HB.LLHARD.HeadFacts
import Johnson.P1K2R.ShownAtRow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes.Maker
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (codeSwitchKind)
open VerifiableInference.Desc.First.K2Caller (spotsFitB k2NoAt WayAt WayOut KeepsOut hlv_opened
  hlv_head_guards hlv_finish seated_is_pAt linkOfM SwRow tableFullLit P2At tableWrittenB)
open H2K.JointK (Sits)
open IM (k2P)
open ProofFile (Cl)

/-- **ONE DOOR, SEVEN PROPERTIES.** -/
theorem k02_sits7_pAt_at {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hsp : spotsFitB Zp = true) (h25 : Zp.s₀.check.frame.shape.link.length = 25) (i : ℕ)
    (a : VerifiableInference.Desc.Place) (ha : P5J.At.ps[i]? = some a)
    (hk : a.kind = KindName.K2) :
    ∃ (B : Block S Cl) (enter : S → Except String S) (leave : S → S → Except String S),
      cF.blocksInOrder[i]? = some B ∧ Sits B (codeSwitchKind (ProofFile.pAtK2 Zp (mOf i)) : Block S Unit) enter leave ∧
      LeftDoor enter leave ∧ EndsUnmarked leave ∧ BookDoor enter leave ∧
      WayAt (mOf i) enter (ProofFile.pAtK2 Zp (mOf i)) ∧ KeepsOut leave ∧ WayOut (mOf i) leave := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Z', Bs', base', c', A', B', O', H⟩ := k02_sits_pAt h.scope h.reads h.laid.value
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := O.unique O'
  obtain ⟨h1, h2, h3⟩ := H hsp h25
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · obtain ⟨b, hb, hX⟩ := h1 l a1 a24
    obtain ⟨hst, fs, f, hfs, hf, hS⟩ := hX (flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb))
    rw [mOf_link l a1 a24]
    exact ⟨b, _, _, hb, hS, leftDoor_opened hfs hf (by omega), ends_opened f, bookDoor_opened hfs
      hf, Or.inl ⟨by omega, hst, fun _ _ e => (Except.ok.inj e).symm⟩, out_opened hfs hf,
      Or.inl ⟨by omega, hlv_opened hfs hf⟩⟩
  · obtain ⟨b, hb, hX⟩ := h2
    obtain ⟨hst, HP, -, hS⟩ := hX (flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb))
    exact ⟨b, _, _, hb, hS, leftDoor_head HP, ends_head HP, bookDoor_head HP, Or.inr (Or.inl ⟨rfl,
      hst, fun _ _ e => (Except.ok.inj e).symm⟩), out_head HP,
      Or.inr (Or.inl ⟨rfl, hlv_head_guards HP⟩)⟩
  · obtain ⟨b, hb, hX⟩ := h3
    obtain ⟨hst, hS⟩ := hX (back_planOk O h.laid.planOk (List.mem_of_getElem? hb))
    exact ⟨_, _, _, (IM.back_numbers h.scope h.reads O).1 0 b hb, hS.same _ rfl rfl fun e =>
      (Bool.and_eq_true _ _ ▸ e : _ ∧ _).1, leftDoor_finish, ends_finish, bookDoor_finish, Or.inr
      (Or.inr ⟨rfl, hst, fun _ _ e => e⟩), out_finish, Or.inr (Or.inr ⟨rfl, hlv_finish⟩)⟩


/-- **The sentence's numbers at a place of the kind are the kind's at the plan's numbers.** -/
theorem pAt_nums {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A
      B)
    (hsp : spotsFitB Zp = true) (h25 : Zp.s₀.check.frame.shape.link.length = 25) (i : ℕ)
    (a : VerifiableInference.Desc.Place) (ha : P5J.At.ps[i]? = some a)
    (hk : a.kind = KindName.K2) :
    ∃ Q n a' nm st, prepOf Zp Bs.G₀ = some Q ∧ numsAt Q (linkOfM (mOf i)) = some n ∧
      ProofFile.pAtK2 Zp (mOf i) = k2P Zp a' nm st n := by
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_link_sits h.scope h.reads O l a1 a24
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 0] at hf
    have hb := flat_planOk O h.laid.planOk b (List.mem_of_getElem? hf)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hb)).1
    have hpl := place_of_is hi hxp
    obtain ⟨Q, n, hQ, hn, e, -⟩ := seated_is_pAt O.blank hsp hx hxp
    rw [hpl] at hn e
    have hg : n.grp = l := numsAt_grp hn
    rw [hg] at e
    rw [mOf_link l a1 a24]
    refine ⟨Q, n, _, _, _, hQ, ?_, e⟩
    unfold linkOfM
    rw [if_pos (by omega), show l - 1 + 1 = l by omega]
    exact hn
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of h.scope h.reads O
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 1] at hf
    have hb := flat_planOk O h.laid.planOk b (List.mem_of_getElem? hf)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
    have hpl := place_of_is hi hxp
    obtain ⟨Q, n, hQ, hn, e, -⟩ := seated_is_pAt O.blank hsp hx hxp
    rw [hpl] at hn e
    have hg : n.grp = 24 := numsAt_grp hn
    rw [hg] at e
    exact ⟨Q, n, _, _, _, hQ, hn, e⟩
  · obtain ⟨b, x, e1, hx, ep, hl, -⟩ := IM.k2_finish_of O
    have hi := IM.k2_mem hx
    rw [ep] at hi
    have hb := back_planOk O h.laid.planOk (List.mem_of_getElem? e1)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
    have hpl := place_of_is hi hxp
    obtain ⟨Q, n, hQ, hn, e, -⟩ := seated_is_pAt O.blank hsp hx hxp
    rw [hpl] at hn e
    have hg : n.grp = 25 := by
      rw [numsAt_grp hn]
      show Q.z.request.link.length = 25
      rw [(prepOf_request hQ).1, h25]
    rw [hg] at e
    exact ⟨Q, n, _, _, _, hQ, hn, e⟩

/-- **THE FIELD hp AT EVERY PLACE OF THE KIND**: hp_written at the lot's own sub-protocol
of the place. -/
theorem hp_const {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A
      B)
    (hT : tableWrittenB Z.pol Z.lay Z.KL = true) (hsp : spotsFitB Zp = true)
    (h25 : Zp.s₀.check.frame.shape.link.length = 25) (i : ℕ)
    (a : VerifiableInference.Desc.Place) (ha : P5J.At.ps[i]? = some a)
    (hk : a.kind = KindName.K2) {r : SwRow} (hr : tableFullLit[mOf i]? = some r) :
    P2At r (ProofFile.pAtK2 Zp (mOf i)) := by
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_link_sits h.scope h.reads O l a1 a24
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 0] at hf
    have hb := flat_planOk O h.laid.planOk b (List.mem_of_getElem? hf)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hb)).1
    have hpl := place_of_is hi hxp
    rw [mOf_link l a1 a24] at hr ⊢
    refine hp_written hT h.laid.pub O.blank hsp hx hxp hr fun P _ => ?_
    rw [hpl]
    show l = l - 1 + 1
    omega
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of h.scope h.reads O
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 1] at hf
    have hb := flat_planOk O h.laid.planOk b (List.mem_of_getElem? hf)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
    have hpl := place_of_is hi hxp
    refine hp_written hT h.laid.pub O.blank hsp hx hxp hr fun P _ => ?_
    rw [hpl]
    rfl
  · obtain ⟨b, x, e1, hx, ep, hl, -⟩ := IM.k2_finish_of O
    have hi := IM.k2_mem hx
    rw [ep] at hi
    have hb := back_planOk O h.laid.planOk (List.mem_of_getElem? e1)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
    have hpl := place_of_is hi hxp
    refine hp_written hT h.laid.pub O.blank hsp hx hxp hr fun P hP => ?_
    rw [hpl]
    show P.z.request.link.length = 25
    rw [(prepOf_request hP).1, h25]

end P1K2

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left saidBehindB pubP_behind
    hheld_paid hrowM_paid hshown_of_cs hpin_of_cs hpin3_of_cs hnc_of_cs)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB laidAtCodes)
open VerifiableInference.Desc.First.K2Ties (AtWritten at_written laidFull laidFull_is
  codes_of_sends)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open Johnson.G (fxAt front_tests_full)
open P1K2 (mOf k2No_mOf EndsUnmarked BookDoor k2_spots)

/-! ## Closed facts, and what P2At says of the roots -/

theorem P2At.roots {r : SwRow} {p : K2.P2} (h : P2At r p) :
    p.roots = ((r.specs.map fun y => (y.round r.set .request).entry : List Fmt.Entry).getD 0
        { name := "" }).roots :=
  congrArg (fun l : List Fmt.Entry => (l.getD 0 { name := "" }).roots) h

set_option maxRecDepth 1000000 in
/-- **By the kernel**: at the 25 written rows logN is at most 32. -/
theorem k2LogN_full : (tableFullLit.all fun r => decide (r.g.main.logN ≤ 32)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: not at most 8. -/
theorem k2LogN_can_fail : (tableFullLit.all fun r => decide (r.g.main.logN ≤ 8)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **By the kernel**: the written notices' lay has as many trees as the row's first round has
roots. -/
theorem rootsLay_full : (List.range 25).all (fun m => (tableFullLit[m]?).any fun r =>
    (layTrees K2Hands.csW (K2Hands.sentW (m + 1)).toArray).any fun lay => lay.shapes.size ==
      ((r.specs.map fun y => (y.round r.set .request).entry : List Fmt.Entry).getD 0
        { name := "" }).roots) =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree more. -/
theorem rootsLay_can_fail : ((tableFullLit[0]?).any fun r =>
    (layTrees K2Hands.csW (K2Hands.sentW 1).toArray).any fun lay => lay.shapes.size + 1 ==
      ((r.specs.map fun y => (y.round r.set .request).entry : List Fmt.Entry).getD 0
        { name := "" }).roots) =
    false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **T14Left's laidL, at the written laid list `laidFull`**: from the pin. -/
theorem t14_laidL (hS : VerifierAndGoals.InScope Z = true)
    (La : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL Dw r₀ Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    laidAtCodes Zp.first.codes Zp.made.proof.1 = some laidFull := by
  have hc : Zp.first.codes = _ := (at_written hS La hy).cs
  have hs : Zp.made.proof.1 = Johnson.G.proofSends0 := by
    rw [VerifiableInference.PlanWritten.Joined.sends_in_scope hS La.pub hy]
    rfl
  rw [hc, codes_of_sends, hs]
  exact laidFull_is

/-! ## The named tests -/

/-- **THE NAMED TESTS**, each by name. -/
structure K2Tests (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain P5J.TS ProofFile.Cl) : Prop where
  pinned : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true
  cut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull
  sendsB : ∀ Bs bs A' B', IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    Zp Bs bs cF A' B' → sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true
  spots : spotsFitB Zp = true
  links25 : Zp.s₀.check.frame.shape.link.length = 25

theorem mOf_lt {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) : mOf k < 25 := by
  rcases k2_spots k pl ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · rw [P1K2.mOf_link l a1 a24]
    omega
  · decide
  · decide

/-! ## The three lists at the constant's terms -/

/-- **T14Left AT THE CONSTANT.** -/
theorem t14Left_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x)
    (Ts : K2Tests Z Zp Np cF) {Bs : ProofFile.PureBase} {bs : List (Block Rec Cl)}
    {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs bs cF A'
      B')
    {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {enter : Rec → Except String Rec}
    (w : WayAt (mOf k) enter (ProofFile.pAtK2 Zp (mOf k))) {r : SwRow}
    (hr : tableFullLit[mOf k]? = some r) {W : SwitchFrame}
    (hW : K2.frameAt (fxAt r) = some W) :
    T14Left (F := frC Dw) (dC Hd) Hd.rchU Z (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) Dw
      r₀ Zp Np cF Bs bs A' B' (mOf k) r W laidFull (ProofFile.pAtK2 Zp) enter pl where
  scope := Hd.scope
  reads := Hd.reads
  laid := Hd.laid
  opened := O
  pinned := Ts.pinned
  cut := Ts.cut
  sendsB := Ts.sendsB Bs bs A' B' O
  laidL := t14_laidL Hd.scope Hd.laid Ts.pinned
  trees83 := (P5J.t1_t2_at Hd).1
  seatsFit := Hd.plan.fit
  members := K2Ties.membersPlan_ofHead Hd (mOf_lt ha hk) hr
  keptSeats := t14_keptSeats Hd.scope Hd.laid Ts.pinned Ts.cut
    (t14_hG_at OnBytes.secondHashFunction Zp Np cF) (t14_laidL Hd.scope Hd.laid Ts.pinned) hr
  dN := rfl
  dcs := rfl
  darr := rfl
  dms := rfl
  named := rfl
  frameAll := by
    unfold ProofFile.allAt
    rw [P1M2.wholeAt_of_laid Hd.laid]
    rfl
  frameKey := by
    unfold ProofFile.keyAt
    rw [P1M2.wholeAt_of_laid Hd.laid]
    rfl
  row := hr
  frameW := hW
  way := w
  firstTree := P1L20.ft_at_switch Hd.laid.pub (mOf k)
  place := by rw [k2No_mOf ha hk]; exact ha
  reach := fun _ _ u => u.1.1

/-- **T3More AT THE CONSTANT.** -/
theorem t3More_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x)
    (Ts : K2Tests Z Zp Np cF) {Bs : ProofFile.PureBase} {bs : List (Block Rec Cl)}
    {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs bs cF A'
      B')
    {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {leave : Rec → Rec → Except String Rec}
    (wo : WayOut (mOf k) leave) {r : SwRow} (hr : tableFullLit[mOf k]? = some r) :
    T3More Zp Bs (mOf k) r (ProofFile.pAtK2 Zp) leave where
  wayOut := wo
  logN := by
    rw [(P1K2.hp_const Hd.toAtMg O (K2Ties.tableWrittenB_head Hd) Ts.spots Ts.links25 k pl ha hk
      hr).logN]
    exact of_decide_eq_true (List.all_eq_true.1 k2LogN_full r (List.mem_of_getElem? hr))
  posIs := by
    obtain ⟨Q, n, a', nm, st, hQ, hn, e⟩ :=
      P1K2.pAt_nums Hd.toAtMg O Ts.spots Ts.links25 k pl ha hk
    intro Pp n' hP hn'
    obtain rfl : Q = Pp := Option.some.inj (hQ.symm.trans hP)
    obtain rfl : n = n' := Option.some.inj (hn.symm.trans hn')
    have hp := (P1K2.hp_const Hd.toAtMg O (K2Ties.tableWrittenB_head Hd) Ts.spots Ts.links25 k pl
      ha hk hr).positions
    rw [e] at hp
    exact hp

/-- **T23More AT THE CONSTANT**, with «shown» as a premise (shown_const pays it). -/
theorem t23More_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x)
    (L₀ : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L₀.c₁ :: L₀.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃)
    (Ts : K2Tests Z Zp Np cF) {k : ℕ} {pl : VerifiableInference.Desc.Place}
    (ha : P5J.At.ps[k]? = some pl) (hk : pl.kind = KindName.K2)
    {q : Piece (ckP .two) (frC Dw) (ProofFile.InstPub × First.S) Cl
      (Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)}
    (hq : (Hd.toAtMg.row L₀)[k]? = some q) {B : Block Rec Cl} (hB : cF.blocksInOrder[k]? = some B)
    {enter : Rec → Except String Rec} {leave : Rec → Rec → Except String Rec}
    (hS : Sits B (K2.codeSwitchKind (ProofFile.pAtK2 Zp (mOf k)) : Block Rec Unit) enter leave)
    (hK : KeepsOut leave) {r : SwRow} (hr : tableFullLit[mOf k]? = some r) {d₁ d₂ : RDT}
    {extq : (ProofFile.InstPub × First.S) × (frC Dw).E.Str → Tr (uLT (ckP .two) [d₁, d₂]) →
      Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok →
      Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok}
    (e : q = k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂ extq)
    (he : [d₁, d₂].map (·.entry) = (K2.rounds (ProofFile.pAtK2 Zp (mOf k))).map (·.entry))
    (hkk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind)
    (shown : (k2Q (P := ProofFile.InstPub) (Cl := Cl)
      (W := Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)
      ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂ extq).ShownAll (dC Hd).G r.cs r.l
      (seatNew (P5J.At.N Zp cF) (mOf k) r)) :
    T23More (F := frC Dw) (dC Hd) Zp cF (mOf k) r (ProofFile.pAtK2 Zp) enter leave B q.base d₁ d₂
      ((below B).lift Prod.snd fun t s => (t.1, s)) extq := by
  have hi : k < 357 := by
    rcases k2_spots k pl ha hk with ⟨l, _, _, rfl⟩ | rfl | rfl <;> omega
  have hm := mOf_lt ha hk
  obtain ⟨Bs, bs, O⟩ := Hd.laid.opened
  have hp := P1K2.hp_const Hd.toAtMg O (K2Ties.tableWrittenB_head Hd) Ts.spots Ts.links25 k pl ha
    hk hr
  have hnd : P5J.At.ps.Nodup := by rw [P1K2.ps_written]; exact IM.places_nodup
  obtain ⟨b1, b2⟩ := P1K2.piece_base_trees_at Hd.toAtMg L₀ q₁ q₂ q₃ k q hq hi B hB _ hS.rounds hnd
  have b3 : d₁.trees.length = (ProofFile.pAtK2 Zp (mOf k)).roots := by
    rw [e] at b2
    exact (List.cons.inj b2).1
  exact
    { frameFt := rfl
      blockAt := by rw [k2No_mOf ha hk]; exact hB
      sits := hS
      keepsOut := hK
      w2 := k2Wr_of hp he hkk
      baseIs := by rw [k2No_mOf ha hk]; exact b1
      treesLen := by
        intro lay₀ hl
        have hc : Zp.first.codes = K2Hands.csW := (at_written Hd.scope Hd.laid Ts.pinned).cs
        have kf := List.all_eq_true.1 rootsLay_full (mOf k) (List.mem_range.2 hm)
        rw [hr, ← hc, hl] at kf
        simp only [Option.any_some, beq_iff_eq] at kf
        rw [b3, hp.roots, kf]
      shownAll := shown }

/-- **«shown» AT THE CONSTANT**: shownAll_at_row at seats_at_row. -/
theorem shown_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x)
    (L₀ : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (Ts : K2Tests Z Zp Np cF) {k : ℕ}
    {q : Piece (ckP .two) (frC Dw) (ProofFile.InstPub × First.S) Cl
      (Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)}
    (hq : (Hd.toAtMg.row L₀)[k]? = some q) {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    q.ShownAll (dC Hd).G r.cs r.l (seatNew (P5J.At.N Zp cF) m r) :=
  P1K2.shownAll_at_row Hd.toAtMg L₀ k q hq
    (seats_at_row (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Hd.plan.fit
      (K2Ties.seats25_const (at_written Hd.scope Hd.laid Ts.pinned)) hr).1

/-- **ALL THREE LISTS, AT EVERY PLACE OF THE KIND.** -/
theorem lists_at_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x)
    (L₀ : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L₀.c₁ :: L₀.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃)
    (Ts : K2Tests Z Zp Np cF) (k : ℕ)
    (q : Piece (ckP .two) (frC Dw) (ProofFile.InstPub × First.S) Cl
      (Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok))
    (pl : VerifiableInference.Desc.Place) (hq : (Hd.toAtMg.row L₀)[k]? = some q)
    (ha : P5J.At.ps[k]? = some pl) (hk : pl.kind = KindName.K2) :
    ∃ (B : Block Rec Cl) (enter : Rec → Except String Rec)
      (leave : Rec → Rec → Except String Rec) (d₁ d₂ : RDT)
      (extq : (ProofFile.InstPub × First.S) × (frC Dw).E.Str → Tr (uLT (ckP .two) [d₁, d₂]) →
        Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok →
        Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)
      (Bs : ProofFile.PureBase) (bs : List (Block Rec Cl)) (A' : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat)
      (r : SwRow) (W : SwitchFrame),
      r.ok = true ∧ cF.blocksInOrder[k]? = some B ∧
      Sits B (K2.codeSwitchKind (ProofFile.pAtK2 Zp (mOf k)) : Block Rec Unit) enter leave ∧ LeftDoor enter leave ∧
      EndsUnmarked leave ∧ BookDoor enter leave ∧
      q = k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂ extq ∧
      [d₁, d₂].map (·.entry) = (K2.rounds (ProofFile.pAtK2 Zp (mOf k))).map (·.entry) ∧
      (∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind) ∧
      T14Left (F := frC Dw) (dC Hd) Hd.rchU Z (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) Dw
      r₀ Zp Np cF Bs bs A' B' (mOf k) r W laidFull (ProofFile.pAtK2 Zp) enter pl ∧
      T23More (F := frC Dw) (dC Hd) Zp cF (mOf k) r (ProofFile.pAtK2 Zp) enter leave B q.base d₁ d₂
        ((below B).lift Prod.snd fun t s => (t.1, s)) extq ∧
      T3More Zp Bs (mOf k) r (ProofFile.pAtK2 Zp) leave := by
  obtain ⟨B, enter, leave, hB, hS, hLD, hE, hBD, hW, hK, hWo⟩ :=
    P1K2.k02_sits7_pAt_at Hd.toAtMg Ts.spots Ts.links25 k pl ha hk
  have hi : k < 357 := by
    rcases k2_spots k pl ha hk with ⟨l, _, _, rfl⟩ | rfl | rfl <;> omega
  obtain ⟨d₁, d₂, extq, e, he, hkk⟩ :=
    P1K2.k2_written_at_row Hd.toAtMg L₀ q₁ q₂ q₃ k q hq hi B hB _ hS.rounds
  obtain ⟨Bs, bs, O⟩ := Hd.laid.opened
  have hm := mOf_lt ha hk
  have hlen : tableFullLit.length = 25 := congrArg Prod.fst seats25_counts
  obtain ⟨r, hr⟩ : ∃ r, tableFullLit[mOf k]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hm)⟩
  obtain ⟨W, hWf, -⟩ := front_tests_full (List.mem_of_getElem? hr)
  refine ⟨B, enter, leave, d₁, d₂, extq, Bs, bs, _, _, r, W,
    List.all_eq_true.1 tableFullLit_ok r (List.mem_of_getElem? hr), hB, hS, hLD, hE, hBD, e, he,
    hkk, t14Left_const Hd Ts O ha hk hW hr hWf,
    t23More_const Hd L₀ q₁ q₂ q₃ Ts ha hk hq hB hS hK hr e he hkk (e ▸ shown_const Hd L₀ Ts hq hr),
    t3More_const Hd Ts O ha hk hWo hr⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms P1K2.k02_sits7_pAt_at
#print axioms P1K2.pAt_nums
#print axioms P1K2.hp_const
#print axioms VerifiableInference.Desc.First.K2Caller.P2At.roots
#print axioms VerifiableInference.Desc.First.K2Caller.k2LogN_full
#print axioms VerifiableInference.Desc.First.K2Caller.k2LogN_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.rootsLay_full
#print axioms VerifiableInference.Desc.First.K2Caller.rootsLay_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.t14_laidL
#print axioms VerifiableInference.Desc.First.K2Caller.mOf_lt
#print axioms VerifiableInference.Desc.First.K2Caller.t14Left_const
#print axioms VerifiableInference.Desc.First.K2Caller.t3More_const
#print axioms VerifiableInference.Desc.First.K2Caller.t23More_const
#print axioms VerifiableInference.Desc.First.K2Caller.shown_const
#print axioms VerifiableInference.Desc.First.K2Caller.lists_at_const
