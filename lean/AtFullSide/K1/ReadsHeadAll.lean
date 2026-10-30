-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsHeadAll.lean: THE PUBLIC PREMISES OF vecTie_head_of (ReadsHead.lean), PAID UNDER THE HEAD. Public data alone, but for hPhi, which stays.

  partsFit_head   the parts' test at every list of tables of the head's shapes whose weights fit: partsOf is the written list; one fact of Lean's kernel
  headFs_at_head  headCallsShape Zp = G.W.HLy.fs: the site on the calls at link 24 against shape_head
  vecTie_head     VecTie at 342 at a seat of segment 24's U3, at nReads, under h, hSaid, hPhi

This letter is for the honest run's own forms alone. NEVER ON SOUNDNESS's ROAD.
NO PROPERTY IS CLAIMED. -/
import AtFullSide.K1.ReadsHead
import AtFullSide.K1.ReadsCount
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.HonestTrace.U3Fit.HeadAtHead
import Johnson.HonestTrace.U3Fit.LookFits
import Johnson.HonestTrace.U3Fit.Slice
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie
import Johnson.Desc.First.Close.Law.HingeMore
import Johnson.Desc.K1.Law.OwnHeldAtSendings
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW plan_in_scope)
open OnBytes.HonestTrace.U3 (covOf u3Seats placeIn SegVals partsFit partsOf sizesOf)
open ProofFile (Spot spotsOf)
open OnBytes.HonestTrace.U3.Fit
open OnBytes.Tie.Pv.Tail.Closed (asksShapes headAsks headShapes shapesOf)
open ProofFile.Honest.K3 (lookSites siteAt)
open ProofFile.Honest.K3.Law.AtThr (headCallsShape)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K6 (headParAt headInFront)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.G (xShapeFull)

/-- The head's fifteen tables at the written numbers. -/
def asksW : List (ℕ × ℕ × ℕ) :=
  [(0, 4, 2 ^ 16), (0, 4, 2 ^ 16), (4 + 1 + 1 + 1, 1, 2 ^ 16), (4 + 1 + 1 + 1, 1, 2 ^ 16),
   (4, 1, 1024), (4, 1, 1024), (4 + 1, 1, 1024), (4 + 1, 1, 1024), (4 + 1, 1, 1024), (4 + 1, 1, 1024),
   (4 + 1, 1, 1024), (4 + 1, 1, 1024), (4 + 1 + 1, 1, 2 ^ 15), (4 + 1 + 1, 1, 2 ^ 15),
   (4 + 1 + 1, 1, 2 ^ 15)]

/-- The parts of the head's tables at the written numbers, with as many weights as the length. -/
def headPartsW : List (ℕ × ℕ × ℕ × ℕ) :=
  (asksShapes matsW asksW 0).map fun T => (T.mat, T.len, T.len, T.start)

/-- The test passes as a Bool. -/
def partsOkB (n : ℕ) : Bool :=
  match partsFit (sizesOf matsW) headPartsW n with
  | .ok _ => true
  | .error _ => false

set_option maxRecDepth 1000000 in
theorem partsW_ok : partsOkB (xShapeFull.2.1.getD 2 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one read more and the test says no. -/
theorem partsW_bent : partsOkB (xShapeFull.2.1.getD 2 0 + 1) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The parts' test under the head.** -/
theorem partsFit_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (funs : Array HFun)
    (hs : shapesOf funs = headShapes G.W.hS G.W.H.tl.mats)
    (hphi : ∀ Fn ∈ funs.toList, Fn.phi.size = Fn.len) :
    partsFit (sizesOf G.W.H.tl.mats) (OnBytes.HonestTrace.U3.partsOf funs) (G.W.H.nU.getD 2 0) = .ok () := by
  have hW := IM.ground_publicK h.laid.pub hG
  have PW := plan_in_scope h.scope h.reads hW
  have eS := _root_.Meaning.HeadS.hS_in_scope h.scope h.reads hW
  have eN : G.W.hS.NHf = 4 := by rw [eS]; rfl
  have eA : G.W.hS.la = 16 := by rw [eS]; rfl
  have eT : G.W.hS.T = 1024 := by rw [eS]; rfl
  have eB : G.W.hS.lmbH = 15 := by rw [eS]; rfl
  have e1 : headAsks G.W.hS = asksW := by
    unfold headAsks
    rw [eN, eA, eT, eB]
    rfl
  have ep : OnBytes.HonestTrace.U3.partsOf funs = headPartsW := by
    have e2 : funs.toList.map (fun f => (f.mat, f.len, f.phi.size, f.start)) =
        (shapesOf funs).map (fun T => (T.mat, T.len, T.len, T.start)) := by
      unfold shapesOf
      rw [List.map_map]
      exact List.map_congr_left fun f hf => by simp [hphi f hf]
    show funs.toList.map (fun f => (f.mat, f.len, f.phi.size, f.start)) = _
    rw [e2, hs]
    unfold headShapes headPartsW
    rw [e1, PW.mats]
  rw [ep, PW.mats, nU_at_head h hG]
  have q := partsW_ok
  unfold partsOkB at q
  cases e : partsFit (sizesOf matsW) headPartsW (xShapeFull.2.1.getD 2 0) with
  | ok u => rfl
  | error w =>
    rw [e] at q
    cases q

/-- **The shape of the lookup on the head's calls.** -/
theorem headFs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : headCallsShape Zp = G.W.HLy.fs := by
  obtain ⟨s, hs, e1, e2, e3⟩ := ProofFile.Honest.K3.Law.AtThr.head_calls_site_found h
  obtain ⟨y, -, hy⟩ := List.mem_filterMap.1 hs
  unfold siteAt at hy
  obtain ⟨p, hp, hy⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨hh, hh', hy⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨n, -, hy⟩ := Option.bind_eq_some_iff.1 hy
  dsimp only at hy
  have hW : G.W = Zp.p.X := ProofFile.Law.blankBy_W hG
  split at hy
  · rename_i hd
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 hy
    have : y.2.1 = false := e2
    rw [this] at hd
    cases hd
  · obtain rfl := Option.some.inj hy
    have f1 : y.1 = 24 := e1
    have f2 : y.2.1 = false := e2
    rw [f1, f2, ← hW] at hp
    have f3 := shape_head h hG p hp
    rw [e3]
    exact Option.some.inj (hh'.symm.trans f3)

/-- At the written seats: each seat of segment 24 stands behind the head's own rounds. -/
def headSeatB (d : ℕ) : Bool :=
  match placeBy cutWritten spotsWritten 24 .K6 with
  | .ok k6 => (seatsW "U3").all fun s =>
      s.seg != 24 || decide (k6.2 + 82 + d ≤ OnBytes.HonestTrace.heardOf (seatsW "U3") s.addr)
  | .error _ => false

set_option maxRecDepth 1000000 in
theorem headSeat_ok : headSeatB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one round further the test says no. -/
theorem headSeat_bent : headSeatB 1 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Member 341's row: 82 rounds; so the rounds in front of 342 are 82 more than in front of 341. -/
theorem row341_ok : ((VerifiableInference.PlanWritten.cutFirstFull[341]?).map (·.2.2.1)) = some 82 ∧
    rowsBeforeW 341 + 82 ≤ rowsBeforeW 342 := by decide +kernel

/-- **VecTie at the output head's reads.** -/
theorem vecTie_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} (hwit : ∀ v, (wit v).x = v.x)
    {st : OnBytes.HonestTrace.Seat} (hst : st ∈ u3Seats Zp G) (hseg : st.seg = 24)
    (hPhi : ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[342]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 342 k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl → ∀ Fn ∈ tl.funs.toList, Fn.phi.size = Fn.len) :
    VecTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said 342 wit Zp G 24
      (nReads (P5J.At.X Zp) 24) st.addr := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O 24 (by omega)
  have he' : cF.blocksInOrder[342]? = some e := he
  obtain ⟨m2, f2, k2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).2
  obtain rfl : m2 = Xl := Option.some.inj (f2.symm.trans hX)
  have hq := VerifiableInference.Desc.K1.quiet_of_kind Bs.G₀ 24 m2 hX k2
  have hW := IM.ground_publicK h.laid.pub hG
  have hGW : Bs.G₀.W = P5J.At.X Zp := ProofFile.Law.blankBy_W hG
  have q6 := placeIn_by Zp spotsWritten 24 .K6
  have q3 := placeIn_by Zp spotsWritten 24 .K3
  rw [cuts_at_head h] at q6 q3
  have hw := List.all_eq_true.1 lookPlacesW_yes 24 (List.mem_range.2 (by omega))
  cases e3 : placeBy cutWritten spotsWritten 24 .K3 with
  | error w' =>
    rw [e3] at hw
    cases hw
  | ok k3 =>
    cases e6 : placeBy cutWritten spotsWritten 24 .K6 with
    | error w' =>
      have : ownOf 24 = .K6 := rfl
      simp [this, e3, e6] at hw
    | ok k6 =>
      have : ownOf 24 = .K6 := rfl
      simp only [this, e6, e3, Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨w3, w6⟩ := hw
      rw [e6] at q6
      rw [e3] at q3
      have h82 := headInFront_at_head h hG
      have hb6 : k6.2 = roundsTo cF.blocksInOrder 341 := by
        rw [roundsTo_at_head h]
        exact w6
      have hb3 : k3.2 = roundsTo cF.blocksInOrder 340 := by
        rw [roundsTo_at_head h]
        exact w3
      have hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt Bs.G₀) 8 = b₆.rounds.length := by
        intro b₆ hb₆
        have hc := First.Close.hc_at_laid h.scope h.laid
        have e1 : ((VerifiableInference.PlanWritten.cutOf cF.blocksInOrder)[341]?).map (·.2.2.1) = some b₆.rounds.length := by
          unfold VerifiableInference.PlanWritten.cutOf
          rw [List.getElem?_map, hb₆]
          rfl
        rw [hc, row341_ok.1] at e1
        rw [h82]
        exact Option.some.inj e1
      have hsw : u3Seats Zp Bs.G₀ = seatsW "U3" := seats_at_head h hG "U3"
      have hcut : k6.2 + headInFront (headParAt Bs.G₀) 8 ≤
          OnBytes.HonestTrace.heardOf (u3Seats Zp Bs.G₀) st.addr := by
        have k := headSeat_ok
        unfold headSeatB at k
        rw [e6] at k
        have k' := List.all_eq_true.1 k st (hsw ▸ hst)
        simp only [hseg, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at k'
        rw [h82, hsw]
        exact k'
      have hfull : k6.2 + headInFront (headParAt Bs.G₀) 8 ≤ roundsTo cF.blocksInOrder 342 := by
        rw [h82, roundsTo_at_head h]
        have := row341_ok.2
        have e0 : k6.2 = rowsBeforeW 341 := w6
        omega
      have eN : nReads (P5J.At.X Zp) 24 = Bs.G₀.W.H.nU.getD 2 0 := by
        unfold nReads
        rw [if_pos rfl, ← hGW]
      rw [eN]
      exact vecTie_head_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hG hq hGW
        (_root_.Fo.Pub.public_T hW).symm (_root_.Fo.Pub.public_V hW).symm he' (IM.alone_underR hu)
        (spots_at_head h) hX k2 q6 q3 hb6 hb3 hlen hcut hfull (headFs_at_head h hG)
        (fun funs a b => partsFit_head h hG funs a b) hwit hPhi

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.partsW_ok
#print axioms ProofFile.Honest.K1.partsW_bent
#print axioms ProofFile.Honest.K1.partsFit_head
#print axioms ProofFile.Honest.K1.headFs_at_head
#print axioms ProofFile.Honest.K1.headSeat_ok
#print axioms ProofFile.Honest.K1.headSeat_bent
#print axioms ProofFile.Honest.K1.row341_ok
#print axioms ProofFile.Honest.K1.vecTie_head
