-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Head.lean: AT THE CLOSED CONSTANT: THE FIELD OF THE KIND K10 (`h.Kind L .K10`) FROM
THE HEAD AND `rowsRead Z`. A statement and its proof: two calls.

  `k10_kind_head`: `k10_kind_of_car_head` (K10TopReads.lean, beside this file) with its one debt
    `AtMgA.K10CarAll` (what stands behind the closing, at all 25 links) paid by
    `AtMgA.k10CarAll_paid` (Johnson/Desc/First/Link/Law/K10CarAllPaid.lean).
  ITS BINDERS: the head h · the filling L · q1, q2, q3 · AND ONE FURTHER ANTECEDENT: `rowsRead Z`:
    the goals' one named condition; it is no part of the head.
Limits. NOT "from the head alone". Nothing is shown of any state: that a statement is inside the
promise, reached and unmarked at one of K10's 25 borders is shown nowhere beneath; a member of the
head itself is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At the
format's second hash function; at the full size. Nothing on soundness.

-/
import Johnson.P5J.K10TopReads
import Johnson.Desc.First.Link.Law.K10CarAllPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts rowSegs)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.First.Close (K10FirstTie K10Car K10Last k10_last_of_two namesOf noK10
seatK10 written_of_mem
  linksFull_layout onS_of_rowAsks fa_front_same good_cs
  plan_of_shapes stPub layPub begun_at shapesAre_begun)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt tie_at_laid smpDrawn covered_laid hm_at
  plainDue gensDue numBy esOf esOf_nodup esOf_all pSseed)
open VerifiableInference.Desc.First.Close (kLay kbAt layPub_some joint0 joint0_on wit0 brw0 smp0)
open VerifiableInference.Desc.P2Notices (seed_at_K10)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First.Close (loFive loSix kbFive kbSix noFiveAt loFive_written
    five_layout
  five_kLay five_corners_at five_entries membersOf hMSub hZSub Corners layAt sizesM sizesZ RowAsks
  ShapesAre hPr_of k10_heavy_of_asks)
open VerifiableInference.Desc.LinkJoin (seatFiveAt plan_seven_five sitsIn_five tie_five_laid SitsIn
  PlanSeven esOf_length k10_rows_due)
open VerifiableInference.Desc.P2Notices (seed_at_five)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- The first chain's pieces' type. -/
local notation "PC" => Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl
  (Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

/-- **THE FIELD OF THE KIND K10, FROM THE HEAD AND rowsRead Z.** -/
theorem k10_kind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (hrr : rowsRead Z) :
    h.Kind L .K10 :=
  k10_kind_of_car_head h L q1 q2 q3 hrr (h.k10CarAll_paid L q1 q2 q3 hrr)

end P5J

#print axioms P5J.k10_kind_head
