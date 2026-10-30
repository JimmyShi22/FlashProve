-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10FiveFacts.lean: AT THE CLOSED CONSTANT, AT LINK 0, AT THE FIVE-LIST (`loFive`: the
first written list without its one message without a main row): THE SMALL FACTS IN THE FORMS IN
WHICH THE JOIN AT LINK 0 SPENDS THEM. Statements and proofs: calls of several theorems.

  `gs0_ok`: the written row 0's group in front is a written group in front; its k is the formula's
    at the SIX-list. `k10_hM_five`, `k10_hZ_five`: the two sentences on the codes at the five-list.
    `k10_corners_five`, `kL_five`: the corners and the number of row variables at the five-list.
  `k10_hX_five_l`: the row asks (`AtMgA.hX_five_head`, with 0 for the place's link).
    `k10_sits_five`, `k10_seven_five`: `SitsIn` and the plan's seven at the five-list
    (`sitsIn_five`, `plan_seven_five`). `k10_hinge_five`: the hinge at the five-list at a statement
    with `XK h 0` (`AtMg.hinge_five_at_border`; `FoldFacts` from the head).
  `five_members_len`: the two lists have equally many members. `k10_rows_five`: Q.rows = nPK + the
    members' samples' number at the five-list + nGK.
Limits. Under the head; two under `rowsRead Z`. Nothing on soundness.

-/
import Johnson.P5J.K10AllLink
import Johnson.P5J.K10HXHead
import Johnson.P2LawR.SeedAtFive
import Johnson.LPFE1R.PlanSevenFive

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

theorem gs0_ok : gsAt 0 ∈ Johnson.G.frontFull ∧ (gsAt 0).k = kLay loSix kbSix :=
  gsAt_ok 0 (by omega)

theorem k10_hM_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C := by
  rw [h.toAtMg.codes_full]
  exact hMSub loFive loFive_written (gsAt 0) gs0_ok.1

theorem k10_hZ_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z := by
  rw [h.toAtMg.codes_full]
  exact hZSub loFive loFive_written (gsAt 0) gs0_ok.1

theorem k10_corners_five :
    Corners loFive (gsAt 0).k (fun i => layAt (sizesM loFive kbFive) i.val)
      (fun i => layAt (sizesZ loFive) i.val) kbFive :=
  five_corners_at (gsAt 0) gs0_ok.2

theorem kL_five :
    kLay loFive kbFive = (stageOf (gsAt 0) 219).h + (stageOf (gsAt 0) 219).g :=
  five_kLay.trans (kh_at 0 (by omega)).1

/-- The row asks at the five-list, with 0 for the place's link. -/
theorem k10_hX_five_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p :
                VerifiableInference.Desc.Place) (hp : At.ps[ixK10 0]? = some p)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) →
      RowAsks (At.cs Zp) loFive (seatFiveAt (At.pseats Zp)) kbFive
        (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)
        (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ
          (noFiveAt (At.seats Zp) (At.pseats Zp)))
        (At.N Zp cF) 0 (oAt (ixK10 0)) (noFiveAt (At.seats Zp) (At.pseats Zp)) a.1 := by
  have t := h.hX_five_head p hp hM hZ (k10_hM_l h 0 (by omega)) (k10_hZ_l h 0 (by omega))
  rw [k10_link_is 0 (by omega) p hp] at t
  exact t

theorem k10_sits_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hrr : rowsRead Z) (p :
                VerifiableInference.Desc.Place) (hp : At.ps[ixK10 0]? = some p)
    (hK : p.kind = KindName.K10) :
    SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 0)) loFive (seatFiveAt (At.pseats Zp)) :=
  sitsIn_five h hrr hp hK (k10_link_is 0 (by omega) p hp)

theorem k10_seven_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hrr : rowsRead Z) (p :
                VerifiableInference.Desc.Place) (hp : At.ps[ixK10 0]? = some p)
    (hK : p.kind = KindName.K10) :
    PlanSeven (At.N Zp cF) (At.ms Zp Z.lay) (At.arr Zp) fullLinks At.ps (ixK10 0) p loFive
      (seatFiveAt (At.pseats Zp)) :=
  plan_seven_five h.scope h.laid hrr hp hK (k10_link_is 0 (by omega) p hp)

/-- The hinge at the five-list. -/
theorem k10_hinge_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) (a : TS ×
                      (Frame.E FR).Str)
    (hx : XK h 0 ((z, a.1), a.2)) :
    ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr →
      ShapesAre (rdK a.1).2.2 Gr loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) := by
  have hr := hx.2.1
  rw [ixK10_is 0 (by omega)] at hr
  exact h.toAtMg.hinge_five_at_border (atMgR_rch_of_head h).choose_spec.fold rfl ((z, a.1), a.2) hr
    (not_not.1 hx.2.2)

theorem five_members_len : (membersOf loFive).length = (membersOf loSix).length := by
  have e := congrArg List.length five_entries
  rwa [List.length_map, List.length_map] at e

/-- The maker's number of rows at link 0 is the sum of the three counts, at the five-list. -/
theorem k10_rows_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par)
    (h9 : IM.k9At Zp 0 = some pw) (hQp : ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q)
    (hfl : cF.blocksInOrder[ixK10 0]? = some b) (hBK : b.place.kind = KindName.K10)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z) :
    Q.rows = nPK Zp cF 0 +
      (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).length +
      nGK Zp cF 0 := by
  rw [esOf_length, five_members_len]
  exact k10_rows_due h.scope h.laid (by omega) hfl
    (k10_rounds_l h 0 (by omega) pw b Q h9 hQp hfl hBK)

end P5J

#print axioms P5J.gs0_ok
#print axioms P5J.k10_hM_five
#print axioms P5J.k10_hZ_five
#print axioms P5J.k10_corners_five
#print axioms P5J.kL_five
#print axioms P5J.k10_hX_five_l
#print axioms P5J.k10_sits_five
#print axioms P5J.k10_seven_five
#print axioms P5J.k10_hinge_five
#print axioms P5J.five_members_len
#print axioms P5J.k10_rows_five
