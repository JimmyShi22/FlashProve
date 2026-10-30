-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K2R/LastJoin5.lean: FOR THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): THE INDEX MASKS' TREE WAS SENT
    IN FRONT OF THE PIECE. One theorem. A law file: no sub-protocol imports it.

What is said. `base_at`: under the head (with the fourteen entry tests) and "L₀'s three lists are
    the description's own", at every place of the kind: `piece_base_trees_at`
    (Johnson/P1K2R/PieceBaseTrees.lean: the base is the table's count of trees in front),
    `P5J.LaidAt.fence` (Johnson/P5T/CoreAtMg.lean: the table's test on the fence, from the
    scope and "the value is laid") and `hidx_at`.

Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/): the theorem may be idle. The import lines are wider than
    the theorem needs. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastJoin4
import Johnson.P1K2R.ShownAtRow
import Johnson.P5J.FoldJ3
import Johnson.P5T.CoreAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Chain Claim FileDescription Strs Wit KindName smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid snAt sendsAreB laidAtCodes)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers flatPlacesOf
    laysPads)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left HeadBears saidBehindB
    decBlind_at AtWritten AtTold at_written at_told sends_at offC_head codes_of_sends left_of_seat)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor EndsUnmarked BookDoor mOf said_at hsam_at hidx_at k2No_mOf
    k2_written_at_row k2_unmarked_at k2_spots piece_base_trees_at flat_planOk linkPlanB k5PlanB
    headPlanB)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB fxAt)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF
                  : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The index masks' tree was sent in front of the piece.** -/
theorem base_at (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (L₀ : P5J.Free numsFull Dw
                (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
                            = L₀.c₁ :: L₀.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂) (q₃ :
                                                 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃) {k : ℕ} {q : Piece (ckP .two)
                                                                      (frC Dw) (ProofFile.InstPub × First.S) Cl (Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)} {pl :
                                                                            VerifiableInference.Desc.Place} (hq : (Hd.toAtMg.row L₀)[k]? = some q) (ha : P5J.At.ps[k]? =
                                                                            some pl) (hk : pl.kind = KindName.K2) {B : Block Rec Cl} (hB : cF.blocksInOrder[k]? = some B) {p : K2.P2}
    (hr : B.rounds = K2.rounds p) :
    (dC Hd).N.index.1 < q.base := by
  have hi : k < 357 := by
    rcases k2_spots k pl ha hk with ⟨l, _, _, rfl⟩ | rfl | rfl <;> omega
  rw [(piece_base_trees_at Hd.toAtMg L₀ q₁ q₂ q₃ k q hq hi B hB p hr ps_nodup).1]
  exact VerifiableInference.Desc.First.fenceFit_at (P5J.At.N Zp cF) P5J.fullLinks P5J.At.ps
      (Hd.toAtMg.laid.fence Hd.toAtMg.scope) k (by rw
      [VerifiableInference.Desc.Kinds.Head.Law.ps_length]; omega) _ (hidx_at _ ha hk)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.base_at
