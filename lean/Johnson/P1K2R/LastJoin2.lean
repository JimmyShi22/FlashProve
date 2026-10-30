-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastJoin2.lean: FOR THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): THE CONSTANT's LIST OF PLACES
    NAMES NO PLACE TWICE. One theorem. A law file: no sub-protocol imports it.

What is said. `ps_nodup`: `P5J.At.ps.Nodup`: `IM.places_nodup`
    (Johnson/IMR/BorderW.lean) along "one written list under two names" (`HashBuild.placesW_full`).

Limits. A fact on the written list. The import lines are wider than the theorem needs: the files
    above take Johnson/P1K2R/TiesTwoThree.lean and PieceBaseTrees.lean through this one. No
    soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.TiesTwoThree
import Johnson.P1K2R.LastJoin
import Johnson.P1K2R.PieceBaseTrees
import Johnson.IMR.BorderW

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
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left saidBehindB decBlind_at)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor EndsUnmarked BookDoor mOf mOf_link said_at hsam_at hidx_at k2No_mOf
    k2_written_at_row k2_unmarked_at k2_spots piece_base_trees_at k02_sits_pAt flat_planOk
    back_planOk leftDoor_opened leftDoor_head leftDoor_finish ends_opened ends_head ends_finish
    bookDoor_opened bookDoor_head bookDoor_finish out_opened out_head out_finish)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB fxAt)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

theorem ps_nodup : P5J.At.ps.Nodup := by
  have h := IM.places_nodup
  rw [HashBuild.placesW_full] at h
  exact h

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.ps_nodup
