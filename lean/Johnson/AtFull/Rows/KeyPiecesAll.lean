-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/KeyPiecesAll.lean: THE WALK OF «key 0» AT rowsW's WRITTEN VALUES, FROM ITS 32
PIECES' CLOSED FACTS (KeyPiecesA.lean to KeyPiecesD.lean), with one premise left: that its written
rounds are 18,852. A law file; no running text imports it.
  `lenK`: [Lean's kernel] «key 0» has 32 pieces at the written values.
  `piecesK_all`: the 32 facts as one «for all i below 32».
  `good_key0_of_drops`: dk ⊢ Good sW (kW 0).rounds (⟨.once, 0, 0, 0⟩, 0) (key0R cW): the premise g0
    of the last join. dk is JoinKey.lean's own premise of that name, another file's closed fact
    (drops_k0).

Limits. What `Good` says: the routine returns, ends at counters 0, and its rounds are, by `sameAll`
(four of a round's fields), the written ones. At the written values alone: that these are what the
planner makes of any public files is not said. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.GoodKey
import Johnson.AtFull.Rows.KeyPiecesA
import Johnson.AtFull.Rows.KeyPiecesB
import Johnson.AtFull.Rows.KeyPiecesC
import Johnson.AtFull.Rows.KeyPiecesD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

set_option maxRecDepth 100000 in
theorem lenK : ((key0Pieces cW).length == 32) = true := by decide +kernel

theorem piecesK_all : ∀ i, i < 32 →
    pieceD sW (kW 0).rounds (tabK3 i) ((key0Pieces cW).getD i (pure ())) = some (tabK3 (i + 1))
  | 0, _ => pieceK_00
  | 1, _ => pieceK_01
  | 2, _ => pieceK_02
  | 3, _ => pieceK_03
  | 4, _ => pieceK_04
  | 5, _ => pieceK_05
  | 6, _ => pieceK_06
  | 7, _ => pieceK_07
  | 8, _ => pieceK_08
  | 9, _ => pieceK_09
  | 10, _ => pieceK_10
  | 11, _ => pieceK_11
  | 12, _ => pieceK_12
  | 13, _ => pieceK_13
  | 14, _ => pieceK_14
  | 15, _ => pieceK_15
  | 16, _ => pieceK_16
  | 17, _ => pieceK_17
  | 18, _ => pieceK_18
  | 19, _ => pieceK_19
  | 20, _ => pieceK_20
  | 21, _ => pieceK_21
  | 22, _ => pieceK_22
  | 23, _ => pieceK_23
  | 24, _ => pieceK_24
  | 25, _ => pieceK_25
  | 26, _ => pieceK_26
  | 27, _ => pieceK_27
  | 28, _ => pieceK_28
  | 29, _ => pieceK_29
  | 30, _ => pieceK_30
  | 31, _ => pieceK_31
  | n + 32, h => absurd h (by omega)

/-- **The walk of «key 0», from its pieces.** -/
theorem good_key0_of_drops
    (dk : (((kW 0).rounds.drop (18851 + 1)).isEmpty && !((kW 0).rounds.drop 18851).isEmpty) =
      true) : Good sW (kW 0).rounds (⟨.once, 0, 0, 0⟩, 0) (key0R cW) :=
  good_key0_of_pieces lenK dk piecesK_all

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lenK
#print axioms VerifiableInference.Desc.LinkJoin.piecesK_all
#print axioms VerifiableInference.Desc.LinkJoin.good_key0_of_drops
