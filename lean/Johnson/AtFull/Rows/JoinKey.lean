-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/JoinKey.lean: THE LAST JOIN WITH «key 0» BY ITS 32 PIECES: every closed
fact beneath `rowsWB = true` as a named premise, «key 0» by the two premises on the pieces (lenK,
pk). After the text of a join by nine slices (not in this library), but for the line that makes g0.
A law file; no running text imports it.
  `rowsWB_of_pieces`: every closed fact a named premise, each in the form in which its own file
    states it ⊢ rowsWB = true.
  `rowsWB_of_rest`: the same with lenK and pk paid (KeyPiecesAll.lean): twelve premises left, all
    closed facts of other files; Johnson/AtFull/Rows/Rows.lean feeds them.

Limits. IT PAYS NOTHING BUT lenK AND pk: EVERY OTHER PREMISE IS OWED; if one
were false the theorem would be empty: it is not to be counted or quoted as «rowsWB = true». What
its end says: a maker returns at written values. The limits of «rowsWB = true» stand in the head of
Johnson/AtFull/Rows/Rows.lean. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Join
import Johnson.AtFull.Rows.KeyPiecesAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- **The last join, «key 0» by its pieces.** -/
theorem rowsWB_of_pieces
    (lens : (cW.key.length == 3 && cW.proof.length == 3 && piecesW.length == 27) = true)
    (dp : (((prW 0).rounds.drop (48292 + 1)).isEmpty && !((prW 0).rounds.drop 48292).isEmpty) =
      true)
    (dk : (((kW 0).rounds.drop (18851 + 1)).isEmpty && !((kW 0).rounds.drop 18851).isEmpty) = true)
    (pc : ∀ i, i < 27 →
      pieceD sW (prW 0).rounds (tabW i) (piecesW.getD i (pure ())) = some (tabW (i + 1)))
    (lenK : ((key0Pieces cW).length == 32) = true)
    (pk : ∀ i, i < 32 →
      pieceD sW (kW 0).rounds (tabK3 i) ((key0Pieces cW).getD i (pure ())) = some (tabK3 (i + 1)))
    (k1 : pieceB sW (kW 1).rounds (⟨scOf cW.sized.key.once .shared, 0, 0, 0⟩, 0) (key1R cW) =
      some (⟨.once, 0, 0, 0⟩, (kW 1).rounds.length))
    (k2 : pieceB sW (kW 2).rounds (⟨scOf cW.sized.key.once .request, 0, 0, 0⟩, 0) (key2R cW) =
      some (⟨.once, 0, 0, 0⟩, (kW 2).rounds.length))
    (e0 : pieceB sW (cW.entry).rounds (⟨.once, 0, 0, 0⟩, 0) (entryR cW) =
      some (⟨.once, 0, 0, 0⟩, (cW.entry).rounds.length))
    (q1 : pieceB sW (prW 1).rounds (⟨scOf cW.sized.proof.batch .shared, 0, 0, 0⟩, 0)
      (proof1R cW) = some (⟨.shared, 0, 0, 0⟩, (prW 1).rounds.length))
    (q2 : pieceB sW (prW 2).rounds (⟨scOf cW.sized.proof.batch .request, 0, 0, 0⟩, 0)
      (proof2R cW) = some (⟨.request, 0, 0, 0⟩, (prW 2).rounds.length))
    (t0 : endOf sW ⟨.once, 0, 0, 0⟩ (key0L cW) = some ⟨.once, 0, 0, 0⟩)
    (t4 : endOf sW ⟨.request, 0, 0, 0⟩ (proof0L cW (List.replicate 25 1) 13) =
      some ⟨.request, 0, 0, 0⟩)
    (ht : (tailFrom cW sW (twinsL cW (List.replicate 25 1) 13)).toOption.isSome = true) :
    rowsWB = true := by
  have l3 : cW.key.length = 3 ∧ cW.proof.length = 3 ∧ piecesW.length = 27 := by
    simp only [Bool.and_eq_true, beq_iff_eq] at lens
    exact ⟨lens.1.1, lens.1.2, lens.2⟩
  have hk : cW.key = [kW 0, kW 1, kW 2] := list3 _ _ l3.1
  have hp : cW.proof = [prW 0, prW 1, prW 2] := list3 _ _ l3.2.1
  have lp : (prW 0).rounds.length = 48292 + 1 := length_of_drops _ _ dp
  have g4 : Good sW (prW 0).rounds (⟨.request, 0, 0, 0⟩, 0)
      (proof0R cW (List.replicate 25 1) 13 armAtW) := by
    rw [proof0R_seq]
    exact good_of_tableC (s := sW) (truth := (prW 0).rounds) (sc' := .request) tabW piecesW
      (fr_proof0Pieces cW (List.replicate 25 1) 13 armAtW)
      (faith_proof0Pieces cW (List.replicate 25 1) 13 armAtW)
      (fun i hi => (pieceD_eq _ _ _ _).symm.trans (pc i (l3.2.2 ▸ hi)))
      (by rw [l3.2.2, lp]; rfl)
  have g0 : Good sW (kW 0).rounds (⟨.once, 0, 0, 0⟩, 0) (key0R cW) :=
    good_key0_of_pieces lenK dk pk
  unfold rowsWB rowsW
  exact rows_of_partsL (c := cW) (sc0 := .once) (sc4 := .request) hk hp g0
    (good_one (fr_key1R cW) k1) (good_one (fr_key2R cW) k2) (good_one (fr_entryR cW) e0) g4
    (good_one (fr_proof1R cW) q1) (good_one (fr_proof2R cW) q2) t0 t4 ht

/-- **The same with the pieces of «key 0» paid.** -/
theorem rowsWB_of_rest
    (lens : (cW.key.length == 3 && cW.proof.length == 3 && piecesW.length == 27) = true)
    (dp : (((prW 0).rounds.drop (48292 + 1)).isEmpty && !((prW 0).rounds.drop 48292).isEmpty) =
      true)
    (dk : (((kW 0).rounds.drop (18851 + 1)).isEmpty && !((kW 0).rounds.drop 18851).isEmpty) = true)
    (pc : ∀ i, i < 27 →
      pieceD sW (prW 0).rounds (tabW i) (piecesW.getD i (pure ())) = some (tabW (i + 1)))
    (k1 : pieceB sW (kW 1).rounds (⟨scOf cW.sized.key.once .shared, 0, 0, 0⟩, 0) (key1R cW) =
      some (⟨.once, 0, 0, 0⟩, (kW 1).rounds.length))
    (k2 : pieceB sW (kW 2).rounds (⟨scOf cW.sized.key.once .request, 0, 0, 0⟩, 0) (key2R cW) =
      some (⟨.once, 0, 0, 0⟩, (kW 2).rounds.length))
    (e0 : pieceB sW (cW.entry).rounds (⟨.once, 0, 0, 0⟩, 0) (entryR cW) =
      some (⟨.once, 0, 0, 0⟩, (cW.entry).rounds.length))
    (q1 : pieceB sW (prW 1).rounds (⟨scOf cW.sized.proof.batch .shared, 0, 0, 0⟩, 0)
      (proof1R cW) = some (⟨.shared, 0, 0, 0⟩, (prW 1).rounds.length))
    (q2 : pieceB sW (prW 2).rounds (⟨scOf cW.sized.proof.batch .request, 0, 0, 0⟩, 0)
      (proof2R cW) = some (⟨.request, 0, 0, 0⟩, (prW 2).rounds.length))
    (t0 : endOf sW ⟨.once, 0, 0, 0⟩ (key0L cW) = some ⟨.once, 0, 0, 0⟩)
    (t4 : endOf sW ⟨.request, 0, 0, 0⟩ (proof0L cW (List.replicate 25 1) 13) =
      some ⟨.request, 0, 0, 0⟩)
    (ht : (tailFrom cW sW (twinsL cW (List.replicate 25 1) 13)).toOption.isSome = true) :
    rowsWB = true :=
  rowsWB_of_pieces lens dp dk pc lenK piecesK_all k1 k2 e0 q1 q2 t0 t4 ht

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsWB_of_pieces
#print axioms VerifiableInference.Desc.LinkJoin.rowsWB_of_rest
