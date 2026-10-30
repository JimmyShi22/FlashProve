-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/CellsAtMatrix.lean: WHAT THE KIND K11 ASKS OF THE SCRIPT's
CELLS (`K11CellsQ`, TiesAtHeadStatement.lean of this folder) AT A SCRIPT WHOSE CELLS ARE, AT EACH
VALID INPUT, THE MATRIX OF THE INPUT's INDEX (`Flat.matrixOf`, Johnson/Flat/ThreeFull.lean). One
lemma with its proof; no definition; none of the library's goals.

IT PAYS NOTHING. IT TRADES one premise on the Script for two. hQ: the Script's cells are laid so: a
laying, the frame's authors'; shown of no Script. hw: the honest side's reader `weights` hands the
entries of that same index: an identity of two readers of the index, the index under "for all" and
the same on both sides; no run's letter in it; shown of no filling. The first half of what is spent,
that the matrix of an index holds that index, is TRUE BY CONSTRUCTION (`Flat.holds_matrixOf`): say
never "paid".

A PREMISE ON THE INDEX's OWN VALUES, OF COMPLETENESS's KIND: never to be laid in front of a law over
coins.

How. Two calls: `cellsOfIndex` (CellsOfIndex.lean of this folder) at i := idx v.w₀;
`Flat.holds_matrixOf`. At W₀ := Cm.Idx and idx := id, hQ reads: the cells are Flat.matrixOf v.w₀. hw
asks at every w, not at the valid inputs' alone: more than `cellsOfIndex` needs.

NEAR, other groups of authors', each asking the like of the Script's cells; this library may not
hold them: `matTie_iff_at_head`; `K4CellsTie`, `K4IndexIs`.

WHAT IT READS. The index, through idx and weights. No run's coin, no challenge, no trace, no
request. Vd is spent as a guard alone: nothing is drawn from it.

Limits. An implication at letters. General in the Script, the layout, the readers and Vd; no thread,
no state, no head. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.CellsOfIndex
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsLay)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (CellsM)
open ProofFile.Honest.FirstThread

/-- **The kind's premise on the cells, at a Script whose cells are the matrix of the index.** It
trades; it pays nothing: see the head. -/
theorem k11CellsQ_at_matrix (Bk : ProverCoinCounts) (W₀ Rc Tr : Type)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (lay : WsLay) (weights : W₀ → Weights) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (idx : W₀ → Cm.Idx)
    (hQ : ∀ v, Vd v → Q.cells v = VerifiableInference.OnPublicFiles.Flat.matrixOf (idx v.w₀))
    (hw : ∀ (w : W₀) a b, algebraMap Cb.Gl.F Cb.Gl.E ((weights w).entry a b) =
      (((idx w).mat a b : ℤ) : Cb.Gl.E)) :
    K11CellsQ Q lay weights Vd :=
  cellsOfIndex Bk W₀ Rc Tr Q lay weights Vd fun v hv =>
    ⟨idx v.w₀, by
      rw [hQ v hv]
      exact VerifiableInference.OnPublicFiles.Flat.holds_matrixOf (idx v.w₀), hw v.w₀⟩

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.k11CellsQ_at_matrix
