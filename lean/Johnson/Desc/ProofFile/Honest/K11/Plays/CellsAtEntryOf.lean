-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/CellsAtEntryOf.lean: WHAT THE KIND K11 ASKS OF THE SCRIPT's
CELLS (`K11CellsQ`, TiesAtHeadStatement.lean of this folder) AT THE READER OF THE INDEX
`OnBytes.HonestTrace.entryOf` (Johnson/HonestTrace/IndexReaders.lean): THERE ONE PREMISE IS LEFT:
THAT THE SCRIPT's CELLS ARE, AT EACH VALID INPUT, THE MATRIX OF THE INPUT's INDEX. Two lemmas with
their proofs; no definition; none of the library's goals.

  `entryOf_is_mat`
      an identity of casts: the reader's entry, carried into the extension field, is the index's
      matrix's entry cast there. The index stands under "for all", the same on both sides; no
      run's letter
  `k11CellsQ_at_entryOf`
      `k11CellsQ_at_matrix` (CellsAtMatrix.lean of this folder) at W₀ := Cm.Idx, idx := id,
      weights := fun i => ⟨entryOf i⟩, its clause hw paid by the first

IT PAYS NOTHING OF A SCRIPT. hQ stays: a laying, the frame's authors'; shown of no Script. The first
lemma is true by the two readers' texts (entryZ i r c := i.mat r c; entryOf its cast into the base
field): TRUE BY CONSTRUCTION. A premise on the index's own values, of
completeness's kind: never to be laid in front of a law over coins.

NEAR, another group of authors'; this library may not hold them: the same identity, by the same
`map_intCast`, at the reader to which ⟨entryOf i⟩ unfolds: `indexIsAt_residues`, `indexIsAt_member`
(Honest/K4/Law/IndexIsAt.lean), `indexIs_residues`, `indexIs_entries`
(Honest/K4/Law/IndexIsOf.lean); `holds_casts` (the same file) is the like of `Flat.holds_matrixOf`
at the full size's own spelling of the shape. `K4IndexIs` at one input is the premise of
`cellsOfIndex` (CellsOfIndex.lean of this folder) there: `k11CellsQ_of_k4IndexIs`
(CellsOfK4Index.lean of this folder).

WHY THIS READER. At the reader that L25's one term fullIn lays, by L25's word; no program runs that
filling. By that word fullIn's field is weights := fun _ i => ⟨entryOf i⟩; the term is not named in
the statements.

Limits. An implication at letters. General in the Script, the layout and Vd; no thread, no state, no
head. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.CellsAtMatrix
import Johnson.HonestTrace.IndexReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsLay)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (CellsM)
open ProofFile.Honest.FirstThread

/-- **The reader's entry in the extension field is the index's matrix's entry there.** -/
theorem entryOf_is_mat (i : Cm.Idx) (a b : ℕ) :
    algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.HonestTrace.entryOf i a b) = ((i.mat a b : ℤ) : Cb.Gl.E) :=
  map_intCast (algebraMap Cb.Gl.F Cb.Gl.E) (i.mat a b)

/-- **The kind's premise on the cells at that reader: one premise is left.** It trades; it pays
nothing of a Script: see the head. -/
theorem k11CellsQ_at_entryOf (Bk : ProverCoinCounts) (Rc Tr : Type)
    (Q : Script Bk (Local Cm.Idx Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (lay : WsLay) (Vd : Local Cm.Idx Rc ProofFile.Inst Tr → Prop)
    (hQ : ∀ v, Vd v → Q.cells v = VerifiableInference.OnPublicFiles.Flat.matrixOf v.w₀) :
    K11CellsQ Q lay (fun i => ⟨OnBytes.HonestTrace.entryOf i⟩) Vd :=
  k11CellsQ_at_matrix Bk Cm.Idx Rc Tr Q lay (fun i => ⟨OnBytes.HonestTrace.entryOf i⟩) Vd id hQ
    entryOf_is_mat

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.entryOf_is_mat
#print axioms ProofFile.Honest.K11.k11CellsQ_at_entryOf
