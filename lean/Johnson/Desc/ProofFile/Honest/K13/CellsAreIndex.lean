-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CellsAreIndex.lean: kind K13, the members' batching: A PREMISE's
FORM, `CellsAreIndex`: AT EVERY ADMITTED INPUT THE SCRIPT's CELLS HOLD THE INPUT's INDEX, AND A
READER OF THE INDEX READS THAT INDEX; AND WHAT FOLLOWS FROM IT: THE SCRIPT's CELLS ARE THE READER's
MATRIX OF CELLS (`Bind.ForProver.cellsOfF`, Johnson/Bind/ForProver/CellsInField.lean), AND THAT
MATRIX IS IN RANGE. One definition of a proposition; three statements with their proofs. IT FIXES
WHAT THE SCRIPT's CELLS ARE AS A FUNCTION OF THE HIDDEN INDEX: OF COMPLETENESS's KIND:
NOT IN FRONT OF A LAW OVER COINS. NO PROPERTY IS CLAIMED. THE FULL SIZE ALONE.

Why. Three texts speak of one matrix: the Script's field `cells`
(Johnson/Desc/ProofFile/Honest/Thread/First.lean: "what the stored table commits to: meant to be
computed from the index alone"); the reader `Weights` (Johnson/Desc/ProofFile/Honest/ForKinds.lean),
which the library's encoder `encW` (Johnson/Bind/ForProver/Enc.lean) encodes; the index of the
library's type `Cm.Idx`. At the reader that is made of an index's own entries the library has a law
on the decoder of the committed table at `encW`'s columns: `column_decodes_at`
(Johnson/Bind/ForProver/JoinsSizes.lean), `column_decodes_inScope`
(Johnson/Bind/ForProver/InScope.lean): it ends at the index's matrix. Such a law at a free reader
would end at the reader's matrix of cells, and would ask that it be in range: no file of the library
has one yet. The last statement here would carry such an end to the Script's cells.

Main names.
  `CellsAreIndex Q Vd weights idx`: the premise's form. idx: which index an input holds. "The
    halves' reader" there is weights: it is meant for the reader of the index with which a prover's
    sides of the sub-protocols, its halves, are built.
  `holds_cellsOfF`: a reader over the base field that agrees with an index inside the shape: its
    matrix of cells holds that index. An index and a reader; no Script, no input.
  `cellsOfF_of_holds`: a matrix of the reference shape that holds the same index is that matrix of
    cells. No Script, no input.
  `cells_are_readers_matrix`: **under `CellsAreIndex`, at every input that Vd admits: Q.cells w is
    `cellsOfF` of the reader's entries, and that matrix is in range.**

Which clause is spent where. The first conjunct spends both clauses of `CellsAreIndex`. The second
conjunct names no Script: it follows from the second clause and from idx's type alone (an index's
matrix is 0 outside the shape: `Cm.ext_out`, Cm/IndexRefProofs.lean). Of the second clause the
entries inside the shape alone are spent.

Kin. The body of `CellsAreIndex` is the premise hI of `k13_matTie_of_index` (MatTieOfIndex.lean of
this folder), there at one input and under "there is an index", here at every admitted input and
with the index named: hX at that input gives hI. No theorem here joins them. The first clause alone,
with the index under "there is" and tied to nothing of w.w₀, is the library's `HoldsOwed`
(Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/AskedT.lean): `CellsAreIndex` gives it at Vd and
Q.cells; no theorem here says so. The same sentence, or a part of it, is asked under other names and
in other forms (with no Script; cell by cell, inside a layout) in files that are no part of the
library and are not imported. At the reader that is made of an index's own entries `holds_cellsOfF`
says what `Flat.holds_matrixOf` (Johnson/Flat/ThreeFull.lean) says at `cellsOfF_matrixOf`
(Johnson/Bind/ForProver/JoinsSizes.lean).

Limits. `CellsAreIndex` IS A PREMISE: THAT IT HOLDS OF ANY SCRIPT, READER AND INPUT IS NOT SHOWN
HERE. At Vd := fun _ => False it holds of itself, and the last statement says nothing. Where "the
Script's cells hold the index" is itself laid into Vd, the first clause is assumed of the input and
shown of nothing. At a Script whose cells are laid as the index's matrix the first clause is true by
construction, never paid; the second is a condition on weights, which no Script fixes: where weights
is the identity it is a condition on the prover's private input. Q, weights and idx are free
letters: no prover is named here, and nothing ties them to one; at an admitted input the first
clause fixes idx w.w₀ (`holds_unique`, Johnson/Flat/LedgerClaim.lean). The second clause binds every
row and column: with idx's type it says that the reader is 0 outside the shape, which the type of an
input does not give; the last statement's end says nothing there, and names no idx: it is weaker,
and there is no way back from it without "0 outside". An input holds pads, encoding randomness, an
instance and a trace beside the index w₀; by its type Q.cells could read them: `CellsAreIndex` and
the last statement say that at two admitted inputs with one w₀ the cells are one. Nothing outside
this file calls these statements.

What is not claimed. It is none of the library's goals. Nothing of what a prover stores, sends or
commits to; nothing of a committer, an extractor or what the verifier accepts. Nothing on soundness,
completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.P5J.LettersAt
import Johnson.Bind.ForProver.CellsInField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds InRange)
open OnBytes.Slice (frS frZ)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (CellsM)
open ProofFile.Honest.FirstThread (Script)
open Bind.ForProver (cellsOfF)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **A premise's form.** idx: which index an input holds. At every input that Vd admits: the
Script's cells hold that index, and the halves' reader reads that index. IT FIXES WHAT THE SCRIPT's
CELLS ARE AS A FUNCTION OF THE HIDDEN INDEX: OF COMPLETENESS's KIND:
NOT IN FRONT OF A LAW OVER COINS. At Vd := fun _ => False it holds of itself. Where "the Script's
cells hold the index" is laid where Vd stands, the first clause is assumed of the input, shown of
nothing. The Script Q and a prover are two letters: it ties neither to the other. At a Script whose
cells are laid as the index's matrix the first clause is true by construction, never paid; the
second is a condition on weights, which no Script fixes. -/
def CellsAreIndex
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (weights : W₀ → Weights) (idx : W₀ → Cm.Idx) : Prop :=
  ∀ w, Vd w →
    Holds (Q.cells w) (idx w.w₀) ∧
    ∀ a b, algebraMap Cb.Gl.F Cb.Gl.E ((weights w.w₀).entry a b) =
      (((idx w.w₀).mat a b : ℤ) : Cb.Gl.E)

/-- A reader over the base field that agrees with an index INSIDE THE SHAPE: its matrix of cells
holds that index, and so is in range. Two letters: an index, a reader. No other matrix, no Script,
no input, no coin. That there is such an index is a true condition on the reader. -/
theorem holds_cellsOfF {i : Cm.Idx} (e : ℕ → ℕ → Cb.Gl.F)
    (he : ∀ (y : Fin hRef) (c : Fin (2 ^ kRef)),
      algebraMap Cb.Gl.F Cb.Gl.E (e y.val c.val) = ((i.mat y.val c.val : ℤ) : Cb.Gl.E)) :
    Holds (cellsOfF frS frZ 402653181 numsRef e) i :=
  ⟨fun y c => he y c, fun _ _ h => Cm.ext_out i.val h⟩

/-- A matrix of the reference shape that holds the same index is the reader's matrix of cells. Three
letters: a matrix, an index, a reader. No Script, no input, no coin. -/
theorem cellsOfF_of_holds {M : Fin hRef → Fin (2 ^ kRef) → GE} {i : Cm.Idx} (e : ℕ → ℕ → Cb.Gl.F)
    (hM : Holds M i)
    (he : ∀ (y : Fin hRef) (c : Fin (2 ^ kRef)),
      algebraMap Cb.Gl.F Cb.Gl.E (e y.val c.val) = ((i.mat y.val c.val : ℤ) : Cb.Gl.E)) :
    M = cellsOfF frS frZ 402653181 numsRef e := by
  funext y c
  exact (hM.1 y c).trans (he y c).symm

variable {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
  {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {weights : W₀ → Weights} {idx : W₀ → Cm.Idx}

/-- hX IS A PREMISE. Under `CellsAreIndex`, at every input that Vd admits: the Script's cells are
the matrix of cells of the reader weights, and that matrix is in range. IT FIXES WHAT THE SCRIPT's
CELLS ARE AS A FUNCTION OF THE HIDDEN INDEX: OF COMPLETENESS's KIND:
NOT IN FRONT OF A LAW OVER COINS. The second conjunct names no Script: it follows from hX's second
clause and from idx's type alone, and is a condition on the private input. At a Script whose cells
are laid as the index's matrix hX's FIRST clause is true by construction, never paid; its second is
a condition on weights, which no Script fixes; where the reader too is laid as that index's casts,
both are true by construction. At Vd := fun _ => False it says nothing. weights is a free letter:
that any prover's halves read it is said nowhere here. -/
theorem cells_are_readers_matrix (hX : CellsAreIndex Q Vd weights idx)
    (w : Local W₀ Rc ProofFile.Inst Tr) (hV : Vd w) :
    Q.cells w = cellsOfF frS frZ 402653181 numsRef (weights w.w₀).entry ∧
      InRange (cellsOfF frS frZ 402653181 numsRef (weights w.w₀).entry) :=
  have he : ∀ (y : Fin hRef) (c : Fin (2 ^ kRef)),
      algebraMap Cb.Gl.F Cb.Gl.E ((weights w.w₀).entry y.val c.val) =
        (((idx w.w₀).mat y.val c.val : ℤ) : Cb.Gl.E) :=
    fun y c => (hX w hV).2 y.val c.val
  ⟨cellsOfF_of_holds _ (hX w hV).1 he, idx w.w₀, holds_cellsOfF _ he⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.CellsAreIndex
#print axioms ProofFile.Honest.K13.holds_cellsOfF
#print axioms ProofFile.Honest.K13.cellsOfF_of_holds
#print axioms ProofFile.Honest.K13.cells_are_readers_matrix
