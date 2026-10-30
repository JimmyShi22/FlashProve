-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CellsOfData.lean: THE OUTPUT HEAD'S INTEGER CELLS AS A FUNCTION OF THE DATA
THAT THE TABLE'S FORMS READ, and the tie to the components that the head's own law reads off the
witness (Law/K6Cut.lean: compCut), UNDER ONE PREMISE ON SYMBOLS.

The forms' files and the head's law read the same committed messages. The forms' files read DATA:
a field element for each element of each named array (AsRow.lean: Bound, dataOf). The head's law
reads INTEGER CELLS: the small integers whose packing the symbols of segment 24's matrices are
(Johnson/Goal/Meaning/HidOwn.lean: ownOf), cut to the four ranges of the head's cells. The arrays
hold these very symbols. Here the second reading is made of the first.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came).
  symD Wp s D k: the symbols of sub-proof k's matrices, read in the data: row of symbols r and
      column c of the matrix mu is element (r, c) of the array that the matrix's label names
      (other files' ownerK, ownerA, nameOf, labAt).
  cellsOfData Wp s D: the head's cells made of these symbols as compCut makes them of the witness's:
      ownOf, the cut, the library's cellsH. ITS WEIGHTS ARE 0: no user reads them.
  cut_congr: two families of symbols that agree in every column of the four ranges give the same cut
      list (the library's cellsOf_congr, column by column).
  comp_of_syms: SO: if in every column of the four ranges the data's element IS the symbol that
      compCut reads (hsym), then compCut's cells and stream are cellsOfData's.

Every letter under "there is": none.
What it does not say. hsym: THAT THE DATA'S ELEMENT IS THAT SYMBOL: it wants: that a cell of dataOf,
a sum over the layout's blocks, is the one table entry at the place where the layout lays the
element (typed by nobody); that the seat of the symbol is that place; that the tenant which segment
24's group holds under the message's number is the seat at which the forms' accessor reads it.
Nothing on the mask row. Nothing on soundness.
-/
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Desc.First.Batch.Law.AsRow
import Johnson.Desc.Kinds.Law.K6Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Road (Mats)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)
open VerifiableInference.Desc.K9L (Bound)

/-- **The symbols of sub-proof k's matrices, read in the data.** -/
def symD (Wp : OnBytes.Model.Verify.Public) (s : Nat → Cb.Pv.Tail.Size) (D : Bound Cb.Gl.E)
    (k : Nat) : Cb.Pv.Tail.Syms Cb.Gl.E (s k) :=
  fun μ r c => D.cell (Meaning.ownerK (Meaning.labAt Wp k μ.val))
    (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp k μ.val))) r.val c.val

/-- **The head's cells, made of the data.** -/
def cellsOfData (Wp : OnBytes.Model.Verify.Public) (s : Nat → Cb.Pv.Tail.Size)
    (D : Bound Cb.Gl.E) : NCells :=
  cellsBack (OnBytes.Road.Hd.cellsH Wp.hS Wp.HLy (borderOf Wp.y)
    (cutM Wp.hS Wp.HLy (borderOf Wp.y) (Meaning.ownOf s (symD Wp s D) 24))) fun _ _ => 0

namespace Came

/-- **The same symbols in the columns of the four ranges: the same cut list.** -/
theorem cut_congr (Wp : OnBytes.Model.Verify.Public) (s : Nat → Cb.Pv.Tail.Size)
    (y y' : ∀ k, Cb.Pv.Tail.Syms Cb.Gl.E (s k))
    (h : ∀ (μ : Fin (s 24).NM) (r : Fin (Alg.symRows ((s 24).m μ))) (c : Fin ((s 24).k μ)),
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c.val → y 24 μ r c = y' 24 μ r c) :
    cutM Wp.hS Wp.HLy (borderOf Wp.y) (Meaning.ownOf s y 24) =
      cutM Wp.hS Wp.HLy (borderOf Wp.y) (Meaning.ownOf s y' 24) := by
  funext a r c
  unfold cutM
  by_cases hin : InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c
  · rw [if_pos hin, if_pos hin]
    unfold Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
    by_cases h1 : a < (s 24).NM
    · rw [dif_pos h1, dif_pos h1]
      by_cases h2 : c < (s 24).k (⟨a, h1⟩ : Fin (s 24).NM)
      · rw [dif_pos h2, dif_pos h2]
        by_cases h3 : r < (s 24).m (⟨a, h1⟩ : Fin (s 24).NM)
        · rw [dif_pos h3, dif_pos h3]
          refine congrFun (Cb.Pv.Tail.cellsOf_congr (Λ := Cb.Pv.Tail.symL Cb.Gl.E (s 24))
            (μ := ⟨a, h1⟩) (c := ⟨c, h2⟩) fun i' => ?_) ⟨r, h3⟩
          exact h ⟨a, h1⟩ i' ⟨c, h2⟩ (colFour_of_in hin)
        · rw [dif_neg h3, dif_neg h3]
      · rw [dif_neg h2, dif_neg h2]
    · rw [dif_neg h1, dif_neg h1]
  · rw [if_neg hin, if_neg hin]

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **compCut's cells and stream are the data's**, where the data's elements are the symbols. -/
theorem comp_of_syms (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (D : Bound Cb.Gl.E)
    (hsym : ∀ (μ : Fin (s 24).NM) (r c : Nat), r < Alg.symRows ((s 24).m μ) → c < (s 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      Sound.readAt cs arr msR N 24 w (seat 24 μ r c).1 false (seat 24 μ r c).2.1
          (seat 24 μ r c).2.2 =
        D.cell (Meaning.ownerK (Meaning.labAt Wp 24 μ.val))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 μ.val))) r c) :
    (compCut cs arr msR N s seat Wp pl w).1.cell = (cellsOfData Wp s D).cell ∧
      (compCut cs arr msR N s seat Wp pl w).1.stream = (cellsOfData Wp s D).stream := by
  have e : ownCut cs arr msR N s seat Wp w =
      cutM Wp.hS Wp.HLy (borderOf Wp.y) (Meaning.ownOf s (symD Wp s D) 24) :=
    cut_congr Wp s _ _ fun μ r c hc => hsym μ r.val c.val r.isLt c.isLt hc
  unfold compCut compOf cellsOfData
  rw [e]
  exact ⟨rfl, rfl⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.cut_congr
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.comp_of_syms
