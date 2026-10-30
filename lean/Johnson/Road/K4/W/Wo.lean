-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Wo.lean: CONDITIONAL.

Not shown here. THE EQUATION ON THE END VALUE (hv) IS A PREMISE: that an honest run's end value
meets it is not shown. That wsPending returns, and what the merge leaves of its claims (ho), are
premises. rowOf is the row's text as row_tie (Johnson/Top/H0/MergeLaw/WoRow.lean) gives it: THAT
THE READER OF A CHAIN's STATE GIVES THIS ROW AT THIS ENTRY IS NOT SHOWN HERE. The witness is any
one that meets four conditions. No example is known. No property is claimed.

THE PENDING ROW ON THE COMMITTED MATRIX OF WEIGHTS, WHICH THE MERGE OF THE SUB-PROTOCOL K4 LEAVES,
HOLDS: where the merge's shown end value is its function at the merge's point plus the factor times
one entry of the index masks. Calls of three laws that stand: pending_port
(Johnson/Road/Rows/PendingPort.lean), stretchMeans (Johnson/Road/Rows/StretchLaws.lean),
rowSays_iff_holds (Johnson/Top/H0/MergeLaw/RowHolds.lean).

  rowOf      the row made of what wsPending returns, at entry c of the mask rows of message nm.
  wo_says    it holds of the matrix and the entries, said plainly (RowSays).
  wo_holds   it holds in the sense of Johnson/Desc/K13/Law/Means.lean.
-/
import Johnson.Top.H0.MergeLaw.RowHolds
import Johnson.Road.Rows.StretchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.W
open OnBytes (E TensorRow mulE)
open OnBytes.Model (Reading WsLay WsClaim WsForkOut WsPending wsPending wsRowPart wsEpsT)
open OnBytes.Road (Wm fmAt gl_numerals)
open OnBytes.Road.Rows (pending_port stretchMeans)
open VerifiableInference.Desc.First.MergeLaw (RowSays rowSays_iff_holds)
open VerifiableInference.Desc.K13.Law (Wit Holds lowBits)

/-- The row made of what wsPending returns, at entry c of the mask rows of message nm. -/
def rowOf (w : WsPending) (nm c : ℕ) : TensorRow :=
  { g := w.g, psi := w.psi, masks := [(⟨nm, c⟩, w.beta)], target := w.target }

/-- **The pending row holds, said plainly.** M: the committed matrix; idx: the index masks'
entries; cr: the merge's claims with their coefficients. -/
theorem wo_says (lay : WsLay) (M : Wm Cb.Gl.E) (o : WsForkOut) (claims : ℕ)
    (S : OnBytes.Params.LinShape) (cr : List (WsClaim × E))
    (ho : o.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    {w : WsPending} (h : wsPending lay o claims S = .ok w) (idx : ℕ → Cb.Gl.E) (nm c : ℕ)
    (hv : Reading.gl.val o.fvp =
      fmAt Reading.gl lay M cr o.rm + idx c * Reading.gl.val o.beta) :
    RowSays lay.lk S.kRow M idx (rowOf w nm c) := by
  obtain ⟨e1, e2, e3, e4⟩ := pending_port gl_numerals (stretchMeans _) lay M o claims S cr ho h
  have ep : (rowOf w nm c).psi.reverse.toArray = o.rm := by
    show w.psi.reverse.toArray = o.rm
    rw [e1, List.reverse_reverse, Array.toArray_toList]
  unfold RowSays
  rw [ep]
  show _ + ([((⟨nm, c⟩ : OnBytes.Slot), w.beta)].map fun x =>
    idx x.1.index * Reading.gl.val x.2).sum = Reading.gl.val w.target
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, e2, e3, hv]
  exact congrArg (· + _) e4

/-- **The pending row holds**, at a witness whose matrix is M and whose mask entry at the row's name
is the index masks' entry. -/
theorem wo_holds (lay : WsLay) (M : Wm Cb.Gl.E) (o : WsForkOut) (claims : ℕ)
    (S : OnBytes.Params.LinShape) (cr : List (WsClaim × E))
    (ho : o.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    {w : WsPending} (h : wsPending lay o claims S = .ok w) (idx : ℕ → Cb.Gl.E) (nm c : ℕ)
    (hv : Reading.gl.val o.fvp =
      fmAt Reading.gl lay M cr o.rm + idx c * Reading.gl.val o.beta)
    {nR : ℕ} (wit : Wit Cb.Gl.E nR lay.lk) (hrm : o.rm.size = lay.lk) (hn : nR ≤ 2 ^ S.kRow)
    (hzero : ∀ j, nR ≤ j → ∀ C, M j C = 0)
    (hmat : ∀ (i : Fin nR) (C : ℕ), C < 2 ^ lay.lk → wit.mat i (lowBits lay.lk C) = M i C)
    (hmask : wit.mask ⟨nm, c⟩ = idx c) :
    Holds Reading.gl wit (rowOf w nm c) := by
  obtain ⟨e1, -, -, -⟩ := pending_port gl_numerals (stretchMeans _) lay M o claims S cr ho h
  refine (rowSays_iff_holds M idx (rowOf w nm c) wit ?_ hn hzero hmat ?_).1
    (wo_says lay M o claims S cr ho h idx nm c hv)
  · show w.psi.length = lay.lk
    rw [e1, List.length_reverse, Array.length_toList, hrm]
  · intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact hmask

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.wo_says
#print axioms OnBytes.Road.K4.W.wo_holds
