-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsSeat.lean: where the oracle messages of a code switch are in the book of trees.

In the first round of a code switch the prover sends the new oracle message, and perhaps others with
it, under one root. A later block reads them by the book of trees. This file shows that after a run
of the switch (OnBytes/Slice/BlkCsRun.lean: `CsRan`) these oracle messages are the parts of one
tree, in the order of sending, and which number that tree has (OnBytes/Slice/BlkSeat.lean: `Seat`).

Main theorems: `CsRan.seatB`, `CsRan.seat`, from `seat_of_sent` (OnBytes/Slice/BlkSentSeat.lean).
What is asked: the program has put all these oracle messages in one tree, part number i for the
i-th of them, and the tree's shape lists their symbols. These are facts on the function that places
trees, at given codes and shapes; they are not shown here.
Not claimed. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsKeeps

set_option autoImplicit false

namespace OnBytes.Slice

section
variable {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- The oracle messages of a switch are the parts of one tree, before the old rows are read.
sh: the tree's shape. The tree's number is that of the chain's first tree plus the number of roots
received before the switch. The hypotheses are those named in the file's head. -/
theorem CsRan.seatB (h : CsRan old T gp others c c' out row lay theta D) (sh : TreeShape)
    (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (sentOf T others).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray) :
    Seat D.cB ((List.range (sentOf T others).size).map (· + c.st.oracles.size))
      (c.ch.firstTree + c.ch.roots) sh.logN ((sentOf T others).toList.map (·.shape)) :=
  seat_of_sent c D.cB (sentOf T others) D.lay sh h.places h.bookB
    (fun i => by
      rw [h.stB]
      unfold CsTaken.stA
      rw [admitted_shape]) h1 ht hmain hmask

/-- The same after the run. -/
theorem CsRan.seat (h : CsRan old T gp others c c' out row lay theta D) (sh : TreeShape)
    (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (sentOf T others).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray) :
    Seat c' ((List.range (sentOf T others).size).map (· + c.st.oracles.size))
      (c.ch.firstTree + c.ch.roots) sh.logN ((sentOf T others).toList.map (·.shape)) := by
  refine (h.seatB sh h1 ht hmain hmask).keeps ?_ (shapesKeep_of_map _ _ fun i => ?_)
  · rw [h.book]
    exact (singleRowsRead_keeps old _ D.y D.cB D.cC h.dryB h.read).book
  · rw [h.shape_at i, h.stB]
    unfold CsTaken.stA
    rw [admitted_shape]

end

end OnBytes.Slice

#print axioms OnBytes.Slice.CsRan.seatB
#print axioms OnBytes.Slice.CsRan.seat
