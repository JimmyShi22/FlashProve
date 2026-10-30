-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndPort.lean: the world that the committed entries give at a state of the
verifier (`portWorld`, OnBytes/Tie/Pv/Led/LedPort.lean) reads the virtual rows that the ties and the
reads of the smallness test use as combinations of the committed cells.

Theorems with their proofs.

Main names:
  `RowsBelow Y F t`: every cell of array t that the lay has lies in a row below the number of rows
    that the state holds for the array.
  `portWorld_row`: there an entry of a virtual row of array t is the sum over the array's rows of
    the row's weight times the committed cell (`ReadsRow`, OnBytes/Tie/Pv/Tail/EndRaw.lean).
  `portWorld_reads`: so at the rows that the ties and the reads use (`ReadsRaw`).
  `rawRows_port`: the four equations (`RawRows`, OnBytes/Tie/Pv/Tail/EndAll.lean) in that world,
    from a run of the verifier's own test of the weights on a view.

Limits: that the lay's cells lie below the arrays' numbers of rows is a premise.


-/
import OnBytes.Tie.Pv.Led.LedLay
import OnBytes.Tie.Pv.Led.LedPort
import OnBytes.Tie.Pv.Tail.EndRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J)

/-- Every cell of array t that the lay has lies in a row below the array's number of rows. -/
def RowsBelow (F : Fork) (t : Nat) : Prop :=
  ∀ k r col, Y.addr k = .cell t r col → r < (F.trees.getD t {}).R

/-- Inside an array the default does not matter. -/
theorem getD_in {α : Type} (a : Array α) (i : Nat) (d d' : α) (h : i < a.size) :
    a.getD i d = a.getD i d' := by
  simp [Array.getD, h]

/-- Outside an array the default is returned. -/
theorem getD_out {α : Type} (a : Array α) (i : Nat) (d : α) (h : ¬ i < a.size) :
    a.getD i d = d := by
  simp [Array.getD, h]

/-- The weights of a virtual row, whichever value stands for an array or a row that is not there. -/
theorem rowWeight_eq (trees : Array HTree) (t r i : Nat) :
    rowWeight ρ trees t r i = ρ.val (((trees.getD t {}).rows.getD r {}).coef.getD i zeroE) := by
  unfold rowWeight
  have e1 : (trees.getD t default).rows = (trees.getD t {}).rows := by
    by_cases ht : t < trees.size
    · rw [getD_in trees t default {} ht]
    · rw [getD_out trees t default ht, getD_out trees t {} ht]
      rfl
  rw [e1]
  generalize (trees.getD t {}).rows = rows
  by_cases hr : r < rows.size
  · rw [getD_in rows r default {} hr]
  · rw [getD_out rows r default hr, getD_out rows r {} hr]
    rfl

/-- An entry of a virtual row, in the world of the committed entries. -/
theorem portWorld_row (F : Fork) (m : J → K) (t r : Nat) (h : RowsBelow Y F t) :
    ReadsRow ρ F (portWorld ρ Y F m) (fun t R i => Y.cellAt m t R i) t r := by
  intro i
  rw [portWorld_entry, Y.entryAt_sum m t _ i (F.trees.getD t {}).R fun k r' hk => h k r' i hk]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [rowWeight_eq]

/-- So at the virtual rows that the ties and the reads use. -/
theorem portWorld_reads (tl : HTailF2) (funs : Array HFun) (F : Fork) (m : J → K)
    (hZ : RowsBelow Y F tl.ix.ZZ) (hS : ∀ mu, mu < tl.NM → RowsBelow Y F (tl.gtTree.getD mu 0))
    (hT : ∀ x ∈ readsList tl funs, RowsBelow Y F (uOf tl x.1)) :
    ReadsRaw ρ tl funs F (portWorld ρ Y F m) (fun t R i => Y.cellAt m t R i) :=
  ⟨portWorld_row ρ Y F m _ _ hZ, portWorld_row ρ Y F m _ _ hZ,
    fun mu hmu => portWorld_row ρ Y F m _ _ (hS mu hmu),
    fun x hx => portWorld_row ρ Y F m _ _ (hT x hx)⟩

/-- The four equations in the world of the committed entries. -/
theorem rawRows_port (tl : HTailF2) (F F' G : Fork) (c c' : Ctx) (funs : Array HFun) (m : J → K)
    (hd : c.ch.dry = false) (h : tl.tileSelfTestF F c = .ok (((), F'), c'))
    (hrows : (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2)
    (hU : ∀ x ∈ readsList tl funs, UnitRow F (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU G (uOf tl x.1))
    (hZ : RowsBelow Y F tl.ix.ZZ) (hS : ∀ mu, mu < tl.NM → RowsBelow Y F (tl.gtTree.getD mu 0))
    (hT : ∀ x ∈ readsList tl funs, RowsBelow Y F (uOf tl x.1)) :
    RawRows (portWorld ρ Y F m) tl G funs (ρ.val F.theta) (fun t R i => Y.cellAt m t R i) :=
  rawRows_run ρ tl F F' G c c' funs _ _ (portWorld_reads ρ Y tl funs F m hZ hS hT) hd h hrows hU

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.portWorld_row
#print axioms OnBytes.Tie.Pv.Tail.rawRows_port
