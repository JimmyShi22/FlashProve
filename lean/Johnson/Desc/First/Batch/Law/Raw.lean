-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Raw.lean
(kind K9's soundness lemma): THEOREMS: THE WORLD IN WHICH K9's LEMMA IS STATED READS
EVERY VIRTUAL ROW AS THE LIBRARY's ReadsRow SAYS (OnBytes/Tie/Pv/Tail/EndRaw.lean): an entry of a
virtual row is the sum of its array's entries under the row weights that the ledger holds.
  cellsOf            the arrays' entries, by the array's number in the ledger's list: the bound
                     data's cells at the link and the name that the segment's list gives the number.
  worldAt_readsRow   ReadsRow at worldAt (Law/Measure.lean), AT EVERY ARRAY AND EVERY VIRTUAL ROW.
  worldAt_readsRaw   so the library's ReadsRaw, at every tail and every list of functions.
  worldAt_entry_of_frame   two ledgers with the same treesFrame give the same entries: so it is
                     carried past the adding of claims (Law/Ledger.lean: addAll_total keeps
                     treesFrame).
No premise. These are sentences on a definition of ours (worldAt): they say that it is the world
that the library's laws on raw rows ask for; nothing on what the commitments hold the prover to.

-/
import OnBytes.Tie.Pv.Tail.EndRaw
import Johnson.Desc.First.Batch.Law.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail (ReadsRow ReadsRaw)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The arrays' entries by the array's number in the ledger's list. At a number that the segment's
list does not name, the cells of the array "" of link 0 are read: shut out where the equation is
made, by its tests "K9.arrays-named" and "K9.arrays-there" (Batch/Text.lean). -/
def cellsOf (L : LinkCtx) (D : Bound K) : Nat → Nat → Nat → K := fun t R i =>
  D.cell (L.arrayOf.getD t (0, "")).1 (L.arrayOf.getD t (0, "")).2 R i

theorem frame_R (trees : Array HTree) (t : Nat) :
    ((treesFrame trees).getD t default).1.R = (trees.getD t {}).R := by
  cases h : trees[t]? with
  | none =>
    simp [treesFrame, Array.getD_eq_getD_getElem?, h]
    rfl
  | some X => simp [treesFrame, Array.getD_eq_getD_getElem?, h, HTree.frame]

theorem frame_coef (trees : Array HTree) (t r : Nat) :
    (((treesFrame trees).getD t default).2.getD r default).1.coef =
      ((trees.getD t {}).rows.getD r {}).coef := by
  cases h : trees[t]? with
  | none =>
    simp [treesFrame, Array.getD_eq_getD_getElem?, h]
    rfl
  | some X =>
    cases h' : X.rows[r]? with
    | none =>
      simp [treesFrame, Array.getD_eq_getD_getElem?, h, h', HTree.frame]
      rfl
    | some R => simp [treesFrame, Array.getD_eq_getD_getElem?, h, h', HTree.frame, HRow.frame]

/-- **The lemma's world reads every virtual row as a sum of its array's entries.** -/
theorem worldAt_readsRow (L : LinkCtx) (F : Fork) (D : Bound K) (t r : Nat) :
    ReadsRow ρ F (worldAt ρ L F D) (cellsOf L D) t r := by
  intro i
  show entryAt ρ L.arrayOf (treesFrame F.trees) D t r i = _
  unfold entryAt
  rw [frame_R, frame_coef]
  rfl

/-- **So it is at the rows that the ties and the reads use.** -/
theorem worldAt_readsRaw (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (F : Fork)
    (D : Bound K) : ReadsRaw ρ tl funs F (worldAt ρ L F D) (cellsOf L D) :=
  ⟨worldAt_readsRow ρ L F D _ _, worldAt_readsRow ρ L F D _ _,
    fun _ _ => worldAt_readsRow ρ L F D _ _, fun _ _ => worldAt_readsRow ρ L F D _ _⟩

/-- Two ledgers with the same frame of arrays give the same entries. -/
theorem worldAt_entry_of_frame (L : LinkCtx) (F G : Fork) (D : Bound K)
    (h : treesFrame G.trees = treesFrame F.trees) :
    (worldAt ρ L G D).entry = (worldAt ρ L F D).entry := by
  show entryAt ρ L.arrayOf (treesFrame G.trees) D = entryAt ρ L.arrayOf (treesFrame F.trees) D
  rw [h]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.worldAt_readsRow
#print axioms VerifiableInference.Desc.K9L.worldAt_readsRaw
#print axioms VerifiableInference.Desc.K9L.worldAt_entry_of_frame
