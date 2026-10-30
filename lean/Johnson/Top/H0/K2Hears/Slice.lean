-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/Slice.lean: the code switch: the old group's symbols at a drawn
position, cut out of the array that the reading of the old rows gives.

The text of the code switch reads the old single rows at the list of the drawn positions by the
library's pure function OnBytes.singleRowsSymbols (OnBytes/Iop/Fold.lean): entry i * rows + j of its
result y is the symbol of row j (the folded main row; the kept rows by member and row; the old mask;
the fresh mask) at the i-th listed position.
  sliceAt        the rows' symbols at the position q, read in the field: nothing if q is not listed
  sliceAt_drawn  at every drawn position the slice is there
  slice_inside   and every entry that it reads lies inside y: no 0 is laid in for a missing symbol
                 (y's length: the library's singleRowsSymbols_inv, OnBytes/Iop/SymbolLaws.lean)
  longOf         the slice under a numbering coord of the typed open word's coordinates
PURE FUNCTIONS OF THE HAND-WRITTEN PROGRAM's FILES ARE NAMED HERE: Positions.ofDraws,
Positions.indexOf, singleRowsSymbols, SingleRows.rows; and the library's laws on them: indexOf_some,
ofDraws_index, singleRowsSymbols_inv. None runs in a context: a walk by constants through the proofs
meets no Blk, Ctx, Chan, SubM, LinkM, StateT, EStateM or IO.
Not here: that the text of the code switch calls the reading at these arguments; which coord the
typed block wants. No soundness is claimed.
-/
import OnBytes.Iop.SymbolReads
import OnBytes.Slice.BlkCsRead
import OnBytes.Slice.BaseYields
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hears
open OnBytes OnBytes.Slice

/-- The rows' symbols at the position q. -/
def sliceAt (rows : ℕ) (pos : Positions) (y : Array E) (q : ℕ) : Option (Fin rows → Cb.Gl.E) :=
  (pos.indexOf q).map fun i j => readE (y.getD (i * rows + j.val) zeroE)

/-- The slice under a numbering of the typed open word's coordinates. -/
def longOf {Aa : Type} (rows : ℕ) (coord : Aa → Fin rows) (pos : Positions) (y : Array E) (q : ℕ) :
    Option (Aa → Cb.Gl.E) :=
  (sliceAt rows pos y q).map fun σ α => σ (coord α)

/-- A drawn position is listed. -/
theorem drawn_listed (logN : ℕ) (draws : List ℕ) (q : ℕ) (hq : q ∈ draws) :
    q ∈ (Positions.ofDraws logN draws).all := by
  obtain ⟨k, hk, e⟩ := ofDraws_index logN draws q hq
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some] at e
  exact e ▸ Array.getElem_mem hk

/-- **At every drawn position the slice is there**, at an index below the list's length. -/
theorem sliceAt_drawn (rows logN : ℕ) (draws : List ℕ) (y : Array E) (q : ℕ) (hq : q ∈ draws) :
    ∃ i, (Positions.ofDraws logN draws).indexOf q = some i ∧
      i < (Positions.ofDraws logN draws).all.size ∧
      sliceAt rows (Positions.ofDraws logN draws) y q =
        some fun j => readE (y.getD (i * rows + j.val) zeroE) := by
  obtain ⟨i, hi, hlt, _⟩ := indexOf_some _ q (drawn_listed logN draws q hq)
  exact ⟨i, hi, hlt, by unfold sliceAt; rw [hi]; rfl⟩

/-- **Every entry that a slice reads lies inside the array.** -/
theorem slice_inside (s : SingleRows) (opened : Array (Array Column)) (n : ℕ) (y : Array E)
    (hm : s.masks ≤ 2) (h : singleRowsSymbols s opened n = some y) (i : ℕ) (hi : i < n)
    (j : Fin s.rows) : i * s.rows + j.val < y.size := by
  have hs : y.size = n * s.rows := (singleRowsSymbols_inv s opened n y hm h).2.2.1
  rw [hs]
  have := j.isLt
  calc i * s.rows + j.val < i * s.rows + s.rows := Nat.add_lt_add_left this _
    _ = (i + 1) * s.rows := (Nat.succ_mul _ _).symm
    _ ≤ n * s.rows := Nat.mul_le_mul_right _ hi

theorem longOf_drawn {Aa : Type} (rows : ℕ) (coord : Aa → Fin rows) (logN : ℕ) (draws : List ℕ)
    (y : Array E) (q : ℕ) (hq : q ∈ draws) :
    ∃ σ, longOf rows coord (Positions.ofDraws logN draws) y q = some σ := by
  obtain ⟨i, _, _, h⟩ := sliceAt_drawn rows logN draws y q hq
  exact ⟨_, by unfold longOf; rw [h]; rfl⟩

end VerifiableInference.Desc.First.K2Hears

#print axioms VerifiableInference.Desc.First.K2Hears.sliceAt_drawn
#print axioms VerifiableInference.Desc.First.K2Hears.slice_inside
#print axioms VerifiableInference.Desc.First.K2Hears.longOf_drawn
