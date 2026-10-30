-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Clamp/CellAgree.lean: two tables that agree at the entries which the request's
layout reads give the open segment the same cells and the same mask entries. Statements and proofs;
no definition.

What it pays. A law that needs "two pinned witnesses have one table" stands at a reader of the
witness that is clamped to each oracle message's own ranges; the composed meaning states its
sentences on linear forms at the reader that is not clamped. Two readers that give the open segment
the same cells, and the same mask entries, give these sentences one truth value. This file brings
that agreement down to single entries of the tables: a cell is a sum over the entries J of a main
table, each weighted by `inBlock`; where the weight is 0 the entry is not read.

  `cellOfBlock_agree`  one block's cell: two tables that agree wherever `inBlock` is not 0
  `dataOf_cell_agree`  the cells of `K9L.dataOf` (Johnson/Desc/First/Batch/Law/AsRow.lean)
  `dataOf_mask_agree`  its mask entry j
  `dataQ_cell_agree`, `dataQ_mask_agree`: the two at `dataQ` (Johnson/Desc/Sound/FormsQ.lean): at
                       the segment's own rows, frame and statement, and `tabQ` at two readers
Limits. Nothing says that two given readers agree at these entries. Nothing on soundness.

-/
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock)

/-- One block's cell reads a table only where `inBlock` is not 0. -/
theorem cellOfBlock_agree {K : Type} [CommRing K] (b : LaidBlock) (R P : ℕ) (tab tab' : ℕ → K)
    (h : ∀ J, J < 2 ^ (R + P) → (K9L.inBlock b R P J : K) ≠ 0 → tab' J = tab J) (i c : ℕ) :
    K9L.cellOfBlock b R P tab' i c = K9L.cellOfBlock b R P tab i c := by
  unfold K9L.cellOfBlock
  refine Finset.sum_congr rfl fun J hJ => ?_
  by_cases h0 : (K9L.inBlock b R P J : K) = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [h J (Finset.mem_range.1 hJ) h0]

/-- **The cells.** -/
theorem dataOf_cell_agree {K : Type} [CommRing K] (Rr : ReqRows) (f : ReqFrame) (S : Statement)
    (tab tab' : ℕ → OnBytes.Part → ℕ → K)
    (h : ∀ born name A o b J, reqArray Rr.layout born name = some A →
      f.whereIs born A.message = some o → b ∈ A.blocks →
      J < 2 ^ (S.rowBits o .main + S.placeBits o .main) →
      (K9L.inBlock b (S.rowBits o .main) (S.placeBits o .main) J : K) ≠ 0 →
      tab' o .main J = tab o .main J) :
    (K9L.dataOf Rr f S tab').cell = (K9L.dataOf Rr f S tab).cell := by
  funext born name i c
  unfold K9L.dataOf
  dsimp only
  cases e1 : reqArray Rr.layout born name with
  | none => rfl
  | some A =>
    dsimp only
    cases e2 : f.whereIs born A.message with
    | none => rfl
    | some o =>
      dsimp only
      congr 1
      refine List.map_congr_left fun b hb => ?_
      exact cellOfBlock_agree b _ _ _ _ (fun J hJ h0 => h born name A o b J e1 e2 hb hJ h0) i c

/-- **A mask entry.** -/
theorem dataOf_mask_agree {K : Type} [CommRing K] (Rr : ReqRows) (f : ReqFrame) (S : Statement)
    (tab tab' : ℕ → OnBytes.Part → ℕ → K) (j : ℕ)
    (h : ∀ o, K9L.maskOracle f = some o → tab' o .mask j = tab o .mask j) :
    (K9L.dataOf Rr f S tab').mask j = (K9L.dataOf Rr f S tab).mask j := by
  unfold K9L.dataOf
  dsimp only
  cases e : K9L.maskOracle f with
  | none => rfl
  | some o => exact h o e

/-- The cells, at the segment's own data and two readers of the witness. -/
theorem dataQ_cell_agree (own : List (ℕ × ℕ)) (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ born name A o b J, reqArray a.L.check.rows.layout born name = some A →
      a.L.check.frame.whereIs born A.message = some o → b ∈ A.blocks →
      J < 2 ^ (a.d.st.rowBits o .main + a.d.st.placeBits o .main) →
      (K9L.inBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) J : GQ) ≠ 0 →
      tabQ own a.d.st a.d.book rd' o .main J = tabQ own a.d.st a.d.book rd o .main J) :
    (dataQ own a rd').cell = (dataQ own a rd).cell :=
  dataOf_cell_agree a.L.check.rows a.L.check.frame a.d.st _ _ h

/-- A mask entry, at the same. -/
theorem dataQ_mask_agree (own : List (ℕ × ℕ)) (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ) (j : ℕ)
    (h : ∀ o, K9L.maskOracle a.L.check.frame = some o →
      tabQ own a.d.st a.d.book rd' o .mask j = tabQ own a.d.st a.d.book rd o .mask j) :
    (dataQ own a rd').mask j = (dataQ own a rd).mask j :=
  dataOf_mask_agree a.L.check.rows a.L.check.frame a.d.st _ _ j h

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.cellOfBlock_agree
#print axioms VerifiableInference.Desc.Sound.dataOf_cell_agree
#print axioms VerifiableInference.Desc.Sound.dataOf_mask_agree
#print axioms VerifiableInference.Desc.Sound.dataQ_cell_agree
#print axioms VerifiableInference.Desc.Sound.dataQ_mask_agree
