-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/RowLengths.lean: THE MAKER's THREE ROWS OF PIECES ARE AS LONG AS THE CHAINS' LISTS OF BLOCKS. Book-keeping, general in the description: so that the boundary «0 + 1 + (the row's rest's length)» at which `RowsOwed` (KeyOfRows.lean) asks a seam is the number of the chain's blocks.
Main names. `cutRow_length` · `rowLen₁` | `rowLen₂` | `rowLen₃`: `(atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ …)).lⱼ.length = kⱼ.length`.
Nothing on soundness.

-/
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound

/-- The maker's row has a piece for each block. -/
theorem cutRow_length {C : CK} {Fr : Frame} {S Cl W : Type} (rest : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds) (putBack : List _root_.Fmt.RoundView) :
    ∀ (l : List (Block S Cl)) (i base : ℕ) (ds : List RDT) (b : Block S Cl), (cutRow rest putBack i base ds b l).2.length = l.length
  | [], _, _, _, _ => rfl
  | b' :: l, i, base, ds, b => by
    show ((cutRow rest putBack (i + 1) _ _ b' l).1 :: (cutRow rest putBack (i + 1) _ _ b' l).2).length = (b' :: l).length
    rw [List.length_cons, List.length_cons, cutRow_length rest putBack l]

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

theorem rowLen₁ : (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length = k₁.length := by
  show (cutRow rest₁ _ _ _ _ _ (k₁.map held)).2.length = _
  rw [cutRow_length, List.length_map]

theorem rowLen₂ : (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length = k₂.length := by
  show (cutRow rest₂ _ _ _ _ _ (k₂.map held)).2.length = _
  rw [cutRow_length, List.length_map]

theorem rowLen₃ : (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length = k₃.length := by
  show (cutRow rest₃ _ _ _ _ _ (k₃.map held)).2.length = _
  rw [cutRow_length, List.length_map]

end

end LPFD

#print axioms LPFD.cutRow_length
#print axioms LPFD.rowLen₁
#print axioms LPFD.rowLen₂
#print axioms LPFD.rowLen₃
