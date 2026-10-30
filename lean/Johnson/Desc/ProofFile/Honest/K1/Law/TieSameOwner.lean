-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieSameOwner.lean: hSame OF tieMatS_of_owners (TieMatOwners.lean): THE BORROWED MATRIX.
At a reader whose cells are the model's own trace, read by cellOf, at a served request, the packed cells of matrix number ν of
segment σ are those of its owner's matrix. OF COMPLETENESS's KIND: it names the input; NOT IN FRONT OF A LAW OVER COINS.

  packed_congr      two matrices of one shape whose cells agree have the same packed cells
  packed_of_owner   the statement


NO PROPERTY IS CLAIMED.
-/
import Johnson.HonestTrace.CellOfOwner
import Johnson.HonestTrace.Packed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes.HonestTrace

/-- Two matrices of one shape whose cells agree have the same packed cells. -/
theorem packed_congr {S : Sz} {cell : ℕ → String → ℕ → ℕ → Cb.Gl.F} {l l₀ ν ν₀ : ℕ} {σ σ₀ : Seg}
    {μ μ₀ : MatName} (hat : S.matAt l ν = some (σ, μ)) (hat₀ : S.matAt l₀ ν₀ = some (σ₀, μ₀))
    (hS : S.shape σ μ = S.shape σ₀ μ₀)
    (hc : ∀ r c, cell l μ.label r c = cell l₀ μ₀.label r c) (i c : ℕ) :
    packedCells S cell l ν i c = packedCells S cell l₀ ν₀ i c := by
  unfold packedCells
  rw [hat, hat₀]
  simp only [hS]
  split
  · congr 1
    funext r
    exact hc r c
  · rfl

/-- **The borrowed matrix.** -/
theorem packed_of_owner {X : OnBytes.Model.Verify.Public} {T : Tr} (N : PartsFit X) (B : BorrowedSame X T)
    {σ : Seg} (hσ : σ.Below 12) {ν ν₀ l₀ : ℕ} {μ : MatName}
    (hμ : (MatName.all 3 1 1 4 σ)[ν]? = some μ)
    (hat : Sz.ref.matAt (σ.no 12) ν = some (σ, μ))
    (hat₀ : Sz.ref.matAt l₀ ν₀ = some (Sz.ref.owner σ μ))
    (hl₀ : l₀ = (Sz.ref.owner σ μ).1.no 12)
    (hS : Sz.ref.shape σ μ = Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2) (i c : ℕ) :
    packedCells Sz.ref (cellOf X T) l₀ ν₀ i c = packedCells Sz.ref (cellOf X T) (σ.no 12) ν i c := by
  subst hl₀
  exact (packed_congr hat hat₀ hS (fun r c => cellOf_owner N B hσ hμ r c) i c).symm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.packed_congr
#print axioms ProofFile.Honest.K1.packed_of_owner
