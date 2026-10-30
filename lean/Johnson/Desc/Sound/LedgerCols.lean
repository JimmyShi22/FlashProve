-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LedgerCols.lean: WHAT THE ACTING PARTS AT TWO NEIGHBOURING BORDERS OF A PROOF
FILE's SHARED CHAIN SHOW OF A TREE THAT WAS SENT IN FRONT OF THE BLOCK BETWEEN THEM: THE SAME
COLUMNS. It pays, from four comparisons of numbers, the premise hcol under which a pin, a promise of
"no collision" and "every leaf is shown" ride past a block at the ledger
(Johnson/Desc/K14/Law/LedgerPins.lean). No kind is named.

  actCol_eq       inside its range (from lo to below the border's top) an acting part's value shows
                  a tree's column as the oracles have it.
  actCell_eq      and the stored table's cells.
  cols_stay       **the columns stay**: for a tree j with lo ≤ j, below the tops of both borders and
                  below the piece's base: by the strings' law colStays.
  cells_stay      so do the stored table's cells.
What is not claimed. The four comparisons are premises: numbers of the plan and of the tiling.
Nothing on soundness.

-/
import Johnson.Desc.Sound.BordersSharedQ
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Shared

variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))

/-- Inside its range an acting part's value shows a tree's column as the oracles have it. -/
theorem actCol_eq (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) (j q : ℕ) (h1 : N.lo ≤ j)
    (h2 : j < hiAt k p l) :
    (strsOfAct Fr ((actQ N p l k).2 a)).col j q = colAt Fr a.2 j q := by
  show ((if N.lo ≤ j ∧ j < hiAt k p l then (posL Fr.all j q).map a.2.2 else none).getD []) = _
  rw [if_pos ⟨h1, h2⟩]
  rfl

/-- It shows the stored table's cells as the oracles have them. -/
theorem actCell_eq (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) :
    (strsOfAct Fr ((actQ N p l k).2 a)).cell = cellAt Fr a.2 := rfl

/-- **The columns stay.** -/
theorem cols_stay (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (a b : (P₁ × S₂) × Fr.E.Str)
    (τ : Iop.Tr (uLT C x.ds)) (hout : x.ior.red.out a τ = some b) (j q : ℕ) (h1 : N.lo ≤ j)
    (h2 : j < hiAt k p l) (h3 : j < hiAt (k + 1) p l) (h4 : j < x.base) :
    (strsOfAct Fr ((actQ N p l k).2 a)).col j q =
      (strsOfAct Fr ((actQ N p l (k + 1)).2 b)).col j q := by
  rw [actCol_eq N p l k a j q h1 h2, actCol_eq N p l (k + 1) b j q h1 h3, out_behind x a b τ hout,
    colStays C Fr x.base x.ds a.2 τ j q h4]

/-- So do the stored table's cells. -/
theorem cells_stay (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (a b : (P₁ × S₂) × Fr.E.Str)
    (τ : Iop.Tr (uLT C x.ds)) (hout : x.ior.red.out a τ = some b) :
    (strsOfAct Fr ((actQ N p l k).2 a)).cell = (strsOfAct Fr ((actQ N p l (k + 1)).2 b)).cell := by
  rw [actCell_eq, actCell_eq, out_behind x a b τ hout]
  exact (funext fun z => cellStays C Fr x.base x.ds a.2 τ z).symm

end VerifiableInference.Desc.Sound
