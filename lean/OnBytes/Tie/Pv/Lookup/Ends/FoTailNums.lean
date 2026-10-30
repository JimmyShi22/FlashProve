-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailNums.lean.
Two premises of kf_ext (OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean) on a smallness test's public
numbers, as tests that can be run.

* pieceTest tl q: PieceOK of each piece of call q, as a Bool. pieceOK_of_test: if the test passes,
  PieceOK holds of each piece.
* apartTest tl q: the key places of the pieces of call q lie pairwise apart, as a Bool.
  apart_of_test: if the test passes, they do.
That the record of a smallness test passes the two tests is not shown here. The premises on the
point's length and on n at most 63 are not among them.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailKf

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.DgP

/-- PieceOK of one piece, as a Bool. -/
def pieceTest1 (tl : HTailF2) (q n : ℕ) (p : Piece) : Bool :=
  decide (p.tree = tl.ix.ZZ) && decide (p.c0 = q * tl.mz) && decide (p.Cp ≤ p.CP) &&
    decide (p.CP = 2 ^ clog2 p.CP) && decide (p.Rp = 2 ^ p.a) &&
    decide (p.b = p.a + clog2 p.CP) && decide (p.b ≤ n) && decide (p.off % 2 ^ p.b = 0) &&
    decide (p.off + 2 ^ p.b ≤ 2 ^ n)

/-- PieceOK of each piece of call q, as a Bool. -/
def pieceTest (tl : HTailF2) (q : ℕ) : Bool :=
  (piecesL tl q).all (pieceTest1 tl q (tl.zOf q).call.n)

theorem pieceOK_of_test {tl : HTailF2} {q : ℕ} (h : pieceTest tl q = true) :
    ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p := by
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  simp only [pieceTest1, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, Nat.dvd_of_mod_eq_zero a8, a9⟩

/-- The pieces' key places lie pairwise apart, as a Bool. -/
def apartTest (tl : HTailF2) (q : ℕ) : Bool :=
  decide ((piecesL tl q).Pairwise fun p p' =>
    p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)

theorem apart_of_test {tl : HTailF2} {q : ℕ} (h : apartTest tl q = true) :
    (piecesL tl q).Pairwise fun p p' => p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off :=
  of_decide_eq_true h

end Fo
