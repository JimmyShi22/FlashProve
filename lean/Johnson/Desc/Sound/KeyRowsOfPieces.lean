-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRowsOfPieces.lean: A ROW OF SEATS MADE OF GIVEN PIECES: where the pieces of a
chain are at hand (cut off the written rounds' data by a maker), a list of rows, one behind each
piece, makes them a row of seats.

The setting. `SeatRow` (Johnson/Desc/Sound/KeyRows.lean) makes its pieces of its seats; the rule
asks that they be the pieces of the three chains (an equation). A maker that cuts the chains' data
at the blocks' rounds hands out pieces. So the row is made of them.

What is said.
  `lastRow A l`, `SeatRow.ofRows A l`: for a first row A and a list l of pairs (a piece, the row
    behind it): the row of seats in which each piece sits `outright`; it ends at the last pair's
    row.
  `ofRows_pieces`: its pieces are the given ones. `ofRows_zip`: so at `ps.zip rs`, where there is a
    row for each piece, its pieces are ps.
  `ofRows_laws`: what is asked of it, pair by pair: the piece is good between the row in front and
    the row behind, and its errors are shares of at most εs.

Limits. Forms.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Err)

variable {S Cl W : Type} {F : Frame}

/-- The row behind the last piece. -/
def lastRow (A : JointRow S F) : List (Piece (ckP .two) F S Cl W × JointRow S F) → JointRow S F
  | [] => A
  | x :: l => lastRow x.2 l

/-- **The given pieces as a row of seats.** -/
def SeatRow.ofRows : (A : JointRow S F) → (l : List (Piece (ckP .two) F S Cl W × JointRow S F)) →
    SeatRow Cl W A (lastRow A l)
  | A, [] => .nil A
  | _, x :: l => .outright x.2 x.1 (SeatRow.ofRows x.2 l)

theorem ofRows_pieces : ∀ (A : JointRow S F) (l : List (Piece (ckP .two) F S Cl W × JointRow S F)),
    (SeatRow.ofRows A l).pieces = l.map (·.1)
  | _, [] => rfl
  | _, x :: l => congrArg (x.1 :: ·) (ofRows_pieces x.2 l)

theorem ofRows_zip (A : JointRow S F) (ps : List (Piece (ckP .two) F S Cl W))
    (rs : List (JointRow S F)) (h : ps.length = rs.length) :
    (SeatRow.ofRows A (ps.zip rs)).pieces = ps := by
  rw [ofRows_pieces]
  exact List.map_fst_zip (Nat.le_of_eq h)

/-- What is asked, pair by pair. -/
def RowsGood (εs : ℝ≥0∞) : JointRow S F → List (Piece (ckP .two) F S Cl W × JointRow S F) → Prop
  | _, [] => True
  | A, x :: l =>
    ((x.1.bk A.on x.2.on (fun a _ => A.rel a) (fun a _ => x.2.rel a)).Good ∧ Err.Below x.1.err εs) ∧
      RowsGood εs x.2 l

theorem ofRows_laws (εs : ℝ≥0∞) : ∀ (A : JointRow S F)
    (l : List (Piece (ckP .two) F S Cl W × JointRow S F)),
    RowsGood εs A l → (SeatRow.ofRows A l).Laws εs
  | _, [], _ => trivial
  | _, x :: l, h => ⟨h.1, ofRows_laws εs x.2 l h.2⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ofRows_zip
#print axioms VerifiableInference.Desc.Sound.ofRows_laws
