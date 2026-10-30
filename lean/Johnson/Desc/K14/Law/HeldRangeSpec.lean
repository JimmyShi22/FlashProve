-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/HeldRangeSpec.lean: "HELD" WITH A TEST OF RANGE: THE STATEMENT. No proof here:
the statement is a definition of a proposition; the proof stands in HeldRange.lean.

IN PLAIN WORDS. The top statements' configuration decodes the stored table, lays what it decodes to
out as a matrix (Johnson/Flat/Claims.lean: cellsOf), and keeps it only if the matrix is in range
(OnBytes/Slice/ConfOf.lean: held). The law of "LIN point" speaks of the matrix by numbers of what
the stored table decodes to (matOf of tabU). The statement: WHERE THAT CONFIGURATION KEEPS A MATRIX,
IT IS THE SAME MATRIX, entry for entry, on the rows and columns that the linear claim reads.

  cellsAt      the matrix that a decoded table holds: cellsOf's text at this kind's typed data: row
               y, column c: the table's row c / 2 ^ kLo at the place c % 2 ^ kLo + 2 ^ kLo * y, if
               that place is within the message and before the cut; else 0.
  heldIf       kept if it meets R, a letter: any test of range.
  matAt        such a matrix by numbers; 0 outside.
  Spec.held    **the statement**: HeldTie at heldIf and matAt, where the matrix's places lie before
               the cut and within the message.
What is not claimed. Anything: nothing is proved here. That cellsAt IS cellsOf at a decoder's record
whose sizes are this shape's: by the two texts, letter for letter; not said in Lean here.

-/
import Johnson.Desc.K13.Law.HeldTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- A matrix of the committed matrix's shape. -/
abbrev MatAt (p : Par) : Type :=
  Fin p.S.matrixRows → Fin (2 ^ (p.S.kLo + p.S.fold.index.v)) → GE

/-- The matrix that a decoded table holds. cut: the number of a row's entries before its pads. -/
def cellsAt (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat) (cut : Nat)
    (U : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) : MatAt p :=
  fun y c =>
    if h : c.val % 2 ^ p.S.kLo + 2 ^ p.S.kLo * y.val < p.S.fold.index.code.ell ∧
        c.val % 2 ^ p.S.kLo + 2 ^ p.S.kLo * y.val < cut then
      U (bitsOf p.S.fold.index.v (c.val / 2 ^ p.S.kLo),
        ⟨c.val % 2 ^ p.S.kLo + 2 ^ p.S.kLo * y.val, h.1⟩)
    else 0

open Classical in
/-- Kept if it meets R. -/
noncomputable def heldIf (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat) (cut : Nat)
    (R : MatAt p → Prop)
    (U : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) :
    Option (MatAt p) :=
  if R (cellsAt p err₂ eM rank cut U) then some (cellsAt p err₂ eM rank cut U) else none

/-- Such a matrix by numbers; 0 outside. -/
def matAt (p : Par) (M : MatAt p) (y c : Nat) : GE :=
  if h : y < p.S.matrixRows ∧ c < 2 ^ (p.S.kLo + p.S.fold.index.v) then M ⟨y, h.1⟩ ⟨c, h.2⟩ else 0

namespace Spec

/-- **Where a matrix is kept, it is the decoded table's.** -/
def held : Prop :=
  ∀ (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat) (cut : Nat)
    (R : MatAt p → Prop),
    p.S.matrixRows * 2 ^ p.S.kLo ≤ cut →
    p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.code.ell →
    HeldTie p err₂ eM rank (heldIf p err₂ eM rank cut R) (matAt p)

end Spec

end Desc.K14.Law
