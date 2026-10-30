-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/PiecesSame.lean: THE
MAKER'S ROW OF PIECES OF THE FIRST CHAIN AT THE KEY FILE'S DESCRIPTION IS THE SAME AT THE
DESCRIPTION PULLED TO THE RECORDS: a frame in other files states its fields at atDesc (Key.descriptionFromSource X N
P) (piecesAt …); the links' laws stand at piecesAt … at FK X N P := (Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample.
The two rows of the first chain are one term, by unfolding.

Main names:
  row₁_same.

Object: piecesAt, atDesc (Johnson/Desc/Sound/).
User: none by name: keeps_k3 (KeepsAtRows.lean) passes the one row for the other by unfolding.
Letters: X, N, P, D, the heads and tails of the three flat lists, the rests.

Limits. The first chain's row alone. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieStated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.PiecesSame
open OnBytes OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Source)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (Fk)

variable {W : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)

/-- **The first chain's row of pieces is one term at the two descriptions.** -/
theorem row₁_same :
    ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd)).p₁ ::
      (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd)).l₁) =
    ((piecesAt (ckP .two) (FK X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).p₁ ::
      (piecesAt (ckP .two) (FK X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).l₁) :=
  rfl

end Johnson.RunOne.Law.PiecesSame

#print axioms Johnson.RunOne.Law.PiecesSame.row₁_same
