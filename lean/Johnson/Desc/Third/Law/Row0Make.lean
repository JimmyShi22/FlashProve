-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Make.lean: THE THREE FIELDS OF MAKE OF WHAT IS LEFT AT ROW 0 OF THE LAST
CHAIN's TABLE (wrap · hand · idle of RowZeroLeft, Johnson/Desc/Third/Law/Row0AtTable.lean), AT THE
PIECE AS THE MAKER OF PIECES CUTS IT (pieceOf, Johnson/Desc/Sound/Tiles.lean) OF THE BLOCK AS A
DESCRIPTION HOLDS IT (held, Johnson/Desc/Sound/PaidAtDesc.lean): K14's second part, typed at the
claims Unit and carried to the file's type of claims by Block.retype. One definition, one theorem.

OBJECT   pieceOf (heldZero p) base ds back r, heldZero p := held ((batchLinearConstraintsSecondPart p : Block S₃
         Unit).retype) written out (that file is not imported):
         pieceZeroAt F D c₀ rest₃ (Johnson/Flat/Last/LastCut.lean) is that term at c₀ := c0 Z :=
         (batchLinearConstraintsSecondPart (p14At Z) : Block S₃ Unit).retype (Johnson/LLT25R/LastSeat.lean).
USER     RowZeroLeft | RowZeroAtWords | RowZeroPublic's first three fields.
LETTERS  p · base · ds · back · r, with r.ext the identity.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  make_pieceOf         wrap ∧ hand ∧ idle.
What is not claimed. That the description's last chain's first block is that block:
last_flat_pure. That the cut's extractor at number 0 is the identity: a premise
(idle_zero at restCap extsLast). Nothing on soundness.

-/
import Johnson.Desc.Sound.Tiles
import Johnson.Desc.Third.Law.Row0AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

variable {P S₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame}

/-- K14's second part as a description's piece holds it: typed at the claims Unit, carried to the
file's type of claims, with the test on the words in front, lifted to the pair. It is
held ((batchLinearConstraintsSecondPart p : Block S₃ Unit).retype) (Johnson/Desc/Sound/PaidAtDesc.lean) by that
definition's text. -/
def heldZero {P Cl : Type} (p : P₁₄) : Block (P × S₃) Cl :=
  (below ((batchLinearConstraintsSecondPart p : Block S₃ Unit).retype (Cl' := Cl))).lift Prod.snd fun t s => (t.1, s)

/-- **The three fields of make, at the maker's own piece.** -/
theorem make_pieceOf (p : P₁₄) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest C Fr ((P × S₁ × S₂) × S₃) Wt ds) (hr : ∀ a τ w, r.ext a τ w = w) :
    YesOf (fun t : (P × S₁ × S₂) × S₃ => t.2) (batchLinearConstraintsSecondPart p : Block S₃ Unit)
        (pieceOf (heldZero (P := P × S₁ × S₂) (Cl := Cl) p) base ds back r).b ∧
      (∀ a τ b,
        (pieceOf (heldZero (P := P × S₁ × S₂) (Cl := Cl) p) base ds back r).ior.red.out a τ =
          some b → b.1.1 = a.1.1) ∧
      ∀ a τ w, (pieceOf (heldZero (P := P × S₁ × S₂) (Cl := Cl) p) base ds back r).ext a τ w = w :=
  ⟨(make_retype p _ rfl).1, (make_retype (Cl₀ := Unit) p _ rfl).2, hr⟩

end VerifiableInference.Desc.Third.Law
