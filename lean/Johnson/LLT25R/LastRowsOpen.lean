-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowsOpen.lean: ONE CLOSED SENTENCE FOR THE LAST TABLE's LETTER ML.rows AT
WHICH TWO OF THE LEDGER's IMPLICATIONS ARE IDENTITIES: `rowsOpen codes arr t₁ t₂ s w`: the seat's
door returns at the record s, and at what it returns every open row of the record's own group holds
of the words that the witness's tables give, read at the seats that the record's own book gives.
  `rows_open`: it IS what row 0's payer asks of ML.rows (the field rows of `LastLeftK`,
    Johnson/LLT25R/LastRowZero.lean): by rfl.
  `rowsBack_open`: and it IS what the seam's rows' half concludes (`insOpenAt` at `seatLast`,
    Johnson/LLT25R/LastSeamEnds.lean), WHERE THE TABLE's CODES cs ARE THE PLAN's: by rfl.
So at ML.rows := `rowsOpen (p14At Z).codes arr t₁ t₂` and cs := (p14At Z).codes the two implications
rows and rowsBack ask nothing. Limits. A definition and two identities. That this sentence is the
one that the top wants of the last table's rows is not said here. Nothing on soundness.

-/
import Johnson.LLT25R.LastSeamEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12.Seat (enterOwn)

variable {Cells Tok : Type}

/-- **The closed sentence.** -/
def rowsOpen (codes : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (s : S₃)
    (w : Wit Cells Tok MsgT) : Prop :=
  ∃ t, enterOwn s = .ok t ∧ ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
    (OnBytes.Means.wordsOn t.st
      (tabAt codes arr (seatBy (noLast t₁ t₂ s.loc.firstTree) s.book) t.st w))

/-- It is what row 0's payer asks. -/
theorem rows_open (codes : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (s : S₃)
    (w : Wit Cells Tok MsgT) (h : rowsOpen codes arr t₁ t₂ s w) :
    ∃ t, enterOwn s = .ok t ∧ ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
      (OnBytes.Means.wordsOn t.st
        (tabAt codes arr (seatBy (noLast t₁ t₂ s.loc.firstTree) s.book) t.st w)) := h

/-- It is what the seam's rows' half concludes. -/
theorem rowsBack_open {P S₁ S₂ : Type} {Fr : Frame} (codes : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (t₁ t₂ : ℕ) (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (h : insOpenAt (Fr := Fr) codes arr (seatLast t₁ t₂) a w) :
    rowsOpen codes arr t₁ t₂ a.1.2 w := h

end LLT25

#print axioms LLT25.rows_open
#print axioms LLT25.rowsBack_open
