-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RwBookRest.lean: THE READER OF THE ROWS ON THE COMMITTED TABLE THROUGH THE STATE's
OWN BOOK, rwBook arr mat (Johnson/Desc/K13/Law/ReaderByBook.lean), IS ONE AT TWO STATES OF THE
VERIFIER IN THE RELATION Rest (Johnson/Desc/First/K4/ReadsAtS.lean: what an accepting run of the
sub-protocol K4 leaves of the state), at every arr and mat. A statement and its proof.

  **`rwBook_rest`**: the statement: that reader reads of the state the fields st and book, and
    nothing else: Rest keeps both.
No new argument.
**Limits.** It is the content of the line rw of the structure K4Reads (Johnson/Road/K4/K4Reads.lean)
at this term: THE LINE ITSELF IS NOT STATED HERE: the file that states it at the composed meaning's
own data, Johnson/Road/K4/K4ReadsAtMgAll.lean, is not in this library. Nothing on soundness.
K04_law, the law of the sub-protocol K4 itself, IS NOT PROVED.


-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.First.K4.ReadsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (rwBook)

/-- **The reader through the state's own book is one at two states in Rest.** -/
theorem rwBook_rest {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → OnBytes.Slice.GE) (Z : Pp) {s s' : S}
    (h : Rest s s') :
    rwBook (Tok := Tok) arr mat (Z, s') = rwBook (Tok := Tok) arr mat (Z, s) := by
  funext w
  unfold rwBook
  dsimp only
  rw [h.st, h.book]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.rwBook_rest
