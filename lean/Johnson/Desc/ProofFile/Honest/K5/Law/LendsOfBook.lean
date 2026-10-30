-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LendsOfBook.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN
ROUNDS (kind K5): Lends5 (Honest/K5/Law/CoinsFewOf.lean), the premise hLent of the kind's joined
law, FROM A TEST WITH CODE ON THE BOOK AND ON THE PARTS' THREE PUBLIC FIELDS: from rowFits; from the
shorter rowNamed (both: Honest/Small/RowNamed.lean). Three statements with their proofs. No
definition.

  k5_parts_plain         a part of K5's half takes no coin of its own and carries none: so the
                         tests' first two clauses are true at K5's parts
  lends5_of_book · lends5_of_named   CONDITIONAL: **Lends5 from rowFits; from rowNamed**

Eleven more names of the namespace ProofFile.Honest.K5 stand for the declarations of the same spelling in
ProofFile.Honest.Small (Honest/Small/RowNamed.lean; one line `export`) and are no declarations here:
`partFits`, `rowFits`, `partBook_of_fits`, `rowBook_of_rowFits`, `lends_of_rowFits`, `partNamed`,
`rowNamed`, `inside_first`, `partFits_of_named`, `rowFits_of_named`, `lends_of_rowNamed`. What they
say, their premises and their Limits stand there.

Called: lends_of_rowFits, lends_of_rowNamed (Honest/Small/RowNamed.lean).

Limits. Conditional. THAT A TEST ACCEPTS AT ANY BOOK THAT A MAKER MAKES IS NOT SHOWN: of the book's
maker this file's writer knows one theorem (bookWhole_word, Honest/AtPureLaw.lean): it says that its
book passes the book's own tests: it says nothing on the entries at a place.
Honest/K5/Law/LendsOfBookToy.lean has each test's yes and no at made-up books. What is lent is not
said: that the lending returns, and no more. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.CoinsFewOf
import Johnson.Desc.ProofFile.Honest.K3.Law.RowLends
import Johnson.Desc.ProofFile.Honest.Law.Rule.Lent
import Johnson.Desc.ProofFile.Honest.Small.RowNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Place FileDescription)

export ProofFile.Honest.Small (partFits rowFits partBook_of_fits rowBook_of_rowFits lends_of_rowFits
  partNamed rowNamed inside_first partFits_of_named rowFits_of_named lends_of_rowNamed)

variable {W₀ Rc Xi Tr X : Type}

/-- A part of K5's half takes no coin of its own and carries none. -/
theorem k5_parts_plain (cells : Tr → Cells) (Z : Seat5) :
    ∀ p ∈ (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts,
      p.takes = ⟨0, 0⟩ ∧ p.carries = [] := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hq
  rcases s with ⟨k | _ | n, i⟩ <;> exact ⟨rfl, rfl⟩

/-- **Lends5 FROM A TEST ON THE BOOK.** CONDITIONAL: rowFits accepts at K5's place and parts. -/
theorem lends5_of_book {Bk : ProverCoinCounts} {cells : Tr → Cells} {Z : Seat5}
    (h : rowFits Bk (Bk.rowsOf 0) (dueAt Bk.first) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = true) :
    Lends5 W₀ Rc Xi X Bk cells Z := fun k => lends_of_rowFits h k

/-- **Lends5 FROM THE SHORTER TEST, AT A BOOK THAT PASSES ITS OWN TESTS.** CONDITIONAL: as
`lends_of_rowNamed`, at K5's place and parts. -/
theorem lends5_of_named {Yi : Type} {F : FileDescription Yi} {Bk : ProverCoinCounts} (h : Bk.word F = none)
    (hp : F.placesOk = true) {cells : Tr → Cells} {Z : Seat5}
    (ha : Z.place ∈ F.first.blocksInOrder.map (·.place))
    (hn : rowNamed Bk (Bk.rowsOf 0) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = true) :
    Lends5 W₀ Rc Xi X Bk cells Z := fun k => lends_of_rowNamed h hp ha hn k

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_parts_plain
#print axioms ProofFile.Honest.K5.lends5_of_book
#print axioms ProofFile.Honest.K5.lends5_of_named
