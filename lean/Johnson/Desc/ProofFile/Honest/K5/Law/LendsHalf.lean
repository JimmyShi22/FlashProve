-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LendsHalf.lean: AN ATTENTION SEGMENT's OWN ROUNDS (kind K5):
THE PREMISE ON THE LENDING (Lends5, CoinsFewOf.lean in this folder: at every run the book's lending
to the kind's row returns) IS ONE Bool OF THE BOOK AND THE ROW: the frame's own test lendsRow
(Honest/Small/LendsRow.lean, of other authors). AN EQUIVALENCE. No filling, no prover, no thread.
Two statements with their proofs: calls alone.

  lendsRow_half       the test at the half's parts is the test at the row at the small input (k5Row,
                      Honest/K5/Row.lean): by lendsRow_map: the seat keeps the three counts
  lends5_iff          **Lends5 W₀ Rc Xi X Bk cells Z ↔ lendsRow Bk 0 Z.place (k5Row Z) = true**
  lendsRow_of_rowNamed   no declaration here: a name that stands, by one line `export`, for the law
                      of that spelling in ProofFile.Honest.Small (Honest/Small/RowNamed.lean): the shorter
                      test rowNamed gives the frame's

Called: lendsRow_iff and lendsRow_map (Honest/Small/LendsRow.lean). From left to right lends5_iff
spends that a book's type of runs has a member (the frame's own instance).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. That the Bool is true at any book is not proved here. It says whether the lending returns:
nothing on what is lent. The test reads of a part its takes, spends and carries alone. Through its
imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/
(lean/LIMITS.md, L15): a fact on import lines. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker

export ProofFile.Honest.Small (lendsRow_of_rowNamed)

section
variable {W₀ Rc Xi Tr X : Type}

/-- The frame's test at the half's parts is the test at the row at the small input. -/
theorem lendsRow_half (Bk : ProverCoinCounts) (cells : Tr → Cells) (Z : Seat5) :
    lendsRow Bk 0 Z.place (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts =
      lendsRow Bk 0 Z.place (k5Row Z) := by
  refine lendsRow_map Bk 0 Z.place _ ?_ (k5Row Z)
  exact fun _ => ⟨rfl, rfl, rfl⟩

/-- **THE PREMISE ON THE LENDING IS ONE Bool OF THE BOOK AND THE ROW.** -/
theorem lends5_iff (Bk : ProverCoinCounts) (cells : Tr → Cells) (Z : Seat5) :
    Lends5 W₀ Rc Xi X Bk cells Z ↔ lendsRow Bk 0 Z.place (k5Row Z) = true := by
  rw [← lendsRow_half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) Bk cells Z]
  exact ⟨fun h => (lendsRow_iff default 0 _ _).1 (h default),
    fun h k => (lendsRow_iff k 0 _ _).2 h⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.lendsRow_half
#print axioms ProofFile.Honest.K5.lends5_iff
