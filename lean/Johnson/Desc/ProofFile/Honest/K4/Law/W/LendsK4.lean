-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LendsK4.lean: one statement with its proof.

What is here. WHETHER THE BOOK LENDS THE SEATED ROW OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN
ROUNDS (sub-protocol K4) IS WHETHER IT LENDS THE UNSEATED ROW `k4RowIn Q` (Honest/K4/Part.lean),
which is made of the member's public data alone. So `lendsRow Bk 0 (k4Place Q) (k4RowIn Q)`
(Honest/Small/LendsRow.lean) is a Bool of the book and these data: the four readers cells, weights,
tokens and look have left it. One call of `lendsRow_map`: the seat, `Part.lift`, keeps a part's
takes, spends and carries by its text.

  `k4_lends_row`   **the equation.** No hypothesis.

Not shown here. That any book passes the test. Nothing on soundness, on completeness or on any other
property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.K4.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest

/-- **The seated row lends as the unseated row does.** No hypothesis. -/
theorem k4_lends_row {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (Bk : ProverCoinCounts) :
    lendsRow Bk 0 (k4Place Q) (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts =
      lendsRow Bk 0 (k4Place Q) (k4RowIn Q) := by
  show lendsRow Bk 0 (k4Place Q) ((k4RowIn Q).map _) = _
  refine lendsRow_map Bk 0 (k4Place Q) _ ?_ (k4RowIn Q)
  exact fun _ => ⟨rfl, rfl, rfl⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_lends_row
