-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/TieOfTwo.lean: A TIE ON CELLS (`CellsTieOn`,
Honest/Law/Rule/TiesOn.lean) INSIDE A RANGE FOLLOWS FROM THE TIES INSIDE TWO PARTS THAT COVER THE
RANGE. Of no kind. No definition; one theorem.

  `cellsTieOn_of_two`

Why. The head's tie on cells is asked inside four ranges, of which one is a borrowed matrix's: its
symbols lie in another message than the three others'. The two are shown, if at all, on two roads.

What it is not.
  * Both ties are hypotheses.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- GENERAL. By cases on P. -/
theorem cellsTieOn_of_two {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {A G : Type} {opn : S → Option A}
    {mine : W → Nat → Nat → Nat → G} {seen : A → S → W → T.Wt → Nat → Nat → Nat → G}
    {In P : Nat → Nat → Nat → Prop}
    (h1 : CellsTieOn T At opn mine seen fun i r c => In i r c ∧ P i r c)
    (h2 : CellsTieOn T At opn mine seen fun i r c => In i r c ∧ ¬ P i r c) :
    CellsTieOn T At opn mine seen In := by
  intro k s m En hA a ha ds i r c hin
  by_cases hP : P i r c
  · exact h1 k s m En hA a ha ds i r c ⟨hin, hP⟩
  · exact h2 k s m En hA a ha ds i r c ⟨hin, hP⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.cellsTieOn_of_two
