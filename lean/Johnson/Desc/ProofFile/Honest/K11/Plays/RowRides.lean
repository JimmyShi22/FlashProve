-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/RowRides.lean: the proofs of `RowRidesAt`, `K11KeepsLeaves`
and `K11RowsRide` (Honest/K11/Plays/RowRidesStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The first: the thread's "means" at the item unfolds to the library's "every row of the class
says its claim of the witness's words", at the state's statement, the class's rows and the words
read through the state's statement and book (as the library's own `row_back` writes it out,
Johnson/Top/H0/MergeLaw/RidesRows.lean); the class's rows are read off the statement and the book
alone (`classRows_same`, there); so two rewritings. The second: the kind's clause holds an equation
for the state behind, which turns two other fields alone: by rfl. The third: the first at the
second.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.RowRidesStatement
import Johnson.Top.H0.MergeLaw.RidesRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First (classRows)
open VerifiableInference.Desc.First.MergeLaw (classRows_same)
open VerifiableInference.Desc.Sound (wordsFirst)

/-- **A row's item rides past every member whose clause leaves the statement and the book.** -/
theorem rowRidesAt : RowRidesAt := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b m c
    hst k s mm E s' ps v _ hK h0
  obtain ⟨e1, e2⟩ := hst s s' hK
  have h1 : OnBytes.Means.AllSay _ s.st (classRows h.𝔇.N m c s)
      (wordsFirst h.𝔇.arr s.st s.book v) := h0
  show OnBytes.Means.AllSay _ s'.st (classRows h.𝔇.N m c s')
    (wordsFirst h.𝔇.arr s'.st s'.book v)
  rw [classRows_same h.𝔇.N m c e1 e2, e1, e2]
  exact h1

/-- **The kind's clause leaves the statement and the book.** -/
theorem k11KeepsLeaves : K11KeepsLeaves := by
  intro P s s' hk
  obtain ⟨⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩, -⟩ := hk
  exact ⟨rfl, rfl⟩

/-- **Every row's item rides past the merge's member.** -/
theorem k11RowsRide : K11RowsRide := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w P hk
    m c
  exact rowRidesAt Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    346 m c fun s s' hK => k11KeepsLeaves P s s' (hk s s' hK)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.rowRidesAt
#print axioms ProofFile.Honest.K11.k11KeepsLeaves
#print axioms ProofFile.Honest.K11.k11RowsRide
