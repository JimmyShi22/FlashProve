-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortLetters3.lean: THE LETTER Kx ON THE SECOND ROAD: K3's PROMISE AT
THE LINK's TWO LOOKUP SEATS (`kxAll`, SortLetters.lean) AND THE THREE CLAUSES funs, heard, hmS
(`NumbersThree`, SortNumbersC.lean): WITHOUT hlen. A definition, and theorems: clauses read back.
SortLetters.lean and SortLetters2.lean stand as they are.

Why a third term. kxAll2 (SortLetters2.lean) holds NumbersOk whole, hlen among its clauses. On the
second road hlen is proved from the batching's own yes AT THE BARE PROMISE: a bare promise that
held hlen would make that proof a circle. So the term that is laid for Kx there must not hold it.
It names no number of claims, so neither the link nor the tables of lengths.

What is said.
  `kxAll3 lmC jC lmD jD q` := kxAll lmC jC lmD jD q ∧ NumbersThree q.
  `kxAll3_k3` (for the payers of the field k3) · `kxAll3_numbers` (**the premise hK of
    numbers_layersC, numbers_attC, numbers_headC, to the letter**) · `kxAll3_of` · `kxAll3_of_two`:
    kxAll2 gives it (so what ends in kxAll2 ends in kxAll3).

Limits. A DEFINITION AND PROJECTIONS. TWO PLACES MAY YET MAKE Kx GROW: the caller's clauses of the
lookup's "planes" and "join". Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters2
import Johnson.Desc.First.Link.Law.SortNumbersC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.LinkJoin (NumbersOk NumbersThree)

/-- **Kx ON THE SECOND ROAD.** -/
def kxAll3 (lmC jC lmD jD : ℕ) (q : Phi BetaAll × Option Pub9) : Prop :=
  kxAll lmC jC lmD jD q ∧ NumbersThree q

/-- K3's promise at the two seats, read back. -/
theorem kxAll3_k3 {lmC jC lmD jD : ℕ} :
    ∀ q, kxAll3 lmC jC lmD jD q → kxAll lmC jC lmD jD q := fun _ h => h.1

/-- **hK.** -/
theorem kxAll3_numbers {lmC jC lmD jD : ℕ} :
    ∀ q, kxAll3 lmC jC lmD jD q → NumbersThree q := fun _ h => h.2

/-- It is met by the two together. -/
theorem kxAll3_of {lmC jC lmD jD : ℕ} {q : Phi BetaAll × Option Pub9}
    (h1 : kxAll lmC jC lmD jD q) (h2 : NumbersThree q) : kxAll3 lmC jC lmD jD q := ⟨h1, h2⟩

/-- The second term, kxAll2 (SortLetters2.lean), gives it. -/
theorem kxAll3_of_two {lmC jC lmD jD : ℕ} {len : Phi BetaAll × Option Pub9 → ℕ}
    {q : Phi BetaAll × Option Pub9} (h : kxAll2 lmC jC lmD jD len q) :
    kxAll3 lmC jC lmD jD q := ⟨h.1, ⟨h.2.funs, h.2.heard, h.2.hmS⟩⟩

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.kxAll3_k3
#print axioms VerifiableInference.Desc.PhiAll.kxAll3_numbers
#print axioms VerifiableInference.Desc.PhiAll.kxAll3_of
#print axioms VerifiableInference.Desc.PhiAll.kxAll3_of_two
