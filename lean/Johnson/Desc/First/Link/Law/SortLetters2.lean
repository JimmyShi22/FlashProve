-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortLetters2.lean: THE LETTER Kx OF WHAT IS LEFT OF A LINK's LAW
(LinkRestAtSort3 | 4), SECOND FORM: K3's PROMISE AT THE LINK's TWO LOOKUP SEATS (`kxAll`,
SortLetters.lean, which stands as it is) AND WHAT THE NUMBERS ASK OF THE FIXED PART (`NumbersOk`,
SortNumbers.lean). A definition, and theorems: clauses read back.

Why. The field Anumbers' payers want four clauses more than the first form's kxAll holds
(SortNumbers.lean's head says which and why).
Kx is a free letter in the lists: so the
term that is laid at the call grows by one conjunct.

What is said.
  `kxAll2 lmC jC lmD jD len q` := kxAll lmC jC lmD jD q ∧ NumbersOk len q. len: the link's own
    runs' number of claims off the fixed part: at the call fun q => lenRuns q (rlOf L ‹the sort's
    terms› ‹the sort's lengths›).
  `kxAll2_k3`: the first form's clause read back (what the payers of the field k3 take).
  `kxAll2_numbers`: **the premise hK of numbers_layers3, numbers_att3, numbers_head3, to the
    letter**, at Kx := kxAll2 .. len.
  `kxAll2_of`: it is met by the two together.

WHAT FOLLOWS. Aready owes kxAll2 at what is fixed in front of the batching: beside K3's promise
(paid from "reached" and the table's promise by kx_of_table) the four clauses funs,
heard, hmS, hlen.

Limits. A DEFINITION AND PROJECTIONS. WHETHER kxAll2 CAN BE MET AT AN HONEST STATE: its clause hlen
has no theorem; evaluated: equality, no slack, at 13 of the 25 segments;
at the 12 attention segments not known. TWO PLACES MAY YET MAKE Kx GROW AGAIN: the caller's
clauses of the lookup's "planes" and "join" (hb, hp', hkv: paid inside k3pl_att,
k3pl_head and k3jn_att, SortK3PlanesRun.lean, at the link's law's closed letters alone (phiAll u
psiAll · FullAt nU · the named Ok with Kx), in scope, at an opening (hS, hR, O; k3jn_att: O alone):
k3pl_att under h4, ha, hm, hL, hK, hP, hlm · k3pl_head under hL, hH, hi, hK, hP, hlm · k3jn_att
under h4, hg, ha, hL, hK, hP: hP asks of Kx the further clauses PlanesAttOk | PlanesHeadOk. NO
MEMBER there). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters
import Johnson.Desc.First.Link.Law.SortNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.LinkJoin (NumbersOk)

/-- **Kx, SECOND FORM.** -/
def kxAll2 (lmC jC lmD jD : ℕ) (len : Phi BetaAll × Option Pub9 → ℕ)
    (q : Phi BetaAll × Option Pub9) : Prop :=
  kxAll lmC jC lmD jD q ∧ NumbersOk len q

/-- K3's promise at the two seats, read back. -/
theorem kxAll2_k3 {lmC jC lmD jD : ℕ} {len : Phi BetaAll × Option Pub9 → ℕ} :
    ∀ q, kxAll2 lmC jC lmD jD len q → kxAll lmC jC lmD jD q := fun _ h => h.1

/-- **hK.** -/
theorem kxAll2_numbers {lmC jC lmD jD : ℕ} {len : Phi BetaAll × Option Pub9 → ℕ} :
    ∀ q, kxAll2 lmC jC lmD jD len q → NumbersOk len q := fun _ h => h.2

/-- It is met by the two together. -/
theorem kxAll2_of {lmC jC lmD jD : ℕ} {len : Phi BetaAll × Option Pub9 → ℕ}
    {q : Phi BetaAll × Option Pub9} (h1 : kxAll lmC jC lmD jD q) (h2 : NumbersOk len q) :
    kxAll2 lmC jC lmD jD len q := ⟨h1, h2⟩

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.kxAll2_k3
#print axioms VerifiableInference.Desc.PhiAll.kxAll2_numbers
#print axioms VerifiableInference.Desc.PhiAll.kxAll2_of
