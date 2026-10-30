-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortLetters4.lean: THE LETTER Kx ON THE SECOND ROAD, BY THE SORT OF THE
LINK, AS WRITTEN TERMS: at a layers' link `kxAll3` (SortLetters3.lean) as it is; at an attention
link `kxAtt`; at the head's link `kxHead`. Definitions, and theorems: clauses read back.
SortLetters.lean .. SortLetters3.lean stand as they are.

Why the term grows at thirteen links. The lookup's runs "planes" (attention and the head) and
"join" (attention) claim forms that the CALLING kind hands in. That the worth of such a form at a
full later state hangs on the fixed part and the data alone asks, of the fixed part, that the
entries which the form names stand at unit rows (EntsOk): no clause of the named Ok says so for
these forms (by a reading). The clauses are another file's: PlanesAttOk
rd c nU q (planes, keysEnts) and PlanesHeadOk iU3 kap nU q (planes): OkPlanes.lean, cut by sort so
that no link owes another sort's clause idly. The laws of the three runs at K9's letters
(SortK3PlanesRun.lean: k3pl_att, k3jn_att, k3pl_head) ask of Kx these clauses and K3's promise, and
nothing more.

What is said.
  `kxAtt lmC jC lmD jD c nU q` := kxAll3 lmC jC lmD jD q ∧ PlanesAttOk rdAll c nU q.
  `kxHead lmC jC lmD jD iU3 nU q` := kxAll3 lmC jC lmD jD q ∧ PlanesHeadOk iU3 kapAll nU q.
  `kxAtt_k3`, `kxHead_k3` (K3's promise: hK of the lookup's laws) · `kxAtt_numbers`,
    `kxHead_numbers` (hK of numbers_attC_at, numbers_headC_at) · `kxAtt_planes`, `kxHead_planes`
    (hP of k3pl_att, k3jn_att, k3pl_head) · `kxAtt_of`, `kxHead_of`.

Limits. DEFINITIONS AND PROJECTIONS. WHAT STANDS IN Kx IS OWED BY THE FIELD AreadyS AT EVERY STATE
OF THE CONDITION IN FRONT OF THE BATCHING: the new clauses too: from the head, an opening and the
table's promise they are theorems: P5J.planesAttOk_mg, P5J.planesHeadOk_mg
(Johnson/P5J/K09PlanesAt.lean). BESIDE, EVALUATED, NO THEOREM (a ride at the 13 honest fronts of one
full-size run): TESTS WITH CODE written for the clauses planes and keysEnts said yes at 13 of 13 and
12 of 12; at "planes" forms were handed in; keysEnts held idly (the key forms name no entry). THAT
RIDE IS NO GROUND FOR THE CLAUSE planes: its test (planesAttB, planesHeadB over formsUpTo,
OkPlanes.lean) asks e = 0 and e = 1 and the columns below n; the clause asks every e and column; a
yes gives EntsOk of the tested list (entsOk_of_B), and no law in that file goes from there to the
clause. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters3
import Johnson.Desc.First.Link.Law.OkPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.LinkJoin (NumbersThree PlanesAttOk PlanesHeadOk)

/-- **Kx AT AN ATTENTION LINK.** -/
def kxAtt (lmC jC lmD jD : ℕ) (c : First.Att.P.ParC) (nU : Array ℕ)
    (q : Phi BetaAll × Option Pub9) : Prop :=
  kxAll3 lmC jC lmD jD q ∧ PlanesAttOk rdAll c nU q

/-- **Kx AT THE HEAD's LINK.** -/
def kxHead (lmC jC lmD jD iU3 : ℕ) (nU : Array ℕ) (q : Phi BetaAll × Option Pub9) : Prop :=
  kxAll3 lmC jC lmD jD q ∧ PlanesHeadOk iU3 kapAll nU q

section
variable {lmC jC lmD jD : ℕ} {c : First.Att.P.ParC} {iU3 : ℕ} {nU : Array ℕ}

theorem kxAtt_k3 : ∀ q, kxAtt lmC jC lmD jD c nU q → kxAll lmC jC lmD jD q :=
  fun _ h => h.1.1

theorem kxAtt_numbers : ∀ q, kxAtt lmC jC lmD jD c nU q → NumbersThree q := fun _ h => h.1.2

theorem kxAtt_planes : ∀ q, kxAtt lmC jC lmD jD c nU q → PlanesAttOk rdAll c nU q :=
  fun _ h => h.2

theorem kxAtt_of {q : Phi BetaAll × Option Pub9} (h1 : kxAll3 lmC jC lmD jD q)
    (h2 : PlanesAttOk rdAll c nU q) : kxAtt lmC jC lmD jD c nU q := ⟨h1, h2⟩

theorem kxHead_k3 : ∀ q, kxHead lmC jC lmD jD iU3 nU q → kxAll lmC jC lmD jD q :=
  fun _ h => h.1.1

theorem kxHead_numbers : ∀ q, kxHead lmC jC lmD jD iU3 nU q → NumbersThree q :=
  fun _ h => h.1.2

theorem kxHead_planes : ∀ q, kxHead lmC jC lmD jD iU3 nU q → PlanesHeadOk iU3 kapAll nU q :=
  fun _ h => h.2

theorem kxHead_of {q : Phi BetaAll × Option Pub9} (h1 : kxAll3 lmC jC lmD jD q)
    (h2 : PlanesHeadOk iU3 kapAll nU q) : kxHead lmC jC lmD jD iU3 nU q := ⟨h1, h2⟩

end

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.kxAtt_k3
#print axioms VerifiableInference.Desc.PhiAll.kxAtt_numbers
#print axioms VerifiableInference.Desc.PhiAll.kxAtt_planes
#print axioms VerifiableInference.Desc.PhiAll.kxAtt_of
#print axioms VerifiableInference.Desc.PhiAll.kxHead_k3
#print axioms VerifiableInference.Desc.PhiAll.kxHead_numbers
#print axioms VerifiableInference.Desc.PhiAll.kxHead_planes
#print axioms VerifiableInference.Desc.PhiAll.kxHead_of
