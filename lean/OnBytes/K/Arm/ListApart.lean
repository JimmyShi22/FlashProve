-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ListApart.lean: a written list as a set, and one test with values in Bool for "no two
of the set are spelt alike".

General in the type X of what stands on the list, in the type Y of spellings (any type on which
equality can be decided: a string of bytes, a pair of strings) and in the spelling sp : X → Y. No
protocol, no file and no hash occurs here.

1. What the file contains.
    `okList R`: x stands on the list R.
    `itemsApartB sp R`: no two places of the list have one spelling. It speaks of places: at a list
      on which one value stands twice it says no. So the list is to be written without repeats.

2. What is checked when the file compiles. The proofs.

3. Theorems.
    `okList_iff`: the test says yes exactly at the values on the list.
    `hsp_of_list`: where `itemsApartB sp R` says yes, sp is one to one on what passes `okList R`.
    `itemsApartB_one`: at a list of one place the test says yes, whatever sp is.

4. What is not claimed. That the test says yes at any list of more than one place. `itemsApartB_one`
   says nothing on sp: a set of one value is spelt one to one by every function.

Terms: lean/GLOSSARY.md.


-/
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFrontList

variable {X : Type} [DecidableEq X] {Y : Type} [DecidableEq Y]

/-- The value stands on the list. -/
def okList (R : List X) (x : X) : Bool := decide (x ∈ R)

/-- No two places of the list have one spelling: so no value stands on it twice. -/
def itemsApartB (sp : X → Y) (R : List X) : Bool := decide ((R.map sp).Nodup)

/-- The test says yes exactly at the values on the list. -/
theorem okList_iff (R : List X) (x : X) : okList R x = true ↔ x ∈ R := decide_eq_true_iff

/-- **Where the test says yes, the spelling is one to one on the list.** -/
theorem hsp_of_list (sp : X → Y) (R : List X) (h : itemsApartB sp R = true) (x y : X)
    (hx : okList R x = true) (hy : okList R y = true) (e : sp x = sp y) : x = y :=
  List.inj_on_of_nodup_map (of_decide_eq_true h) (of_decide_eq_true hx) (of_decide_eq_true hy) e

omit [DecidableEq X] in
/-- At a list of one place the test says yes, whatever the spelling is. -/
theorem itemsApartB_one (sp : X → Y) (x : X) : itemsApartB sp [x] = true :=
  decide_eq_true (List.nodup_singleton (sp x))

end OnBytes.K.Arm.ProofFrontList
