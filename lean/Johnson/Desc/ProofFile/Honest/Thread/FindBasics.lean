-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FindBasics.lean: THREE LEMMAS ON THE SEARCH BY PLACE IN A LIST
OF SIDES. General in the list: no lot, no filling, no prover. Of a side its place alone is read.
Three statements with their proofs.

  find_single         a list of one side: the search at that side's place finds it
  any_of_find         where the search finds a side at a place, some side stands there
  find_of_unique      a member of a list that alone stands at its place is what the search there
                      finds (near kin: find_own_place, Honest/K5/Law/LotFindAt.lean, which asks that
                      no place comes twice in the whole list)

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. On lists and places alone. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place)

/-- A list of one side: the search at that side's place finds it. -/
theorem find_single {V W X : Type} (x : Placed V W X) :
    ([x] : List (Placed V W X)).find? (fun g => g.place == x.place) = some x :=
  List.find?_cons_of_pos (by exact beq_self_eq_true _)

/-- Where the search finds a side at a place, some side stands there. -/
theorem any_of_find {V W X : Type} {hs : List (Placed V W X)} {p : Place} {y : Placed V W X}
    (h : hs.find? (fun g => g.place == p) = some y) : (hs.any fun g => g.place == p) = true :=
  List.any_eq_true.2 ⟨y, List.mem_of_find?_eq_some h,
    List.find?_some (p := fun g : Placed V W X => g.place == p) h⟩

/-- A member of a list that alone stands at its place is what the search there finds. -/
theorem find_of_unique {V W X : Type} : ∀ {hs : List (Placed V W X)} {x : Placed V W X}, x ∈ hs →
    (∀ y ∈ hs, y.place = x.place → y = x) → hs.find? (fun g => g.place == x.place) = some x
  | [], _, hx, _ => by cases hx
  | a :: hs, x, hx, hu => by
    by_cases e : a.place = x.place
    · rw [List.find?_cons_of_pos (p := fun g : Placed V W X => g.place == x.place)
        (beq_iff_eq.2 e), hu a (List.mem_cons_self ..) e]
    · rw [List.find?_cons_of_neg (p := fun g : Placed V W X => g.place == x.place)
        (fun b => e (beq_iff_eq.1 b))]
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd rfl e
      · exact find_of_unique hx' fun y hy => hu y (List.mem_cons_of_mem _ hy)

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.find_single
#print axioms ProofFile.Honest.FirstFill.any_of_find
#print axioms ProofFile.Honest.FirstFill.find_of_unique
