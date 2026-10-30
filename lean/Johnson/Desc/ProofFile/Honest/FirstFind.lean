-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FirstFind.lean: which prover's side is found at a place of the first
chain. `firstOf` (Honest/Frame.lean) concatenates the prover's sides of a list of lots, and the
functions that play a chain take the first side whose place is the sub-protocol's
(`List.find?`, in `chainSteps`). These lemmas say when that first side is a given lot's own. Four
lemmas; no definition.

  1  `find_none_of_places`   a list with no side at the place: nothing is found
  2  `firstOf_find`   the lot is in the list; every lot of the list either has no side at the place
     or has the same sides as the lot: what is found in the whole list is what is found in the lot
  3  `firstOf_find_named`   the same, with the second hypothesis by the lots' names: a lot of
     another name has no side at the place, and a lot of the same name is the lot
  4  `atPure_first_find`   the same for the prover that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns

Limits.
  * What a lot's own list holds at the place (the hypothesis `hg`) is for the caller to show.
  * The lemmas are about lists.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

variable {V W X : Type}

theorem find_none_of_places {l : List (Placed V W X)} {p : Place} (h : ∀ x ∈ l, x.place ≠ p) :
    l.find? (fun x => x.place == p) = none := by
  rw [List.find?_eq_none]
  intro x hx hb
  exact h x hx (eq_of_beq hb)

theorem firstOf_find {Z : Pub} {G : Ground} {ls : List (HLot V W X)} {L : HLot V W X} {p : Place}
    {g : Placed V W X} (hL : L ∈ ls)
    (ho : ∀ M ∈ ls, (∀ x ∈ M.halves Z G, x.place ≠ p) ∨ M.halves Z G = L.halves Z G)
    (hg : (L.halves Z G).find? (fun x => x.place == p) = some g) :
    (firstOf Z G ls).find? (fun x => x.place == p) = some g := by
  unfold firstOf
  induction ls with
  | nil => cases hL
  | cons M tl ih =>
    rw [List.flatMap_cons, List.find?_append]
    rcases ho M (List.mem_cons.2 (Or.inl rfl)) with hn | he
    · rw [find_none_of_places hn]
      have hL' : L ∈ tl := by
        rcases List.mem_cons.1 hL with e | h'
        · rw [e, find_none_of_places hn] at hg
          cases hg
        · exact h'
      exact ih hL' fun N hN => ho N (List.mem_cons_of_mem _ hN)
    · rw [he, hg]
      rfl

theorem firstOf_find_named {Z : Pub} {G : Ground} {ls : List (HLot V W X)} {L : HLot V W X}
    {p : Place} {g : Placed V W X} (hL : L ∈ ls)
    (ho : ∀ M ∈ ls, M.name ≠ L.name → ∀ x ∈ M.halves Z G, x.place ≠ p)
    (h1 : ∀ M ∈ ls, M.name = L.name → M = L)
    (hg : (L.halves Z G).find? (fun x => x.place == p) = some g) :
    (firstOf Z G ls).find? (fun x => x.place == p) = some g := by
  refine firstOf_find hL (fun M hM => ?_) hg
  by_cases hn : M.name = L.name
  · exact Or.inr (by rw [h1 M hM hn])
  · exact Or.inl (ho M hM hn)

theorem atPure_first_find {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} {p : Place}
    {g : Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} (hL : L ∈ P.lots)
    (ho : ∀ M ∈ P.lots,
      (∀ x ∈ M.halves A.Z A.G, x.place ≠ p) ∨ M.halves A.Z A.G = L.halves A.Z A.G)
    (hg : (L.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g := by
  rw [(atPure_ok h).2.2.2.2.2.2.2.1]
  exact firstOf_find hL ho hg

end ProofFile.Honest

#print axioms ProofFile.Honest.find_none_of_places
#print axioms ProofFile.Honest.firstOf_find
#print axioms ProofFile.Honest.firstOf_find_named
#print axioms ProofFile.Honest.atPure_first_find
