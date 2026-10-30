-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/LotKind.lean: OF WHAT KIND THE HALVES OF K13's LOT ARE, AND WHAT
ITS OWN LIST HOLDS AT THE KIND's PLACE. Six statements with their proofs, on the definitions of
Part.lean of this folder alone; no definition.

Why. That the honest prover's first chain holds, at a given place, a given half is a fact on the
list of all lots' halves. The frame's lemma on that list asks of each lot that every half of it
stands at a place of the lot's own kind, and of the lot in question what its own list holds at the
place. These are the two facts for K13's lot (`k13Lot`).
Main names:
  `k13Lot_halves`: the lot lays one half. `k13Place_whereOf`: its place as numbers.
  `k13Lot_kind`: **every half that the lot lays stands at a place of the kind K13**, at every reader
    of the weights and every filler of the pile. `k13Lot_kind_id`: at the identity as the reader.
  `k13Lot_find`: **the lot's own list holds the kind's half at the kind's place.**
    `k13Lot_find_none`: nothing at another place.

What is not claimed. That the lot stands in any list of lots. That no other lot lays a half at a
place of this kind. Anything of the sub-protocol behind, in the same place's neighbour (the own
group and the row on W): THE LOT LAYS NO HALF FOR IT. Anything of the pile's filler, which stays a
parameter. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K13 (whereOf)

variable {W₀ Rc Xi Tr X : Type}

/-- The kind's place at a proof file's public part, as numbers: the first chain, behind the links,
number 3, the kind K13. -/
theorem k13Place_whereOf (Z : Pub) : k13Place (whereOf Z) = ⟨1, none, 3, .K13⟩ := rfl

/-- **The lot lays one half**: the kind's, at the pile's filler as handed the public part and the
segments' public data, and at the kind's numbers of that public part. -/
theorem k13Lot_halves (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) (Z : Pub)
    (G : Ground) :
    (k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Z G =
      [proverSideOfClaimCombination weights (pile Z G) (whereOf Z)] := rfl

/-- **EVERY HALF THAT THE LOT LAYS STANDS AT A PLACE OF THE KIND K13**, whatever the reader of the
weights and the pile's filler. -/
theorem k13Lot_kind (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) (Z : Pub)
    (G : Ground) :
    ∀ x ∈ (k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Z G,
      x.place.kind = .K13 := by
  intro x hx
  rw [k13Lot_halves, List.mem_singleton] at hx
  rw [hx]
  rfl

/-- The same where the reader of the weights is the identity. -/
theorem k13Lot_kind_id (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ (k13Lot (Rc := Rc) (Tr := Tr) (X := X) id pile).halves Z G, x.place.kind = .K13 :=
  k13Lot_kind id pile Z G

/-- **WHAT THE LOT's OWN LIST HOLDS AT THE KIND's PLACE**: the kind's half. -/
theorem k13Lot_find (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) (Z : Pub)
    (G : Ground) :
    ((k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Z G).find?
        (fun x => x.place == k13Place (whereOf Z)) =
      some (proverSideOfClaimCombination weights (pile Z G) (whereOf Z)) := by
  rw [k13Lot_halves]
  exact List.find?_cons_of_pos (by simp [proverSideOfClaimCombination])

/-- At every other place it holds nothing. -/
theorem k13Lot_find_none (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) (Z : Pub)
    (G : Ground) {p : Place} (hp : p ≠ k13Place (whereOf Z)) :
    ((k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Z G).find?
        (fun x => x.place == p) = none := by
  rw [k13Lot_halves, List.find?_cons_of_neg (by simpa [proverSideOfClaimCombination] using fun e => hp e.symm)]
  rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13Place_whereOf
#print axioms ProofFile.Honest.K13.k13Lot_halves
#print axioms ProofFile.Honest.K13.k13Lot_kind
#print axioms ProofFile.Honest.K13.k13Lot_kind_id
#print axioms ProofFile.Honest.K13.k13Lot_find
#print axioms ProofFile.Honest.K13.k13Lot_find_none
