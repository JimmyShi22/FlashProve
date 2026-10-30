-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotKind.lean: EVERY HALF THAT THE HONEST SIDE OF THE LOT OF THE
KIND "an attention segment's own rounds" (K5) LAYS STANDS AT A PLACE OF THAT KIND. Three small
theorems, on no premise: by the lot's own text.

Why. A law that says which half the halves of several lots, laid one behind another, hold at a place
p asks of every other lot M of the list: ∀ x ∈ M.halves Z G, x.place.kind ≠ p.kind. For that, each
lot says of which kind its own halves' places are; from "= .K5" and a p of another kind it is one
step.

Main names:
  `k5Half_place`   the half at public data Y stands at the place ⟨1, some Y.link, 3, .K5⟩
  `k5LotK_kind`   **every x in (k5LotK cells keyOf).halves Z G has x.place.kind = .K5**: general in
    cells, keyOf, Z and G
  `k5Lot_kind`   the same of the elder `k5Lot` (Honest/K5/Row.lean)

Limits. Nothing says that the list holds a half at all: where the maker of the public data yields
nothing the lot lays none, and the statement holds of an empty list. Nothing is said of other lots.
`k5Lot` and `k5LotK` bear one and the same name string: whoever tells lots apart by their names
cannot tell these two apart.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.KeysFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)

variable {W₀ Rc Xi Tr X : Type}

/-- The half at public data Y stands at Y's place: the first chain, Y's link, piece 3, the kind K5.
-/
theorem k5Half_place (cells : Tr → Cells) (Y : Seat5) :
    (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Y).place =
      ⟨1, some Y.link, 3, .K5⟩ := rfl

/-- **EVERY HALF OF THE LOT's HONEST SIDE STANDS AT A PLACE OF THE KIND K5.** No premise. -/
theorem k5LotK_kind (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground) :
    ∀ x ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G,
      x.place.kind = .K5 := by
  intro x hx
  have hx' : x ∈ (H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map (k5Half cells) := hx
  obtain ⟨y, _, hy⟩ := List.mem_filterMap.1 hx'
  obtain ⟨Y, _, rfl⟩ := Option.map_eq_some_iff.1 hy
  rfl

/-- The same of the elder lot. No premise. -/
theorem k5Lot_kind (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground) :
    ∀ x ∈ (k5Lot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G,
      x.place.kind = .K5 := by
  intro x hx
  have hx' : x ∈ (H2K5.k5Places G).filterMap fun y =>
      (seatAt keyOf Z G y.1 y.2.1 y.2.2).map (k5Half cells) := hx
  obtain ⟨y, _, hy⟩ := List.mem_filterMap.1 hx'
  obtain ⟨Y, _, rfl⟩ := Option.map_eq_some_iff.1 hy
  rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Half_place
#print axioms ProofFile.Honest.K5.k5LotK_kind
#print axioms ProofFile.Honest.K5.k5Lot_kind
