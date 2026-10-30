-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/LotKeepKind.lean: kind K13, the members' batching: EVERY HALF THAT
THE KEPT FORM OF THE KIND's LOT LAYS (`k13LotKeep`, KeepJob.lean of this folder) STANDS AT A PLACE
OF THE KIND K13: whatever the reader of the weights, the filler of the pile, and the reader and
setter of what is kept. Two statements with their proofs; no definition; no hypothesis.

Main names: `k13LotKeep_halves`: the lot lays one half: by its text. `k13LotKeep_kind`: **the
kind.**

Why. A filling's maker holds the lists of several kinds; that no other list has a side at a place of
a given kind is drawn from one such sentence a list. `k13Lot_kind` (LotKind.lean of this folder) is
the plain lot's; this is the same proof at the kept form.

Limits. A sentence on places alone: nothing on what a half does. Nothing calls these statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.KeepJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K13 (whereOf)
variable {W₀ Rc Xi Tr X : Type}

/-- **The kept form of the lot lays one half**: by its text. -/
theorem k13LotKeep_halves (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi)
    (get : X → Option K13Kept) (set : X → Option K13Kept → X) (Z : Pub) (G : Ground) :
    (k13LotKeep (Rc := Rc) (Tr := Tr) weights pile get set).halves Z G =
      [k13HalfKeep weights (pile Z G) get set (whereOf Z)] := rfl

/-- **EVERY HALF THAT THE KEPT FORM OF THE LOT LAYS STANDS AT A PLACE OF THE KIND K13**, whatever
the reader of the weights, the pile's filler, and the reader and setter of what is kept. -/
theorem k13LotKeep_kind (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi)
    (get : X → Option K13Kept) (set : X → Option K13Kept → X) (Z : Pub) (G : Ground) :
    ∀ x ∈ (k13LotKeep (Rc := Rc) (Tr := Tr) weights pile get set).halves Z G,
      x.place.kind = .K13 := by
  intro x hx
  rw [k13LotKeep_halves, List.mem_singleton] at hx
  rw [hx]
  rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13LotKeep_halves
#print axioms ProofFile.Honest.K13.k13LotKeep_kind
