-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FirstFindKind.lean: the lemmas of Honest/FirstFind.lean with their
hypothesis on the other lots stated by kinds. If every prover's side of a lot is at a place of one
kind, a lot of another kind has no side at a place of this kind. Three lemmas; no definition.

  1  `firstOf_find_kind`   the lot is in the list; every lot of the list either has sides at places
     of other kinds than the place's alone, or has the same sides as the lot: what is found in the
     whole list is what is found in the lot
  2  `atPure_first_find_kind`   the same for the prover that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns
  3  `replyLot_kind`   every side of the next token's lot (`replyLot`, Honest/K7.lean) is at a place
     of the kind K7: the form of the lemma that each lot needs

Limits.
  * The lemmas are about lists and places.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.FirstFind
import Johnson.Desc.ProofFile.Honest.K7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

theorem firstOf_find_kind {V W X : Type} {Z : Pub} {G : Ground} {ls : List (HLot V W X)}
    {L : HLot V W X} {p : Place} {g : Placed V W X} (hL : L ∈ ls)
    (ho : ∀ M ∈ ls,
      (∀ x ∈ M.halves Z G, x.place.kind ≠ p.kind) ∨ M.halves Z G = L.halves Z G)
    (hg : (L.halves Z G).find? (fun x => x.place == p) = some g) :
    (firstOf Z G ls).find? (fun x => x.place == p) = some g :=
  firstOf_find hL
    (fun M hM => (ho M hM).imp (fun hk x hx e => hk x hx (congrArg Place.kind e)) id) hg

theorem atPure_first_find_kind {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} {p : Place}
    {g : Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} (hL : L ∈ P.lots)
    (ho : ∀ M ∈ P.lots,
      (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ p.kind) ∨ M.halves A.Z A.G = L.halves A.Z A.G)
    (hg : (L.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g := by
  rw [(atPure_ok h).2.2.2.2.2.2.2.1]
  exact firstOf_find_kind hL ho hg

theorem replyLot_kind {W₀ Rc Tr X : Type} (Z : Pub) (G : Ground) :
    ∀ x ∈ (replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Z G,
      x.place.kind = .K7 := by
  intro x hx
  obtain rfl := List.mem_singleton.1 hx
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.firstOf_find_kind
#print axioms ProofFile.Honest.atPure_first_find_kind
#print axioms ProofFile.Honest.replyLot_kind
