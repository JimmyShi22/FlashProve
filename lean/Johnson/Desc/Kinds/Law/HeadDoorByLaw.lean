-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadDoorByLaw.lean: lettersAt Z (Johnson/Desc/Kinds/HeadDoorAtZ.lean) IS
lettersBy (Johnson/Desc/Kinds/HeadDoorBy.lean) at Z's three lists of sendings, Z's request's shape
and the table of counts of roots read off Z.D. Theorems. No Mathlib.

What is proved.
  flatMap_same     two functions that agree on a list's members give one flatMap.
  getD_map_zipIdx  at a member (a, i) of l.zipIdx: (l.map f).getD i 0 = f a.
  planSeats_by, chainSeats_by, planSeatsAll_by   the three seat functions are seatsBy,
          chainSeatsBy, seatsAllBy at rootsOf's lists.
  **lettersAt_by**   lettersAt Z = lettersBy Z.made.proof Z.first.shape (rootsOf Z.made.proof Z.D).

No existential quantifier. For all Z. Nothing on soundness.

-/
import Johnson.Desc.Kinds.HeadDoorBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open P5T (PSeat rootsBefore planSeats chainSeats planSeatsAll)
open Johnson.G (ChainSends)

theorem flatMap_same {α β : Type} (F G : α → List β) :
    ∀ (l : List α), (∀ x ∈ l, F x = G x) → l.flatMap F = l.flatMap G
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      flatMap_same F G l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem getD_map_zipIdx {α : Type} (l : List α) (f : α → Nat) {x : α × Nat}
    (hx : x ∈ l.zipIdx) : (l.map f).getD x.2 0 = f x.1 := by
  have h := List.mem_zipIdx_iff_getElem?.1 hx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

theorem planSeats_by (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) :
    planSeats Z dl = seatsBy Z.made.proof.1 Z.first.shape
      (Z.made.proof.1.sends.map fun s => rootsBefore dl (s.entry - 1)) := by
  unfold planSeats seatsBy
  refine flatMap_same _ _ _ fun s hs => ?_
  have e : (Z.made.proof.1.sends.map fun s => rootsBefore dl (s.entry - 1)).getD s.2 0 =
      rootsBefore dl (s.1.entry - 1) := getD_map_zipIdx _ _ hs
  dsimp only
  cases OnBytes.layTrees Z.made.proof.1.codes s.1.sent.toArray with
  | none => rfl
  | some lay =>
    dsimp only
    rw [e]
    rfl

theorem chainSeats_by (chain base : Nat) (c : ChainSends) (dl : List Fmt.DeclaredRound) :
    chainSeats chain base c dl =
      chainSeatsBy chain base c (c.sends.map fun s => rootsBefore dl (s.entry - 1)) := by
  unfold chainSeats chainSeatsBy
  refine flatMap_same _ _ _ fun s hs => ?_
  have e : (c.sends.map fun s => rootsBefore dl (s.entry - 1)).getD s.2 0 =
      rootsBefore dl (s.1.entry - 1) := getD_map_zipIdx _ _ hs
  cases OnBytes.layTrees c.codes s.1.sent.toArray with
  | none => rfl
  | some lay =>
    dsimp only
    rw [e]

theorem planSeatsAll_by (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) :
    planSeatsAll Z D = seatsAllBy Z.made.proof Z.first.shape (rootsOf Z.made.proof D) := by
  unfold planSeatsAll seatsAllBy rootsOf
  dsimp only
  rw [planSeats_by, chainSeats_by, chainSeats_by]

/-- **The five arguments are a function of the sendings, the shape and the table.** -/
theorem lettersAt_by (Z : ProofFile.Pub) :
    lettersAt Z = lettersBy Z.made.proof Z.first.shape (rootsOf Z.made.proof Z.D) := by
  unfold lettersAt lettersBy
  rw [planSeatsAll_by, planSeats_by]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.flatMap_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.getD_map_zipIdx
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planSeats_by
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.chainSeats_by
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planSeatsAll_by
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.lettersAt_by
