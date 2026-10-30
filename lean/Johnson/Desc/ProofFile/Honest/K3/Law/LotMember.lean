-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LotMember.lean: small links between the sub-protocols
that the lookups' lot gives a proof file's description (`K3Lot.lot`,
Johnson/Desc/ProofFile/Lot/K3.lean) and what the honest side's theorems speak of. Theorems.

Terms. Honest/K3/GLOSSARY.md ("address", "description", "lot", "member", "sub-protocol").

What is shown.
  `lot_blocks`: the lot's sub-protocols, as the description's makers read them (`Lot.blocks`), are
    `K3Lot.hear Z`: it has no sub-protocol that states no claims.
  `lookAt_link`, `placeAt_link`: the place's parameters bear the link's number at which they were
    asked.
  `theOwn_place`, `theWhole_place`, `theStated_place`: the sub-protocol at an address bears that
    address as its place.
  `lot_block_at`: every sub-protocol of the lot stands at an address of the lot's list, bears it as
    its place, and has the rounds of the verifier's own parameters there.
  `reads_none`, `lot_reads_none`: a lookup's rounds open nothing: the frame's list of what is read
    in them is empty, and the columns are filled: none.
Four of them state what a theorem of the library's states under the same short name: `lookAt_link`,
`theOwn_place` and `theStated_place` (`IM.…`, Johnson/IMR/K3Seat.lean) and `placeAt_link`
(Johnson/Road/K4/Riders/PlanTests.lean). `reads_none` says what `readsOf_plain`
(Honest/K3/Law/Top.lean) says.

Hypotheses that remain. `h`: in the five theorems on a link and a place: the function returns at the
address; in `lot_block_at` and `lot_reads_none`: b is one of the lot's sub-protocols.

Users. A theorem on the description's own member at a lookup's place goes from the member to "a
sub-protocol of a lot at that place"; the theorems of Honest/K3/LotLaw.lean begin at "a sub-protocol
of K3Lot.hear Z". These are the links between; and the frame asks, beside the play, that the columns
read in the member's rounds can be filled. This file is imported by Honest/K3/Law/MemberAtSite.lean
and Honest/K3/Law/StatedAtLot.lean [not in this library].

Limits. They speak of the lot's sub-protocols: that the description's member at the place has the
rounds of the lot's sub-protocol is shown in other files (Honest/Member/).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt lookAt)
open VerifiableInference.Desc.K3 (pieceAt theOwn theWhole theStated)

/-- The lot's sub-protocols, as the description's makers read them. -/
theorem lot_blocks (Z : Pub) (G : Ground) : (K3Lot.lot Z).blocks G = K3Lot.hear Z := rfl

theorem lookAt_link {X : OnBytes.Model.Verify.Public} {i : Nat} {d : Bool}
    {x : VerifiableInference.Desc.First.Look.Place} (h : lookAt X i d = some x) : x.link = i := by
  unfold lookAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (obtain rfl := Option.some.inj h
       rfl)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
       rfl)
    | (obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
       obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
       rfl)
    | (obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
       obtain rfl := Option.some.inj h
       rfl)

theorem placeAt_link {X : OnBytes.Model.Verify.Public} {i : Nat} {d : Bool}
    {p : VerifiableInference.Desc.First.Look.P} (h : placeAt X i d = some p) : p.link = i := by
  unfold placeAt at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact lookAt_link hx

theorem theOwn_place {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theOwn claim runs X codes shape a = some b) :
    b.place = a := by
  unfold theOwn at h
  split at h
  · exact nomatch h
  · rename_i hck
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, hpl, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      obtain ⟨c, l, pc, k⟩ := a
      simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, not_or, not_not] at hck
      simp only at hi
      obtain ⟨rfl, rfl⟩ := hck
      subst hi
      rw [← placeAt_link hpl]
      cases runs <;> rfl

theorem theWhole_place {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theWhole claim runs X codes shape a = some b) :
    b.place = a := by
  unfold theWhole at h
  obtain ⟨b₀, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have := theOwn_place claim runs X codes shape a b₀ hb
  split
  · exact this
  · exact this

theorem theStated_place {Cl : Type} (claim : OnBytes.Model.Aff → Cl)
    (readers : Nat → Option (VerifiableInference.Desc.K3.Readers S))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theStated claim readers X codes shape a = some b) :
    b.place = a := by
  unfold theStated at h
  obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.1 h
  have h4 := theWhole_place claim true X codes shape a b₀ hb
  split at h
  · obtain rfl := Option.some.inj h
    exact h4
  · split at h
    · obtain rfl := Option.some.inj h
      exact h4
    · split at h
      · obtain rfl := Option.some.inj h
        exact h4
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact h4

/-- **Every sub-protocol of the lot stands at an address of the lot's list, bears it as its place,
and has the rounds of the verifier's own parameters there.** -/
theorem lot_block_at (Z : Pub) (G : Ground) (b : Block S Cl) (h : b ∈ (K3Lot.lot Z).blocks G) :
    ∃ x ∈ K3Lot.addresses Z, b.place = x.2.2 ∧ FromPlace Z.p.X x.2.2 b := by
  rw [lot_blocks] at h
  unfold K3Lot.hear at h
  obtain ⟨x, hx, hb⟩ := List.mem_filterMap.1 h
  exact ⟨x, hx, theStated_place _ _ _ _ _ _ b hb, theStated_from _ _ _ _ _ _ b hb⟩

/-- Rounds that are made of entries alone open nothing. -/
theorem reads_none (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
    readsOf chain ft stored tree (es.map fun e => { entry := e }) ds = []
  | [], _ => by simp [readsOf]
  | _ :: _, [] => by simp [readsOf]
  | _ :: es, _ :: ds => by
    simp only [List.map_cons, readsOf, List.flatMap_nil, List.nil_append]
    exact reads_none chain ft stored tree es ds

/-- **A lookup's rounds open nothing**: nothing is read in them, and the columns are filled: none.
-/
theorem lot_reads_none (Z : Pub) (G : Ground) (b : Block S Cl) (h : b ∈ (K3Lot.lot Z).blocks G)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) (back : List
         VerifiableInference.Desc.OpenedColumn) :
    readsOf chain ft stored tree b.rounds ds = [] ∧
      fillCols (readsOf chain ft stored tree b.rounds ds) back = .ok [] := by
  obtain ⟨_, _, _, _, _, p, _, _, _, hr⟩ := lot_block_at Z G b h
  have e : readsOf chain ft stored tree b.rounds ds = [] := by
    rw [hr]
    exact reads_none chain ft stored tree _ ds
  exact ⟨e, by rw [e]; rfl⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.lot_blocks
#print axioms ProofFile.Honest.K3.Law.placeAt_link
#print axioms ProofFile.Honest.K3.Law.theStated_place
#print axioms ProofFile.Honest.K3.Law.lot_block_at
#print axioms ProofFile.Honest.K3.Law.lot_reads_none
#print axioms ProofFile.Honest.K3.Law.lookAt_link
#print axioms ProofFile.Honest.K3.Law.theOwn_place
#print axioms ProofFile.Honest.K3.Law.theWhole_place
#print axioms ProofFile.Honest.K3.Law.reads_none
