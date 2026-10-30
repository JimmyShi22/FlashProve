-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontLength.lean: how many entries of the first chain's flat list stand in
front of the entries behind the last segment: 14 for each segment, 2 more for the head's, and the
chain's first entry: (frontOf c).length = 14 · (the number of segments) + 3. At 25 segments: 353. A
law file; no running text imports it.

  `linkPlaces_length`   a segment's flat list has 14 places; the head's has 16.
  `sum_places`      over a list of parts that ends with the head and has no other head.
  `firstChain_back_length`   the driver's chain has as many entries behind the last segment as
                    `backKinds` names.
  `frontOf_length`  at every chain that the driver makes.
  `frontOf_353`     at 25 segments.
Limits. That the plan at hand has 25 segments is a premise. Nothing on soundness or on hiding.

-/
import Johnson.Goal.Meaning.KeepsDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open Meaning.K2 (frontOf backOf flat_eq firstChain_noFront)

variable {S Cl : Type}

theorem linkPlaces_length (l : Nat) (sub : ModelPart) :
    (linkPlaces l sub).length = 14 + if sub = .head then 2 else 0 := by
  unfold linkPlaces
  simp only [List.length_cons, List.length_append, List.length_nil, length_addresses]
  unfold closeAddresses closeKinds
  simp only [List.length_map, List.length_zipIdx, List.length_cons, List.length_nil]
  cases sub <;> cases (l == 0) <;> rfl

/-- The places of the segments, counted: general in the number of the first. -/
theorem places_length : ∀ (links : List ModelPart) (n : Nat),
    ((links.zipIdx n).flatMap fun x => linkPlaces x.2 x.1).length =
      14 * links.length + 2 * (links.filter (· == .head)).length
  | [], _ => rfl
  | sub :: rest, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, places_length rest (n + 1),
      linkPlaces_length]
    cases sub <;> simp <;> omega

/-- A list of parts that ends with the head and has no other head has one head. -/
theorem one_head {links : List ModelPart} (h : linksOk links = true) :
    (links.filter (· == .head)).length = 1 := by
  unfold linksOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hl : links.getLast? = some .head := eq_of_beq h1
  have e : links = links.dropLast ++ [.head] := by
    obtain ⟨hne, hlast⟩ := List.getLast?_eq_some_iff.1 hl
    rw [hlast]
    simp
  rw [e, List.filter_append]
  have h0 : (links.dropLast.filter (· == ModelPart.head)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    have := List.all_eq_true.1 h2 a ha
    simpa using this
  rw [h0]
  rfl

theorem firstChain_facts {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) :
    linksOk links = true ∧ c.back.length = (backKinds several).length := by
  unfold firstChain at h
  obtain ⟨c₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  rename_i hok
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, -, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, hk, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  refine ⟨by simpa using hok, ?_⟩
  show (back.map _).length = _
  rw [List.length_map, length_of_mapM H _ _ hk, length_addresses]

/-- **The number of entries in front of the entries behind the last segment.** -/
theorem frontOf_length {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) : (frontOf c).length = 14 * links.length + 3 := by
  obtain ⟨hok, hb⟩ := firstChain_facts h
  have e := congrArg List.length (flat_places H links several c h)
  rw [List.length_map, flat_eq (firstChain_noFront h), List.length_append] at e
  unfold flatPlacesOf backOf at e
  simp only [List.length_cons, List.length_append, List.length_nil, List.length_map,
    length_addresses, hb] at e
  have p := places_length links 0
  rw [one_head hok] at p
  have p' : (links.zipIdx.flatMap fun x => linkPlaces x.2 x.1).length = 14 * links.length + 2 * 1 :=
    p
  omega

theorem frontOf_353 {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) (h25 : links.length = 25) :
    (frontOf c).length = 353 := by
  rw [frontOf_length h, h25]

end VerifiableInference.Desc.Keeps1

#print axioms VerifiableInference.Desc.Keeps1.frontOf_length
#print axioms VerifiableInference.Desc.Keeps1.frontOf_353
