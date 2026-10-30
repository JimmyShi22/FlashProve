-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Leaves/HasK7.lean: WHERE THE DRIVER MAKES A FIRST CHAIN, A BLOCK STANDS AT A
PLACE OF THE KIND K7: by the driver's own table of places (`flat_places`,
Johnson/Desc/First/Driver/PlacesLaw.lean) and its test on the list of parts (`linksOk`: the list
ends with the head, whose segment opens with K7).
  `mem_zipIdx_of_mem`: a member of a list stands in the numbered list.
  `firstChain_linksOk`: a first chain is made only where `linksOk` says yes.
  `flatPlaces_has_K7`: then the table holds a place of the kind K7.
  `firstChain_has_K7`: so the flat list holds a block at such a place.
Limits. A fact on places. It does not say that there is just one.

-/
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

theorem mem_zipIdx_of_mem {α : Type} (x : α) : ∀ (l : List α) (n : Nat), x ∈ l →
    ∃ i, (x, i) ∈ l.zipIdx n
  | [], _, h => by cases h
  | a :: l, n, h => by
    rw [List.zipIdx_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨n, List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := mem_zipIdx_of_mem x l (n + 1) h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

variable {S Cl : Type}

theorem firstChain_linksOk {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) : linksOk links = true := by
  unfold firstChain at h
  obtain ⟨c₀, h₀, _⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h₀
  simp only [Option.bind_eq_bind, Option.pure_def] at h₀
  split at h₀
  · cases h₀
  · rename_i hn
    simpa using hn

theorem flatPlaces_has_K7 (links : List ModelPart) (several : Bool) (h : linksOk links = true) :
    ∃ a ∈ flatPlacesOf links several, a.kind = .K7 := by
  unfold linksOk at h
  have h1 : links.getLast? = some ModelPart.head := eq_of_beq (Bool.and_eq_true_iff.1 h).1
  obtain ⟨i, hi⟩ := mem_zipIdx_of_mem ModelPart.head links 0 (List.mem_of_getLast? h1)
  refine ⟨⟨1, some i, 1, .K7⟩, ?_, rfl⟩
  unfold flatPlacesOf
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_flatMap.2 ⟨(ModelPart.head, i), hi, ?_⟩)))
  unfold linkPlaces
  dsimp only
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ ?_)))
  unfold addresses
  exact List.mem_map.2 ⟨(.K7, 0), List.mem_cons_self, rfl⟩

/-- **Where the driver makes a first chain, a block stands at a place of the kind K7.** -/
theorem firstChain_has_K7 {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) : ∃ b ∈ c.blocksInOrder, b.place.kind = .K7 := by
  obtain ⟨a, ha, hk⟩ := flatPlaces_has_K7 links several (firstChain_linksOk h)
  rw [← flat_places H links several c h] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  exact ⟨b, hb, hk⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.firstChain_has_K7
