-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatGuardHears.lean: THE ROW THAT LAYS, BEHIND THE GUARD (Johnson/Desc/SeatGuard.lean): "every block of the guarded chain's flat list that stands at a place told apart hears once", FROM THE UNGUARDED CHAIN's PARTS; and the
guarded flat list's places.

Why. Chain.guarded_flat (SeatGuardLaws.lean) pays every block but those at the places that but names. At these the block's own decision stands: so what is owed there is owed by the block that was handed in (guarded_under). But the flat list
also holds the blocks that Link.blocksInOrder makes, and the batching: that NONE OF THEM stands at a place told apart is a fact on places, not on texts.

  Link.HearsAt, Chain.HearsAt: THE DEBT: each block of first | front | hear | close | back | last at a place that but names hears once (Block.HearsOnce r, HearsOnce.lean); the batching's place and the places of kind "frame" are not told apart.
  **Chain.HearsAt.guarded_flat**: then every block of (c.guarded same but).blocksInOrder at a place that but names hears once.
  **Chain.guarded_places**: (c.guarded same but).blocksInOrder.map (·.place) = c.blocksInOrder.map (·.place), where no batching's place hangs on the function that it is handed: so a law on the unguarded chain's places (the driver's flat_places) crosses by one rewrite.

Silly members. but := fun _ => false: the debt is met for nothing and the first law says nothing. but := fun _ => true: the debt fails at the first link ("frame").
Every "there is", walked: no statement has one.
Limits. Rules: shown of no chain of the protocol. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.Sound.SeatGuardLaws
import Johnson.Desc.Sound.SeatGuardFaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl β : Type}

/-- What a link's parts owe for the places told apart. -/
structure Link.HearsAt (r : S → Option β) (but : Place → Bool) (L : Link S Cl) : Prop where
  hear : ∀ b ∈ L.hear, but b.place = true → b.HearsOnce r
  close : ∀ b ∈ L.close, but b.place = true → b.HearsOnce r
  batch : ∀ f, but (L.batch f).place = false
  frame : ∀ i, but ⟨L.chain, some L.number, i, .frame⟩ = false

/-- What a chain's parts owe for the places told apart. -/
structure Chain.HearsAt (r : S → Option β) (but : Place → Bool) (c : Chain S Cl) : Prop where
  first : but c.first.place = true → c.first.HearsOnce r
  front : ∀ b ∈ c.front, but b.place = true → b.HearsOnce r
  links : ∀ L ∈ c.links, L.HearsAt r but
  back : ∀ b ∈ c.back, but b.place = true → b.HearsOnce r
  last : but c.last.place = true → c.last.HearsOnce r

section
variable {r : S → Option β} {but : Place → Bool} (same : S → S → Bool)

/-- One block: behind the guard it hears once if it did. -/
theorem guarded_hearsOnce (b : Block S Cl) (h : but b.place = true → b.HearsOnce r)
    (hp : but (b.guarded same but).place = true) : (b.guarded same but).HearsOnce r :=
  hearsOnce_of_under (guarded_under same but b) (h hp)

theorem Link.HearsAt.guarded_flat {L : Link S Cl} (H : L.HearsAt r but) :
    ∀ b ∈ (L.guarded same but).blocksInOrder, but b.place = true → b.HearsOnce r := by
  intro b hb hp
  unfold Link.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.cons_append, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | ((hb | rfl | rfl) | hb) | rfl
  · have hp' : but ⟨L.chain, some L.number, 0, .frame⟩ = true := hp
    rw [H.frame] at hp'
    exact nomatch hp'
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_hearsOnce same b₀ (H.hear b₀ h₀) hp
  · have hp' : but (L.batch _).place = true := hp
    rw [H.batch] at hp'
    exact nomatch hp'
  · have hp' : but ⟨L.chain, some L.number, (L.guarded same but).hear.length + 2, .frame⟩ = true := hp
    rw [H.frame] at hp'
    exact nomatch hp'
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_hearsOnce same b₀ (H.close b₀ h₀) hp
  · have hp' : but ⟨L.chain, some L.number,
        (L.guarded same but).hear.length + (L.guarded same but).close.length + 3, .frame⟩ = true := hp
    rw [H.frame] at hp'
    exact nomatch hp'

/-- **Behind the guard, every block at a place told apart hears once.** -/
theorem Chain.HearsAt.guarded_flat {c : Chain S Cl} (H : c.HearsAt r but) :
    ∀ b ∈ (c.guarded same but).blocksInOrder, but b.place = true → b.HearsOnce r := by
  intro b hb hp
  unfold Chain.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap, List.cons_append,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | (((⟨p, hq, rfl⟩ | ⟨L, hL, hb⟩) | ⟨p, hq, rfl⟩) | rfl)
  · exact fun s rs gs s' D => guarded_hearsOnce same c.first H.first hp s rs gs s' D
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hq
    exact fun s rs gs s' D => guarded_hearsOnce same b₀ (H.front b₀ h₀) hp s rs gs s' D
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact (H.links L₀ h₀).guarded_flat same b hb hp
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hq
    exact fun s rs gs s' D => guarded_hearsOnce same b₀ (H.back b₀ h₀) hp s rs gs s' D
  · exact fun s rs gs s' D => guarded_hearsOnce same c.last H.last hp s rs gs s' D

/-- **The guarded flat list's places are the chain's**, by the faces. -/
theorem Chain.guarded_places (but : Place → Bool) (c : Chain S Cl) (hb : ∀ L ∈ c.links, L.BatchFace) :
    (c.guarded same but).blocksInOrder.map (·.place) = c.blocksInOrder.map (·.place) := by
  have e := congrArg (List.map fun x => x.2.1) (Chain.guarded_faces same but c hb)
  rw [List.map_map, List.map_map] at e
  exact e

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.guarded_hearsOnce
#print axioms VerifiableInference.Desc.Link.HearsAt.guarded_flat
#print axioms VerifiableInference.Desc.Chain.HearsAt.guarded_flat
#print axioms VerifiableInference.Desc.Chain.guarded_places
