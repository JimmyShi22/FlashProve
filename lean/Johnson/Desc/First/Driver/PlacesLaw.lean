-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/PlacesLaw.lean: the places of the first chain's flat list are the driver's
table, whatever blocks the kinds supply.

Block.lean's table `wanted` has a row for every block of a chain's flat list: its place and its
number of rounds. `flatPlacesOf` (Johnson/Desc/First/Driver/Chain.lean) is the first chain's list of
places for that table, made of the list of parts alone. This file proves that it is the list of the
places of the blocks that `firstChain` lays, in their order. Statements and proofs.
Main names:
  `mapM_cons_some`, `map_of_mapM`, `flatMap_of_mapM`, `mem_of_mapM`: what a yes of mapM says of the
    list of values.
  `place_of_blockAt`, `places_of_mapM`, `length_of_mapM`: the blocks that the driver takes for a
    list of places stand at these places, and are as many. `length_addresses`: a list of kinds gives
    as many places.
  `link_places`, `bare_places`: where linkAt makes a segment, the places of its flat list are
    `linkPlaces`; where firstChainWithoutReplyGuard makes a chain, those of its flat list are `flatPlacesOf`.
  `guarded_map_places`, `guarded_link_places`: the guard of Johnson/Desc/SeatGuard.lean turns no
    place of a list of blocks, nor of a segment that linkAt has made.
  `flat_places`: where firstChain makes a chain, the places of its flat list are `flatPlacesOf`.
Limits. A place is a label that the driver writes into a block: the law says that the labels are the
table's, not which block bears a label. Nothing is proved on the numbers of rounds: `wantedOf` takes
them as an argument. Block.lean asks that its table `wanted` is made by other files, of another
writer, than those that write the blocks; whether the driver is that is not said here. No soundness
is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-- A yes of mapM, taken apart at the first member. -/
theorem mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (l : List α) (r : List β)
    (h : (a :: l).mapM f = some r) : ∃ b bs, f a = some b ∧ l.mapM f = some bs ∧ r = b :: bs := by
  rw [List.mapM_cons] at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact ⟨b, bs, hb, hbs, rfl⟩

/-- What holds of each member's value holds of the list of values. -/
theorem map_of_mapM {α β γ : Type} (f : α → Option β) (g : β → γ) (k : α → γ)
    (hk : ∀ a b, f a = some b → g b = k a) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.map g = l.map k
  | [], r, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, r, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_some f a l r h
    rw [List.map_cons, List.map_cons, hk a b hb, map_of_mapM f g k hk l bs hbs]

/-- The like for lists laid in a row. -/
theorem flatMap_of_mapM {α β γ : Type} (f : α → Option β) (g : β → List γ) (k : α → List γ)
    (hk : ∀ a b, f a = some b → g b = k a) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.flatMap g = l.flatMap k
  | [], r, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, r, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_some f a l r h
    rw [List.flatMap_cons, List.flatMap_cons, hk a b hb, flatMap_of_mapM f g k hk l bs hbs]

/-- Every value comes from a member. -/
theorem mem_of_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h => by
    rw [List.mapM_nil] at h
    cases h
    intro b hb
    cases hb
  | a :: l, r, h => by
    obtain ⟨b0, bs, hb0, hbs, rfl⟩ := mapM_cons_some f a l r h
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hb0⟩
    · obtain ⟨a', ha', e⟩ := mem_of_mapM f l bs hbs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', e⟩

variable {S Cl : Type}

/-- The block that the driver takes for a place stands at that place. -/
theorem place_of_blockAt (H : Blocks S Cl) (a : Place) (b : Block S Cl)
    (h : blockAt H a = some b) : b.place = a := by
  unfold blockAt at h
  obtain ⟨b0, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- The blocks that the driver takes for a list of places stand at these places. -/
theorem places_of_mapM (H : Blocks S Cl) (as : List Place) (bs : List (Block S Cl))
    (h : as.mapM (blockAt H) = some bs) : bs.map (·.place) = as := by
  rw [map_of_mapM (blockAt H) (·.place) id (place_of_blockAt H) as bs h, List.map_id]

/-- They are as many as the places. -/
theorem length_of_mapM (H : Blocks S Cl) (as : List Place) (bs : List (Block S Cl))
    (h : as.mapM (blockAt H) = some bs) : bs.length = as.length := by
  rw [← places_of_mapM H as bs h, List.length_map]

theorem length_addresses (link : Option Nat) (ks : List KindName) :
    (addresses link ks).length = ks.length := by
  unfold addresses
  rw [List.length_map, List.length_zipIdx]

/-- **The places of a segment's flat list are the table's.** -/
theorem link_places (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) : L.blocksInOrder.map (·.place) = linkPlaces l sub := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  have e1 := places_of_mapM H _ _ hh
  have e2 := places_of_mapM H _ _ hc
  have n1 : hear.length = (kindsBeforeBatching sub (l == 0)).length := by
    rw [length_of_mapM H _ _ hh, length_addresses]
  have n2 : close.length = closeKinds.length := by
    rw [length_of_mapM H _ _ hc]
    unfold closeAddresses
    rw [List.length_map, List.length_zipIdx]
  unfold Link.blocksInOrder linkPlaces
  simp only [List.map_cons, List.map_append, List.map_nil, e1, e2, n1, n2]
  rfl

/-- The places of the flat list of the chain without the scaffolding are the table's. -/
theorem bare_places (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (h : firstChainWithoutReplyGuard H links several = some c) :
    c.blocksInOrder.map (·.place) = flatPlacesOf links several := by
  unfold firstChainWithoutReplyGuard at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ls, hl, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨back, hb, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  have e1 : (ls.flatMap Link.blocksInOrder).map (·.place) =
      links.zipIdx.flatMap fun x => linkPlaces x.2 x.1 := by
    rw [List.map_flatMap]
    exact flatMap_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1)
      (fun L => L.blocksInOrder.map (·.place)) (fun x => linkPlaces x.2 x.1)
      (fun x L hx => link_places H x.2 x.1 L hx) _ _ hl
  have e2 := places_of_mapM H _ _ hb
  have n2 : back.length = (backKinds several).length := by
    rw [length_of_mapM H _ _ hb, length_addresses]
  unfold Chain.blocksInOrder flatPlacesOf
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_map, e1, n2]
  have e3 : back.map ((·.place) ∘ fun b : Block S Cl => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) =
      back.map (·.place) := rfl
  rw [e3, e2]
  rfl

/-- The guard turns no place: of a list of blocks. -/
theorem guarded_map_places (same : S → S → Bool) (but : Place → Bool) (bs : List (Block S Cl)) :
    (bs.map (Block.guarded same but)).map (·.place) = bs.map (·.place) := by
  rw [List.map_map]
  rfl

/-- The places of the flat list of a segment behind the guard are the table's. (The batching's place
is the one that linkAt writes, whatever function of the claims it is handed.) -/
theorem guarded_link_places (same : S → S → Bool) (but : Place → Bool) (H : Blocks S Cl) (l : Nat)
    (sub : ModelPart) (L : Link S Cl) (h : linkAt H l sub = some L) :
    (L.guarded same but).blocksInOrder.map (·.place) = linkPlaces l sub := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  have e1 := places_of_mapM H _ _ hh
  have e2 := places_of_mapM H _ _ hc
  have n1 : hear.length = (kindsBeforeBatching sub (l == 0)).length := by
    rw [length_of_mapM H _ _ hh, length_addresses]
  have n2 : close.length = closeKinds.length := by
    rw [length_of_mapM H _ _ hc]
    unfold closeAddresses
    rw [List.length_map, List.length_zipIdx]
  unfold Link.blocksInOrder Link.guarded linkPlaces
  simp only [List.map_cons, List.map_append, List.map_nil, guarded_map_places, List.length_map, e1,
    e2, n1, n2]
  rfl

/-- **The places of the first chain's flat list are the table's.** -/
theorem flat_places (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (h : firstChain H links several = some c) :
    c.blocksInOrder.map (·.place) = flatPlacesOf links several := by
  unfold firstChain at h
  obtain ⟨c0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, hl, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, hb, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  have e1 : ((ls.map (Link.guarded H.same hearsReply)).flatMap Link.blocksInOrder).map (·.place) =
      links.zipIdx.flatMap fun x => linkPlaces x.2 x.1 := by
    rw [List.map_flatMap, List.flatMap_map]
    exact flatMap_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1)
      (fun L => (L.guarded H.same hearsReply).blocksInOrder.map (·.place)) (fun x => linkPlaces x.2 x.1)
      (fun x L hx => guarded_link_places H.same hearsReply H x.2 x.1 L hx) _ _ hl
  have e2 := places_of_mapM H _ _ hb
  have n2 : back.length = (backKinds several).length := by
    rw [length_of_mapM H _ _ hb, length_addresses]
  unfold Chain.blocksInOrder Chain.guarded flatPlacesOf
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_map, e1, n2]
  have e3 : back.map ((·.place) ∘ (fun b : Block S Cl => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ∘
      Block.guarded H.same hearsReply) = back.map (·.place) := rfl
  rw [e3, e2]
  rfl

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.link_places
#print axioms VerifiableInference.Desc.First.bare_places
#print axioms VerifiableInference.Desc.First.guarded_link_places
#print axioms VerifiableInference.Desc.First.flat_places
