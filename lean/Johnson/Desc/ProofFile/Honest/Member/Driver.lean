--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/Driver.lean: what a member of the driver's first chain is, as a
term: general in the type of states, the type of claims and the driver's structure H. Statements
with their proofs.

The library says which sub-protocol stands where in the driver's chain (`linkAt_shape`,
`firstChain_shape`, Johnson/Desc/First/Link/Law/Shape.lean), and walks the flat list for names and
places (`chain_walk`, `link_walk`, Johnson/IMR/DriverWalk.lean). Here the same walk hands out the
member itself: a member that is of a kind is what H gives at the member's own place, with the place
written in, behind the guard on the reply, as `Chain.blocksInOrder` lays it.
Main names:
  `AsFlat.fields`: what `Chain.blocksInOrder` leaves of a sub-protocol: all but its test on the plan.
  `link_member`: every member of a segment's flat list that is of a kind.
  `chain_member`: **every member of the first chain's flat list that is of a kind**: what H gives as
    a sub-protocol at its place (in a segment: that term itself, with no further test on the plan);
    or, at a place of the kind K9, what H gives there as the batching of the segment's claims, at
    some gatherer.
  `mem_flat_of_hear`: a hearing sub-protocol of a segment, by index, is a member of the flat list.
  `last_member`: the one member of the kind `frame` outside the segments whose piece is not 0 is the
    chain's last sub-protocol.

What is not claimed. Nothing on the other members of the kind `frame`. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.Member.Statement
import Johnson.IMR.DriverWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (ModelPart Blocks firstChain linkAt blockAt hearsReply)

variable {σ C : Type}

/-- What `Chain.blocksInOrder` leaves of a sub-protocol. -/
theorem AsFlat.fields {x m : Block σ C} (h : AsFlat x m) :
    m.place = x.place ∧ m.name = x.name ∧ m.rounds = x.rounds ∧ m.oracles = x.oracles ∧
      m.before = x.before ∧ m.decide = x.decide ∧ m.claims = x.claims ∧ m.after = x.after := by
  rcases h with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What the driver fetches at a place: what H gives there, with the place written in. -/
theorem blockAt_eq {H : Blocks σ C} {a : Place} {y : Block σ C} (h : blockAt H a = some y) :
    ∃ b, H.block a = some b ∧ y = { b with place := a } := by
  unfold blockAt at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨b, hb, rfl⟩

/-- **Every member of a segment's flat list that is of a kind.** -/
theorem link_member {H : Blocks σ C} {l : Nat} {sub : ModelPart} {Lk : Link σ C}
    (h : linkAt H l sub = some Lk) (same : σ → σ → Bool) {x : Block σ C}
    (hx : x ∈ (Lk.guarded same hearsReply).blocksInOrder) (hk : x.place.kind ≠ KindName.frame) :
    (∃ b, H.block x.place = some b ∧
        x = Block.guarded same hearsReply { b with place := x.place }) ∨
      (x.place.kind = KindName.K9 ∧ ∃ mk g, H.batch x.place = some mk ∧
        x = Block.guarded same hearsReply { mk g with place := x.place }) := by
  obtain ⟨-, hh, ⟨batch, hbt, ebt⟩, hcl, -⟩ := VerifiableInference.Desc.Shape.linkAt_shape h
  unfold Link.blocksInOrder Link.guarded at hx
  dsimp only at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd rfl hk
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, _, e⟩ := IM.mem_of_map_some hh hy
          obtain ⟨b, hb, rfl⟩ := blockAt_eq e
          exact Or.inl ⟨b, hb, rfl⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · rw [ebt] at hk ⊢
          exact Or.inr ⟨rfl, batch, _, hbt, rfl⟩
        · obtain rfl := List.mem_singleton.1 hx
          exact absurd rfl hk
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨a, _, e⟩ := IM.mem_of_map_some hcl hy
      obtain ⟨b, hb, rfl⟩ := blockAt_eq e
      exact Or.inl ⟨b, hb, rfl⟩
  · obtain rfl := List.mem_singleton.1 hx
    exact absurd rfl hk

/-- **Every member of the first chain's flat list that is of a kind.** -/
theorem chain_member {H : Blocks σ C} {links : List ModelPart} {several : Bool} {c : Chain σ C}
    (h : firstChain H links several = some c) {x : Block σ C} (hx : x ∈ c.blocksInOrder)
    (hk : x.place.kind ≠ KindName.frame) :
    (∃ b, H.block x.place = some b ∧
        AsFlat (Block.guarded H.same hearsReply { b with place := x.place }) x ∧
        (x.place.link ≠ none → x = Block.guarded H.same hearsReply { b with place := x.place })) ∨
      (x.place.kind = KindName.K9 ∧ ∃ mk g, H.batch x.place = some mk ∧
        AsFlat (Block.guarded H.same hearsReply { mk g with place := x.place }) x) := by
  obtain ⟨-, c0, ⟨hfirst, hfront, hls, hbk, hlast⟩, rfl⟩ :=
    VerifiableInference.Desc.Shape.firstChain_shape h
  unfold Chain.blocksInOrder Chain.guarded at hx
  dsimp only at hx
  rw [hfront, hfirst, hlast] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd rfl hk
        · cases hx
      · obtain ⟨Lg, hLg, hx⟩ := List.mem_flatMap.1 hx
        obtain ⟨Lk, hLk, rfl⟩ := List.mem_map.1 hLg
        obtain ⟨a, _, e⟩ := IM.mem_of_map_some hls hLk
        rcases link_member e H.same hx hk with ⟨b, hb, e'⟩ | ⟨h9, mk, g, hmk, e'⟩
        · exact Or.inl ⟨b, hb, Or.inl e', fun _ => e'⟩
        · exact Or.inr ⟨h9, mk, g, hmk, Or.inl e'⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
      obtain ⟨a, ha, e⟩ := IM.mem_of_map_some hbk hy0
      obtain ⟨b, hb, rfl⟩ := blockAt_eq e
      exact Or.inl ⟨b, hb, Or.inr rfl, fun hn => absurd (IM.address_kind ha).2 hn⟩
  · obtain rfl := List.mem_singleton.1 hx
    exact absurd rfl hk

/-- A hearing sub-protocol of a segment of the chain is a member of the flat list. -/
theorem mem_flat_of_hear {c : Chain σ C} {l i : Nat} {Lk : Link σ C} {b : Block σ C}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) : b ∈ c.blocksInOrder := by
  have hb : b ∈ Lk.blocksInOrder := by
    unfold Link.blocksInOrder
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_of_getElem? h2))))
  unfold Chain.blocksInOrder
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨Lk, List.mem_of_getElem? h1, hb⟩)))

/-- **The one member of the kind `frame` outside the segments whose piece is not 0** is the chain's
last sub-protocol, as `Chain.blocksInOrder` lays it. -/
theorem last_member {H : Blocks σ C} {links : List ModelPart} {several : Bool} {c : Chain σ C}
    (h : firstChain H links several = some c) {x : Block σ C} (hx : x ∈ c.blocksInOrder)
    (hk : x.place.kind = KindName.frame) (hl : x.place.link = none) (hp : x.place.piece ≠ 0) :
    x = { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter } := by
  obtain ⟨-, c0, ⟨hfirst, hfront, hls, hbk, -⟩, rfl⟩ :=
    VerifiableInference.Desc.Shape.firstChain_shape h
  unfold Chain.blocksInOrder at hx
  dsimp only at hx
  rcases List.mem_append.1 hx with hx | hx
  · exfalso
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · have e : (c0.guarded H.same hearsReply).first.place = c0.first.place := rfl
          have hp' : (c0.guarded H.same hearsReply).first.place.piece ≠ 0 := hp
          rw [e, hfirst] at hp'
          exact hp' rfl
        · have e : (c0.guarded H.same hearsReply).front = c0.front.map _ := rfl
          rw [e, hfront] at hx
          cases hx
      · obtain ⟨Lg, hLg, hx⟩ := List.mem_flatMap.1 hx
        obtain ⟨Lk, hLk, rfl⟩ := List.mem_map.1 hLg
        obtain ⟨a, _, e⟩ := IM.mem_of_map_some hls hLk
        rcases IM.link_walk e H.same hearsReply hx with
          ⟨_, _, _, _, q⟩ | ⟨_, _, _, _, q⟩ | ⟨_, q, _⟩
        · rw [hl] at q
          cases q
        · rw [q] at hl
          cases hl
        · have q' : x.place.link = some a.2 := q
          rw [hl] at q'
          cases q'
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
      obtain ⟨a, ha, e⟩ := IM.mem_of_map_some hbk hy0
      obtain ⟨b, _, rfl⟩ := blockAt_eq e
      have hk' : a.kind = KindName.frame := hk
      have hin := (IM.address_kind ha).1
      rw [hk'] at hin
      revert hin
      cases several <;> decide
  · exact List.mem_singleton.1 hx

end ProofFile.Honest.AtPlace

#print axioms ProofFile.Honest.AtPlace.AsFlat.fields
#print axioms ProofFile.Honest.AtPlace.blockAt_eq
#print axioms ProofFile.Honest.AtPlace.link_member
#print axioms ProofFile.Honest.AtPlace.chain_member
#print axioms ProofFile.Honest.AtPlace.mem_flat_of_hear
#print axioms ProofFile.Honest.AtPlace.last_member
