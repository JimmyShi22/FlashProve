-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/DriverWalk.lean: a law about the driver's chain, general in the record H of the kinds'
blocks: what every block of the flat list is: one walk.
Object. (firstChain H links several).blocksInOrder and (linkAt H l sub).guarded.blocksInOrder (Johnson/Desc/First/Driver/Chain.lean · Johnson/Desc/Block.lean · Johnson/Desc/SeatGuard.lean).
User. chainC_flat (Johnson/IMR/LaidFirst.lean) · shape_frame_names (Johnson/IMR/FrameSeat.lean) · flat_block_at (Johnson/IMR/SameSpot.lean). Letters. H : Blocks σ C · l, sub: a link's number and sort · n: the number of its hearing blocks.
Called, not typed: linkAt_shape · linkAt_length · firstChain_shape (Johnson/Desc/First/Link/Law/Shape.lean). That law does not say the link's name, chain and number: for these three fields linkAt's text is opened here, once.
It imports no Mathlib.

  no_frame_hears · address_kind · mem_of_map_some · blockAt_is   small things on the driver's tables.
  FrameName l n x   what a block of the kind «frame» in a link's flat list is called, by its piece (0: «link l: laid» · n + 2: «… behind the batching» · n + 6: «… cleared»).
  LinkMember H l n x   the three sorts: what the record gives at x's own place, under that name, of a kind, in link l · the record's batching at K9's address · one of Link.blocksInOrder's own three (FrameName).
  link_walk         every block of a driver's link's flat list, behind the guard, is a LinkMember.
  chain_walk        every block of the first chain's flat list: a LinkMember of a link of the row · or what the record gives at its own place behind the links · or the chain's first or last block (kind «frame», no link).

What is not claimed. Nothing on decisions, rounds or tests on the plan. No soundness.
-/
import Johnson.Desc.First.Link.Law.Shape
import Johnson.Desc.SeatGuard

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain Link Place KindName roundlessBlock)
open VerifiableInference.Desc.First (ModelPart Blocks firstChain linkAt blockAt kindsBeforeBatching addresses hearsReply
  closeAddresses closeKinds backKinds)

/-! ## 1 Small things on the driver's tables -/

theorem no_frame_hears (sub : ModelPart) (f : Bool) : KindName.frame ∉ kindsBeforeBatching sub f := by
  cases sub <;> cases f <;> decide

theorem address_kind {link : Option Nat} {ks : List KindName} {a : Place} (h : a ∈ addresses link ks) :
    a.kind ∈ ks ∧ a.link = link := by
  unfold addresses at h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  exact ⟨(List.mem_zipIdx hy).2.2 ▸ List.getElem_mem _, rfl⟩

/-- A member of a list that is given, member by member, as the values of a function that may give nothing. -/
theorem mem_of_map_some {α β : Type} {g : α → Option β} {xs : List β} {as : List α}
    (h : xs.map some = as.map g) {y : β} (hy : y ∈ xs) : ∃ a ∈ as, g a = some y := by
  have h1 : some y ∈ as.map g := h ▸ List.mem_map.2 ⟨y, hy, rfl⟩
  obtain ⟨a, ha, e⟩ := List.mem_map.1 h1
  exact ⟨a, ha, e⟩

/-- What the driver fetches at an address: the record's block there, with the address written in. -/
theorem blockAt_is {σ C : Type} {H : Blocks σ C} {a : Place} {y : Block σ C}
    (h : blockAt H a = some y) : ∃ b, H.block a = some b ∧ y.name = b.name ∧ y.place = a := by
  unfold blockAt at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨b, hb, rfl, rfl⟩

/-! ## 2 The walk through a link's flat list -/

/-- What a block of the kind «frame» in a link's flat list is called, by its piece. -/
def FrameName (l n : Nat) (x : String × Place) : Prop :=
  x.2.link = some l ∧
    ((x.2.piece = 0 ∧ x.1 = s!"link {l}" ++ ": laid") ∨
      (x.2.piece = n + 2 ∧ x.1 = s!"link {l}" ++ ": behind the batching") ∨
      (x.2.piece = n + 6 ∧ x.1 = s!"link {l}" ++ ": cleared"))

/-- The three sorts of block in the flat list of a driver's link number l with n hearing blocks. -/
def LinkMember {σ C : Type} (H : Blocks σ C) (l n : Nat) (x : Block σ C) : Prop :=
  (∃ b, H.block x.place = some b ∧ x.name = b.name ∧ x.place.kind ≠ KindName.frame ∧
      x.place.link = some l) ∨
    (∃ mk g, H.batch x.place = some mk ∧ x.name = (mk g).name ∧
      x.place = { chain := 1, link := some l, piece := n + 1, kind := .K9 }) ∨
    (x.place.kind = KindName.frame ∧ FrameName l n (x.name, x.place))

/-- **EVERY BLOCK OF A DRIVER's LINK's FLAT LIST, BEHIND THE GUARD**: what the record gives at the block's own place, under that name · or the record's batching at K9's address · or one of Link.blocksInOrder's own three, under the driver's name of the link.
(The link's make: linkAt_shape (Johnson/Desc/First/Link/Law/Shape.lean); THE LINK's NAME, CHAIN AND NUMBER are not in that law: for these linkAt's text is opened here, once.) -/
theorem link_walk {σ C : Type} {H : Blocks σ C} {l : Nat} {sub : ModelPart} {Lk : Link σ C}
    (h : linkAt H l sub = some Lk) (same : σ → σ → Bool) (but : Place → Bool) {x : Block σ C}
    (hx : x ∈ (Lk.guarded same but).blocksInOrder) :
    LinkMember H l (kindsBeforeBatching sub (l == 0)).length x := by
  obtain ⟨-, hh, ⟨batch, hbt, ebt⟩, hcl, -⟩ := VerifiableInference.Desc.Shape.linkAt_shape h
  have hlen := VerifiableInference.Desc.Shape.linkAt_length h
  have hclen : Lk.close.length = 3 := by
    have := congrArg List.length hcl
    simpa [closeAddresses, closeKinds] using this
  have hnm : Lk.name = s!"link {l}" ∧ Lk.chain = 1 ∧ Lk.number = l := by
    unfold linkAt at h
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨e1, e2, e3⟩ := hnm
  unfold Link.blocksInOrder Link.guarded at hx
  dsimp only at hx
  rw [e1, e2, e3] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr (Or.inr ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩)
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, ha, e⟩ := mem_of_map_some hh hy
          obtain ⟨b, hb, en, ep⟩ := blockAt_is e
          obtain ⟨hk, hl⟩ := address_kind ha
          refine Or.inl ⟨b, ?_, en, ?_, ?_⟩
          · show H.block y.place = some b
            rw [ep]
            exact hb
          · show y.place.kind ≠ _
            rw [ep]
            exact fun e' => no_frame_hears _ _ (e' ▸ hk)
          · show y.place.link = _
            rw [ep]
            exact hl
      · rcases List.mem_cons.1 hx with rfl | hx
        · refine Or.inr (Or.inl ⟨batch, VerifiableInference.Desc.claimsInBy Lk.each
            (Lk.hear.map (Block.guarded same but)) Lk.order, ?_, ?_, ?_⟩)
          · show H.batch (Lk.batch _).place = some batch
            rw [ebt]
            exact hbt
          · show (Lk.batch _).name = _
            rw [ebt]
          · show (Lk.batch _).place = _
            rw [ebt]
        · obtain rfl := List.mem_singleton.1 hx
          refine Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inl ⟨?_, rfl⟩)⟩)
          show (Lk.hear.map _).length + 2 = _
          rw [List.length_map, hlen]
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨a, ha, e⟩ := mem_of_map_some hcl hy
      obtain ⟨b, hb, en, ep⟩ := blockAt_is e
      have hka : a.kind ≠ KindName.frame ∧ a.link = some l := by
        unfold closeAddresses closeKinds at ha
        simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> exact ⟨(fun e => nomatch e), rfl⟩
      refine Or.inl ⟨b, ?_, en, ?_, ?_⟩
      · show H.block y.place = some b
        rw [ep]
        exact hb
      · show y.place.kind ≠ _
        rw [ep]
        exact hka.1
      · show y.place.link = _
        rw [ep]
        exact hka.2
  · obtain rfl := List.mem_singleton.1 hx
    refine Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inr ⟨?_, rfl⟩)⟩)
    show (Lk.hear.map _).length + (Lk.close.map _).length + 3 = _
    rw [List.length_map, List.length_map, hlen, hclen]

/-! ## 3 The walk through the chain's flat list -/

/-- **EVERY BLOCK OF THE DRIVER's FIRST CHAIN's FLAT LIST**: a member of a link of the row of links · or what the record gives at the block's own place behind the links · or the chain's first or last block, of the kind «frame», in no link. (Over
firstChain_shape.) -/
theorem chain_walk {σ C : Type} {H : Blocks σ C} {links : List ModelPart} {several : Bool} {c : Chain σ C}
    (h : firstChain H links several = some c) {x : Block σ C} (hx : x ∈ c.blocksInOrder) :
    (∃ l sub, links[l]? = some sub ∧ LinkMember H l (kindsBeforeBatching sub (l == 0)).length x) ∨
      (∃ b, H.block x.place = some b ∧ x.name = b.name ∧ x.place.kind ≠ KindName.frame ∧
        x.place.link = none) ∨
      (x.place.kind = KindName.frame ∧ x.place.link = none) := by
  obtain ⟨-, c0, ⟨hfirst, hfront, hls, hbk, hlast⟩, rfl⟩ :=
    VerifiableInference.Desc.Shape.firstChain_shape h
  unfold Chain.blocksInOrder Chain.guarded at hx
  dsimp only at hx
  rw [hfront, hfirst, hlast] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · cases hx
      · obtain ⟨Lg, hLg, hx⟩ := List.mem_flatMap.1 hx
        obtain ⟨Lk, hLk, rfl⟩ := List.mem_map.1 hLg
        obtain ⟨a, ha, e⟩ := mem_of_map_some hls hLk
        obtain ⟨sub, l⟩ := a
        have ha' : links[l]? = some sub := by
          simpa using (List.mk_mem_zipIdx_iff_getElem?.1 ha)
        exact Or.inl ⟨l, sub, ha', link_walk e _ _ hx⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
      obtain ⟨a, ha, e⟩ := mem_of_map_some hbk hy0
      obtain ⟨b, hb, en, ep⟩ := blockAt_is e
      obtain ⟨hk, hl⟩ := address_kind ha
      refine Or.inr (Or.inl ⟨b, ?_, en, ?_, ?_⟩)
      · show H.block y0.place = some b
        rw [ep]
        exact hb
      · show y0.place.kind ≠ _
        rw [ep]
        intro e'
        rw [e'] at hk
        revert hk
        cases several <;> decide
      · show y0.place.link = _
        rw [ep]
        exact hl
  · obtain rfl := List.mem_singleton.1 hx
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

end IM

#print axioms IM.link_walk
#print axioms IM.chain_walk
