-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/Shape.lean: THE SHAPE OF A SEGMENT AND OF THE FIRST CHAIN AS THE DRIVER
LAYS THEM (Johnson/Desc/First/Driver/Chain.lean: `linkAt`, `firstChainWithoutReplyGuard`,
`firstChain`), for every record H of the kinds' blocks: WHICH BLOCK STANDS WHERE. Theorems. Over
Block.lean and the driver with the guard as scaffolding.

Why. The law of a segment speaks of a `Link`; the description that runs is the flat list that the
driver makes of the kinds' blocks. That the labels (the places) of that list are the table's is the
driver's own law (Johnson/Desc/First/Driver/PlacesLaw.lean: `link_places`, `flat_places`),
which is called here, not typed again. The labels alone do not tell which block bears a label: a
driver that fetched every block at one address and wrote the right address into each would have all
the places. So the shape says of each field of the segment what it is made of.

What is said.
  `SegShape H l sub L`, `linkAt_shape`: **what the driver's segment is made of**: the places of its
    flat list (`linkPlaces`); each hearing block is what `blockAt H` returns at its own address; the
    batching is what the record returns at K9's address, with that address written in; the closing's
    three blocks are what `blockAt H` returns at `closeAddresses`; THE TWO ORDERS ARE THE
    PROTOCOL's, UNCUT; the tests behind each run and behind the adding are the record's; what starts
    and ends the segment is the record's.
  `ChainShape`, `bareChain_shape`: the like of the whole first chain in front of the scaffolding:
    the front; nothing else in front of the segments; each segment is `linkAt`'s at its number and
    sort; behind them what `blockAt H` returns at the addresses of `backKinds`; the seal.
    `firstChain_shape`: **the first chain has the table's places, and it is a chain of that make
    behind the guard** (`Chain.guarded H.same hearsReply`, Johnson/Desc/SeatGuard.lean).
  `LinkShapeRow`, `linkShapeRow`: both, for every record. `LinkShapeMember`, `linkShapeMember`: the
    driver does make a chain: of idle blocks, at three segments: 49 blocks.
  Controls. `swapped_places`: a flat list with the batching in front of the hearing blocks has not a
    segment's places. `silly_fails`: a driver that fetches every hearing block at the first address
    and writes the right address into each has all the places and fails `SegShape`. `swapped_fails`:
    so does one that exchanges two addresses before it writes the places in. `cut_fails`: **and so
    does one that cuts the order down to the runs that its blocks state**, as the driver once
    did: all places, every block where it belongs, an empty order. No control is shown at the
    batching, the closing, each | tests, lay | clear.
  The places of a segment with n hearing blocks (`linkPlaces`): the frame at 0 · the hearing blocks
    at 1 .. n · K9 at n + 1 · the frame at n + 2 · K9, K10, K9 at n + 3 .. n + 5 · the frame at n +
    6. Once lay, tests, the orders, the hearing blocks and clear are given, the three blocks that
    `Link.blocksInOrder` itself lays are determined too.

Limits. On what the driver lays, not on what the kinds' blocks do. What the guard does to a block, a
segment or a chain is left to Johnson/Desc/SeatGuard.lean; `linkAt`'s segment stands in
front of it. That a run goes by the chain that `firstChain` makes is not said here. The idle
record's segments fail Block.lean's test on the plan (their blocks state no run, and the order is
uncut): `linkShapeMember` says that a chain is made, not that it passes. Nothing on soundness.

-/
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Shape
open First (ModelPart Blocks kindsBeforeBatching backKinds closeAddresses addresses blockAt linkAt firstChainWithoutReplyGuard
  firstChain hearsReply linkPlaces flatPlacesOf frameAt orderOf orderAfterOf map_of_mapM link_places
  flat_places)

variable {S Cl : Type} {H : Blocks S Cl}

/-! ## 1 A segment -/

/-- **What the driver's segment is made of.** -/
def SegShape (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl) : Prop :=
  L.blocksInOrder.map (·.place) = linkPlaces l sub ∧
  L.hear.map some = (addresses (some l) (kindsBeforeBatching sub (l == 0))).map (blockAt H) ∧
  (∃ batch, H.batch ⟨1, some l, (kindsBeforeBatching sub (l == 0)).length + 1, .K9⟩ = some batch ∧
    L.batch = fun c =>
      { batch c with place := ⟨1, some l, (kindsBeforeBatching sub (l == 0)).length + 1, .K9⟩ }) ∧
  L.close.map some = (closeAddresses l (kindsBeforeBatching sub (l == 0)).length).map (blockAt H) ∧
  L.order = orderOf sub ∧ L.orderAfter = orderAfterOf sub ∧
  L.each = H.each l ∧ L.tests = H.tests l ∧
  L.lay = H.lay l ∧ L.clear = H.clear l

theorem linkAt_shape {l : Nat} {sub : ModelPart} {L : Link S Cl} (h : linkAt H l sub = some L) :
    SegShape H l sub L := by
  refine ⟨link_places H l sub L h, ?_⟩
  simp only [linkAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨hear, h1, batch, h2, close, h3, rfl⟩ := h
  exact ⟨map_of_mapM (blockAt H) some (blockAt H) (fun _ _ hb => hb.symm) _ _ h1,
    ⟨batch, h2, rfl⟩, map_of_mapM (blockAt H) some (blockAt H) (fun _ _ hb => hb.symm) _ _ h3,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- It has as many hearing blocks as `kindsBeforeBatching` lists. -/
theorem linkAt_length {l : Nat} {sub : ModelPart} {L : Link S Cl} (h : linkAt H l sub = some L) :
    L.hear.length = (kindsBeforeBatching sub (l == 0)).length := by
  have := congrArg List.length (linkAt_shape h).2.1
  simpa [First.length_addresses] using this

/-! ## 2 The whole first chain -/

/-- **What the driver's first chain is made of, in front of the scaffolding** (`firstChainWithoutReplyGuard`). -/
def ChainShape (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl) : Prop :=
  c.first = { H.first with place := frameAt none 0 } ∧ c.front = [] ∧
  c.links.map some = links.zipIdx.map (fun x => linkAt H x.2 x.1) ∧
  c.back.map some = (addresses none (backKinds several)).map (blockAt H) ∧
  c.last = { H.last with place := frameAt none ((backKinds several).length + 1) }

theorem bareChain_shape {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChainWithoutReplyGuard H links several = some c) : ChainShape H links several c := by
  unfold firstChainWithoutReplyGuard at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, ls, h1, back, h2, rfl⟩ := h
    have e3 : back.length = (backKinds several).length := by
      rw [First.length_of_mapM H _ _ h2, First.length_addresses]
    refine ⟨rfl, rfl, map_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) some
      (fun x => linkAt H x.2 x.1) (fun _ _ hb => hb.symm) _ _ h1,
      map_of_mapM (blockAt H) some (blockAt H) (fun _ _ hb => hb.symm) _ _ h2, ?_⟩
    show ({ H.last with place := ⟨1, none, back.length + 1, .frame⟩ } : Block S Cl) = _
    rw [e3]
    rfl

/-- **The first chain**: its places are the table's; and it is a chain of that make behind the
guard. -/
theorem firstChain_shape {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) :
    c.blocksInOrder.map (·.place) = flatPlacesOf links several ∧
      ∃ c₀, ChainShape H links several c₀ ∧ c = c₀.guarded H.same hearsReply := by
  refine ⟨flat_places H links several c h, ?_⟩
  unfold firstChain at h
  obtain ⟨c₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨c₀, bareChain_shape h0, rfl⟩

/-! ## 3 The row, a member, and controls -/

/-- **THE SHAPE OF WHAT THE DRIVER LAYS**, for every type of state and of claim and for every
record H of the kinds' blocks: a segment's flat list; the whole first chain's. -/
def LinkShapeRow : Prop :=
  ∀ (S Cl : Type) (H : Blocks S Cl),
    (∀ (l : Nat) (sub : ModelPart) (L : Link S Cl), linkAt H l sub = some L → SegShape H l sub L) ∧
    ∀ (links : List ModelPart) (several : Bool) (c : Chain S Cl), firstChain H links several = some c →
      c.blocksInOrder.map (·.place) = flatPlacesOf links several ∧
        ∃ c₀, ChainShape H links several c₀ ∧ c = c₀.guarded H.same hearsReply

theorem linkShapeRow : LinkShapeRow := fun _ _ _ =>
  ⟨fun _ _ _ h => linkAt_shape h, fun _ _ _ h => firstChain_shape h⟩

/-- A record of idle blocks. -/
def idleH : Blocks Unit Unit :=
  { block := fun _ => some (roundlessBlock "idle" 1 none 0 .ok)
    batch := fun _ => some fun _ => roundlessBlock "idle" 1 none 0 .ok
    lay := fun _ => .ok, clear := fun _ => .ok
    each := fun _ _ _ _ => .ok (), tests := fun _ _ => .ok (), same := fun _ _ => true
    first := roundlessBlock "idle" 1 none 0 .ok, last := roundlessBlock "idle" 1 none 0 .ok }

/-- **THE DRIVER DOES MAKE A CHAIN**: of that record, at a group of feed-forward layers, a group of
attention layers and the head: 14 + 14 + 16 blocks in the segments, 3 behind them, the front and the
seal. -/
def LinkShapeMember : Prop :=
  ∃ c, firstChain idleH [.layers, .attention, .head] false = some c ∧ c.blocksInOrder.length = 49

theorem linkShapeMember : LinkShapeMember := by
  have hs : (firstChain idleH [.layers, .attention, .head] false).isSome = true := rfl
  obtain ⟨c, h⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨c, h, ?_⟩
  have := congrArg List.length (flat_places idleH _ _ c h)
  rw [List.length_map] at this
  rw [this]
  decide

/-- A control: a flat list with the batching in front of the hearing blocks does not have a
segment's places: the idle record's first segment, with these two stretches exchanged. -/
theorem swapped_places : ∃ L, linkAt idleH 0 .layers = some L ∧
    (L.blocksInOrder.take 1 ++ (L.blocksInOrder.drop 8).take 1 ++ (L.blocksInOrder.drop 1).take 7 ++ L.blocksInOrder.drop 9).map
      (·.place) ≠ linkPlaces 0 .layers := by
  have hs : (linkAt idleH 0 .layers).isSome = true := rfl
  obtain ⟨L, h⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨L, h, ?_⟩
  simp only [List.map_append, List.map_take, List.map_drop, link_places idleH 0 .layers L h]
  decide

/-- A record whose block at the first address differs from the others, by its name. -/
def twoH : Blocks Unit Unit :=
  { idleH with
    block := fun a => some (roundlessBlock (if a.piece = 1 then "one" else "other") 1 none 0 .ok) }

/-- A silly driver: it fetches every hearing block at the segment's FIRST address, and writes the
right address into each. -/
def sillyAt (H : Blocks Unit Unit) (l : Nat) (sub : ModelPart) : Option (Link Unit Unit) :=
  (linkAt H l sub).map fun L =>
    { L with hear := L.hear.map fun b =>
        match H.block ⟨1, some l, 1, .K1⟩ with
        | some b0 => { b0 with place := b.place }
        | none => b }

/-- The name of a block that is there. -/
def nameOf (o : Option (Block Unit Unit)) : String := (o.map (·.name)).getD ""

/-- **A control: THE PLACES ALONE DO NOT TELL WHICH BLOCK STANDS WHERE**: the silly driver's segment
has all the places, and fails `SegShape`. -/
theorem silly_fails : ∃ L, sillyAt twoH 0 .layers = some L ∧
    L.blocksInOrder.map (·.place) = linkPlaces 0 .layers ∧ ¬ SegShape twoH 0 .layers L := by
  have hs : (sillyAt twoH 0 .layers).isSome = true := rfl
  obtain ⟨L, h⟩ := Option.isSome_iff_exists.1 hs
  have e1 : (sillyAt twoH 0 .layers).map (fun L => L.blocksInOrder.map (·.place)) =
      some (linkPlaces 0 .layers) := by decide
  have e2 : (sillyAt twoH 0 .layers).map (fun L => L.hear.map (·.name)) =
      some (List.replicate 7 "one") := by decide
  rw [h] at e1 e2
  refine ⟨L, h, Option.some.inj e1, fun hS => ?_⟩
  have e3 := congrArg (List.map nameOf) hS.2.1
  have e4 : (L.hear.map some).map nameOf = L.hear.map (·.name) := by
    rw [List.map_map]
    rfl
  have e2' : L.hear.map (·.name) = List.replicate 7 "one" := Option.some.inj e2
  rw [e4, e2'] at e3
  exact absurd e3 (by decide)

/-- A second silly driver: it fetches the first two hearing blocks at each other's addresses, and
writes the right address into each. -/
def swapAt (H : Blocks Unit Unit) (l : Nat) (sub : ModelPart) : Option (Link Unit Unit) :=
  (linkAt H l sub).map fun L =>
    { L with hear :=
        match L.hear with
        | a :: b :: t => { b with place := a.place } :: { a with place := b.place } :: t
        | t => t }

/-- **A control**: the driver that exchanges two addresses before the stamp has all the places, and
fails `SegShape`. -/
theorem swapped_fails : ∃ L, swapAt twoH 0 .layers = some L ∧
    L.blocksInOrder.map (·.place) = linkPlaces 0 .layers ∧ ¬ SegShape twoH 0 .layers L := by
  have hs : (swapAt twoH 0 .layers).isSome = true := rfl
  obtain ⟨L, h⟩ := Option.isSome_iff_exists.1 hs
  have e1 : (swapAt twoH 0 .layers).map (fun L => L.blocksInOrder.map (·.place)) =
      some (linkPlaces 0 .layers) := by decide
  have e2 : (swapAt twoH 0 .layers).map (fun L => L.hear.map (·.name)) =
      some ("other" :: "one" :: List.replicate 5 "other") := by decide
  rw [h] at e1 e2
  refine ⟨L, h, Option.some.inj e1, fun hS => ?_⟩
  have e3 := congrArg (List.map nameOf) hS.2.1
  have e4 : (L.hear.map some).map nameOf = L.hear.map (·.name) := by
    rw [List.map_map]
    rfl
  have e2' : L.hear.map (·.name) = "other" :: "one" :: List.replicate 5 "other" :=
    Option.some.inj e2
  rw [e4, e2'] at e3
  exact absurd e3 (by decide)

/-- A third silly driver: it cuts the order of the runs of claims down to the runs that its blocks
state. -/
def cutAt (H : Blocks Unit Unit) (l : Nat) (sub : ModelPart) : Option (Link Unit Unit) :=
  (linkAt H l sub).map fun L =>
    { L with order := First.stated (·.claims.map (·.1)) L.hear L.order }

/-- **A control: THE DRIVER THAT CUTS THE ORDER** has all the places and every block where it
belongs, and fails `SegShape`: at the idle record, whose blocks state no run, its order is empty. -/
theorem cut_fails : ∃ L, cutAt idleH 0 .layers = some L ∧
    L.blocksInOrder.map (·.place) = linkPlaces 0 .layers ∧
    L.hear.map some = (addresses (some 0) (kindsBeforeBatching .layers true)).map (blockAt idleH) ∧
    L.order = [] ∧ ¬ SegShape idleH 0 .layers L := by
  have hs : (linkAt idleH 0 .layers).isSome = true := rfl
  obtain ⟨L0, h0⟩ := Option.isSome_iff_exists.1 hs
  have hS := linkAt_shape h0
  have e0 : (linkAt idleH 0 .layers).map
      (fun L => First.stated (·.claims.map (·.1)) L.hear L.order) = some [] := by decide
  rw [h0] at e0
  have e0' : First.stated (·.claims.map (·.1)) L0.hear L0.order = [] := Option.some.inj e0
  refine ⟨{ L0 with order := First.stated (·.claims.map (·.1)) L0.hear L0.order }, ?_, ?_, hS.2.1,
    e0', fun hC => ?_⟩
  · unfold cutAt
    rw [h0]
    rfl
  · have e1 : (cutAt idleH 0 .layers).map (fun L => L.blocksInOrder.map (·.place)) =
        some (linkPlaces 0 .layers) := by decide
    unfold cutAt at e1
    rw [h0] at e1
    exact Option.some.inj e1
  · have h5 : First.stated (·.claims.map (·.1)) L0.hear L0.order = orderOf .layers := hC.2.2.2.2.1
    rw [e0'] at h5
    exact absurd h5 (by decide)

end VerifiableInference.Desc.Shape

#print axioms VerifiableInference.Desc.Shape.linkAt_shape
#print axioms VerifiableInference.Desc.Shape.linkAt_length
#print axioms VerifiableInference.Desc.Shape.bareChain_shape
#print axioms VerifiableInference.Desc.Shape.firstChain_shape
#print axioms VerifiableInference.Desc.Shape.linkShapeRow
#print axioms VerifiableInference.Desc.Shape.linkShapeMember
#print axioms VerifiableInference.Desc.Shape.swapped_places
#print axioms VerifiableInference.Desc.Shape.silly_fails
#print axioms VerifiableInference.Desc.Shape.swapped_fails
#print axioms VerifiableInference.Desc.Shape.cut_fails
