-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/Chain.lean: which kind of block stands at which place of a proof file's
first chain.

This file has definitions only, all computable. Nothing is proved here. It imports
Johnson/Desc/SeatGuard.lean (for the guard alone) and with it Johnson/Desc/Block.lean, which
defines `Place`, `Block`, `Link`, `Chain` and the names of the kinds,
`K1` to `K14`, with `frame` for a block of no kind, such as the seal.

Words. A block is a run of consecutive rounds, with the verifier's decision on them. A kind is a
sort of block: the blocks of one kind share one text and differ in their public parameters. A chain
is a sequence of blocks. A segment (`Link` in the code) is the stretch of the chain that treats one
part of the model. A place says where a block stands: the chain, the segment if there is one, the
block's number there, and its kind. The state (`S`) is what the verifier carries from one block to
the next. A claim (`Cl`) is an equation that a block derives but does not test; its segment's
batching takes it up.

The first chain. The model is cut into parts: groups of feed-forward layers and groups of attention
layers in turn, and the output head last. Each part has a segment. A segment has seven blocks, then
a batching, then a closing:
  1. K2, a code switch, which takes over what the segment before has left. The first segment has K1,
     a commitment, in its place.
  2. K3, a lookup for the table look-ups that the part's computation makes.
  3. K4, K5 or K6: the rounds that are particular to feed-forward layers, to attention layers or to
     the output head.
  4. K1, a commitment.
  5. K8, the smallness test (a range check): one round, in which the verifier draws a random matrix.
  6. K1, another commitment.
  7. K3, a lookup for the smallness test's digits.
  8. K9, the batching: one drawn element turns all claims of the segment into one equation.
  9. The closing, in three blocks. A block of K9 without a round writes the batching's sum as one
     equation. K10 folds that equation into what the next segment takes over. A second block of K9
     without a round ends the closing. A segment for feed-forward layers or for the head also leaves
     one pending claim on the weight table, which is settled after the last segment.
The head's segment has two more blocks. K7, in which the prover sends the reply (the next token),
comes first. K11, which merges the claims on the weight table, comes last before the batching.
After the last segment come K2, a code switch; K12, a proximity test; K13, which joins the pending
claims that the segments have left on the weight table, if there is more than one; K1, a commitment;
and the seal, which is the chain's last round. In front of the first segment stands the chain's
front: a block that whoever fills `Blocks` supplies. This file asks nothing of it and names no test:
whether a test on public data is needed there is not said here.

Main names:
  `ModelPart`: the three sorts of part of the model.
  `kindsBeforeBatching`: the kinds of a segment's blocks before its batching, in order.
  `backKinds`: the kinds of the blocks after the last segment, in order.
  `linksOk`: the list of parts ends with the head and has no other head.
  `orderCuts`, `orderOf`, `orderAfterOf`: the protocol's order of a segment's named lists of claims,
    in three stretches and in a row, and of what its blocks do after the batching.
  `stated`, `wholeOrNone`: the entries of an order that the blocks have; all of a stretch or none.
    Neither is called here: they serve OrderTally.lean and OrderLaw.lean.
  `Blocks S Cl`: what the kinds supply: a block for a place, a batching for a place, what starts and
    ends a segment, a segment's tests after each list of claims and after its batching, how the
    reply is compared, the chain's front, and the seal.
  `linkAt`: one segment, with the protocol's two orders uncut. `firstChainWithoutReplyGuard`: the whole first chain.
  `hearsReply`, `firstChain`: firstChainWithoutReplyGuard behind a guard: no block writes the reply, but
    for the decision at the one place that hears it; a step that does is refused.
  `placesOf`: the table of the places that have rounds of the plan.
  `closeKinds`, `closeAddresses`: the three blocks of a segment's closing.
  `linkPlaces`, `flatPlacesOf`: the places of all blocks, in the order of the flat list.
  `wantedOf`: the first chain's rows of Block.lean's table `wanted`.

The guard. `firstChain` lays `firstChainWithoutReplyGuard` behind the guard of Johnson/Desc/SeatGuard.lean:
no block but the one of the kind K7 writes the reply; a step that does is refused. The soundness
theorem's proof takes from this test that only one step changes the reply. What is proved of the
chain with a test that always says yes in its place: Johnson/LPFGuard/, with its limits.

What is not here. The list of parts, and whether more than one pending claim is left on the weight
table, are arguments: this file does not compute them
from the plan, which is
the public list of the file's rounds. No block is defined here. Each kind builds its block from the
public parameters of a place, which it finds in the plan. This file hands the kind the place and
writes the place into the block, so that a block's field `place` is where the block stands.

-/
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-- The three sorts of part of the model that a segment can treat: a group of feed-forward layers, a
group of attention layers, or the output head. -/
inductive ModelPart where
  | layers
  | attention
  | head
  deriving DecidableEq, Repr

/-- The kind of the block that holds the rounds particular to a part of the model: K4 for
feed-forward layers, K5 for attention layers, K6 for the output head. -/
def kindOfModelPart : ModelPart → KindName
  | .layers => .K4
  | .attention => .K5
  | .head => .K6

/-- The kinds of a segment's blocks before its batching, in order. `first` is true for the chain's
first segment, which opens with a commitment (K1) where the others open with a code switch (K2). The
head's segment also has the reply (K7) in front, and the merge of the claims on the weight table
(K11) at the end. -/
def kindsBeforeBatching (sub : ModelPart) (first : Bool) : List KindName :=
  (if sub = .head then [.K7] else []) ++
  [if first then .K1 else .K2, .K3, kindOfModelPart sub, .K1, .K8, .K1, .K3] ++
  (if sub = .head then [.K11] else [])

/-- The kinds of the blocks after the last segment, in order, without the seal. `several` is true if
the segments have left more than one pending claim on the weight table. Only then is there a block
that joins them (K13). -/
def backKinds (several : Bool) : List KindName :=
  [.K2, .K12] ++ (if several then [.K13] else []) ++ [.K1]

/-- The kinds of the three blocks of a segment's closing, in order: a block of K9 that writes the
batching's sum as one equation, the closing of K10, and a block of K9 that ends the closing. The
first and the third have no round. -/
def closeKinds : List KindName := [.K9, .K10, .K9]

/-- The list of parts ends with the head, and the head stands nowhere else in it. -/
def linksOk (links : List ModelPart) : Bool :=
  links.getLast? == some .head && links.dropLast.all (· != .head)

/-- The places of a list of kinds on the first chain. `link` is the segment's number, or `none`
after the last segment. The field `piece` numbers the blocks from 1, in the order of the list. -/
def addresses (link : Option Nat) (ks : List KindName) : List Place :=
  ks.zipIdx.map fun x => { chain := 1, link := link, piece := x.2 + 1, kind := x.1 }

/-- The places of a segment's closing. `n` is the number of the segment's blocks before its
batching. The first stands two numbers after the batching: the number between them belongs to a
block without rounds that Block.lean itself lays there (`Link.blocksInOrder`). -/
def closeAddresses (l n : Nat) : List Place :=
  closeKinds.zipIdx.map fun x => { chain := 1, link := some l, piece := n + 3 + x.2, kind := x.1 }

/-- The protocol's order of a segment's claims, in three stretches: the claims of the part of the
model itself, the claims of the test that values are small, and the claims after that test. A block
can state several lists of claims, each under a name. An entry names a block before the batching,
counted from 0 in the order of `kindsBeforeBatching`, and one of its lists. The order matters: a claim's
weight in the batching is fixed by its number, which it gets when it is added. The names are the
ones that the kinds' blocks use. -/
def orderCuts : ModelPart → List (List (Nat × String))
  | .layers =>
    [[(1, "objects"), (1, "guests"), (2, "front")],
     [(6, "objects"), (6, "guests"), (4, "K8.equations")],
     [(2, "back")]]
  | .attention =>
    [[(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "join"), (2, "second"),
      (1, "planes")],
     [(6, "objects"), (6, "guests"), (4, "K8.equations")],
     []]
  | .head =>
    [[(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes")],
     [(7, "objects"), (7, "guests"), (5, "K8.equations")],
     [(3, "logits"), (8, "the merge")]]

/-- The protocol's order of a segment's claims: the three stretches in a row. -/
def orderOf (sub : ModelPart) : List (Nat × String) := (orderCuts sub).flatten

/-- The same for what a segment's blocks do after the batching. -/
def orderAfterOf : ModelPart → List (Nat × String)
  | .layers => [(4, "K8.lsTail"), (2, "free-slot"), (4, "K8.tests")]
  | .attention => [(4, "K8.lsTail"), (4, "K8.tests")]
  | .head => [(5, "K8.lsTail"), (5, "K8.tests")]

/-- The entries of an order whose block has a list of that name. `names` gives a block's names.
`linkAt` does not call it: it lays the orders uncut. It serves the count of OrderTally.lean and the
laws of OrderLaw.lean. -/
def stated {B : Type} (names : B → List String) (bs : List B) (order : List (Nat × String)) :
    List (Nat × String) :=
  order.filter fun o => (bs[o.1]?).any fun b => (names b).contains o.2

/-- Of a stretch of an order, the blocks have either every list or none. A stretch of which only
some lists are stated would be added in part by the blocks and in part by something else, and the
claims' numbers would not be the protocol's. It says yes also where a stretch is stated by no
block at all. Where `orderOk` holds of the uncut order, every stretch is whole (OrderLaw.lean). -/
def wholeOrNone {B : Type} (names : B → List String) (bs : List B) (cut : List (Nat × String)) :
    Bool :=
  stated names bs cut == cut || (stated names bs cut).isEmpty

/-- What the kinds supply to this file. -/
structure Blocks (S Cl : Type) where
  /-- the block at a place; `none` if there is no block for that place -/
  block : Place → Option (Block S Cl)
  /-- the batching (K9) at a place; its argument reads the segment's claims off the state -/
  batch : Place → Option ((S → Except String (List Cl × S)) → Block S Cl)
  /-- what is done to the state where a segment starts (`lay`) and where it ends (`clear`) -/
  lay : Nat → S → Except String S
  clear : Nat → S → Except String S
  /-- a segment's test after each of its lists of claims: it is handed the segment's number, the
  entry of the order, that list's own claims, and the state after the list -/
  each : Nat → Nat × String → List Cl → S → Except String Unit
  /-- a segment's tests on the state after its batching, asked before what its blocks do after the
  batching; they cannot change the state -/
  tests : Nat → S → Except String Unit
  /-- Guard (see `firstChain`): the two states have the same reply: `same before after`. That
  it compares the reply, and the whole of it, is the matter of whoever supplies it -/
  same : S → S → Bool
  /-- the chain's front, the chain's first block. Block.lean means the field for a chain's tests on
  public data, in a block without a round; this file names no such test and asks none: a block that
  asks nothing fits -/
  first : Block S Cl
  /-- the seal, the chain's last block: one round, the last entry of the plan -/
  last : Block S Cl

variable {S Cl : Type}

/-- The block at a place, with that place written into its field `place`. -/
def blockAt (H : Blocks S Cl) (a : Place) : Option (Block S Cl) :=
  (H.block a).map fun b => { b with place := a }

/-- One segment. `l` is its number, from 0. The result is `none` if a block is missing. The closing
has three blocks (`closeAddresses`). The two orders are the protocol's, uncut. A list
that an order names and no block states then fails Block.lean's tests `orderOk` and
`orderAfterOk`, whose last clause asks that the order names no other list than the blocks state;
the segment's first block holds these tests (`Link.blocksInOrder`). -/
def linkAt (H : Blocks S Cl) (l : Nat) (sub : ModelPart) : Option (Link S Cl) := do
  let ks := kindsBeforeBatching sub (l == 0)
  let hear ← (addresses (some l) ks).mapM (blockAt H)
  let a9 : Place := { chain := 1, link := some l, piece := ks.length + 1, kind := .K9 }
  let batch ← H.batch a9
  let close ← (closeAddresses l ks.length).mapM (blockAt H)
  pure { name := s!"link {l}", chain := 1, number := l, lay := H.lay l, hear := hear,
         order := orderOf sub, each := H.each l, orderAfter := orderAfterOf sub, tests := H.tests l,
         batch := fun c => { batch c with place := a9 }, close := close, clear := H.clear l }

/-- The first chain, as the kinds' blocks are: without the guard of `firstChain`. The result
is `none` if the list of parts fails `linksOk`, or if a block is missing. The front's place and the
seal's have the kind `frame`, which Block.lean gives to a block of none of the fourteen kinds. The
front has the number 0 among the blocks outside the segments. -/
def firstChainWithoutReplyGuard (H : Blocks S Cl) (links : List ModelPart) (several : Bool) : Option (Chain S Cl) := do
  if !linksOk links then none
  let ls ← links.zipIdx.mapM fun x => linkAt H x.2 x.1
  let back ← (addresses none (backKinds several)).mapM (blockAt H)
  let aS : Place := { chain := 1, link := none, piece := back.length + 1, kind := .frame }
  let aF : Place := { chain := 1, link := none, piece := 0, kind := .frame }
  pure { first := { H.first with place := aF }, front := [], links := ls, back := back,
         last := { H.last with place := aS } }

/-- The one place whose decision may write the reply: that of the kind K7, which `kindsBeforeBatching` lays
once, first in the head's segment. -/
def hearsReply (a : Place) : Bool := a.kind == .K7

/-- The first chain: `firstChainWithoutReplyGuard` behind the guard of Johnson/Desc/SeatGuard.lean: no
block writes the reply, but for the decision at the one place that hears it. Behind every other
decision, every list of claims, everything that a block does after the batching, and what starts and
ends a segment stands a test: a step that leaves another reply than it found is refused. The
soundness theorem's proof takes from this test that only one step changes the reply. What is proved
of the chain with a test that always says yes in its place: Johnson/LPFGuard/, with its limits.
A yes behind the guard is the block's own yes, with the same state after it, by the guard's own
text: its test returns the state that it is handed, or refuses. With a `same` that always says yes
it is idle.
That a run goes by this chain, and not by a list of blocks of a seat's own, is not said here. -/
def firstChain (H : Blocks S Cl) (links : List ModelPart) (several : Bool) : Option (Chain S Cl) :=
  (firstChainWithoutReplyGuard H links several).map (Chain.guarded H.same hearsReply)

/-- The table of places: the places of the first chain's blocks, in order, without the front's and
the seal's. For
each segment these are the blocks of `kindsBeforeBatching`, then the batching (K9) and the closing (K10).
After the last segment they are the blocks of `backKinds`. These are the places that have rounds of
the plan; the blocks without rounds (Block.lean's own, and the first and third block of a closing)
are not in it: `flatPlacesOf` has them all. -/
def placesOf (links : List ModelPart) (several : Bool) : List Place :=
  (links.zipIdx.flatMap fun x =>
    let ks := kindsBeforeBatching x.1 (x.2 == 0)
    addresses (some x.2) (ks ++ [.K9]) ++
      [{ chain := 1, link := some x.2, piece := ks.length + 4, kind := .K10 }]) ++
    addresses none (backKinds several)

/-- The place of a block of no kind. -/
def frameAt (link : Option Nat) (piece : Nat) : Place :=
  { chain := 1, link := link, piece := piece, kind := .frame }

/-- The places of all blocks of one segment, in the order of `Link.blocksInOrder`: Block.lean's block where
the segment starts; the blocks of `kindsBeforeBatching`; the batching; Block.lean's block after the batching;
the three blocks of the closing; Block.lean's block where the segment ends. -/
def linkPlaces (l : Nat) (sub : ModelPart) : List Place :=
  let ks := kindsBeforeBatching sub (l == 0)
  frameAt (some l) 0 :: addresses (some l) ks ++
    [{ chain := 1, link := some l, piece := ks.length + 1, kind := .K9 },
      frameAt (some l) (ks.length + 2)] ++ closeAddresses l ks.length ++
    [frameAt (some l) (ks.length + closeKinds.length + 3)]

/-- The places of all blocks of the first chain, in the order of `Chain.blocksInOrder`: the front, the
segments, the blocks after the last segment, the seal. -/
def flatPlacesOf (links : List ModelPart) (several : Bool) : List Place :=
  frameAt none 0 :: (links.zipIdx.flatMap fun x => linkPlaces x.2 x.1) ++
    addresses none (backKinds several) ++ [frameAt none ((backKinds several).length + 1)]

/-- The first chain's rows of Block.lean's table `wanted`: for every block of the flat list its
place and its number of rounds. `takes` gives the numbers of rounds of the places of `placesOf`, in
that order (an argument: this file does not compute them from the plan),
and then the seal's. Every other block has none. This file does not say how many
rounds the seal's block declares. -/
def wantedOf (links : List ModelPart) (several : Bool) (takes : List Nat) : List (Place × Nat) :=
  let aS := frameAt none ((backKinds several).length + 1)
  let table := (placesOf links several ++ [aS]).zip takes
  (flatPlacesOf links several).map fun a => (a, (table.lookup a).getD 0)

end VerifiableInference.Desc.First
