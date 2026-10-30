-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/LotCore.lean: the records in which a module hands its blocks to the proof
file's description (OnlineDescriptionFromBlockTables.lean) and to test harnesses.
  `Lot`       a named table of blocks for some places of the first chain, with what a segment needs
              besides blocks. A module defines a function from the public part (`Pub`) to a `Lot`.
  `SharedSeat`, `SecondSeat`   a whole later chain, at a state of its module's own
  `Control`   a test that belongs to a lot. Only test harnesses read it.
  `Cl`        the type of a claim in all three chains
How a block is placed. A block is typed at the state `S` (Johnson/Desc/First/State.lean).
It is put into the chain by its place (chain, segment, piece, kind), and from then on carries the
place's name, whatever name its module gave it. A block at no place, and two blocks at one place,
are faults (Frames1.lean: `faultsOf`). Blocks of the kind `frame` go into `own` too; Frames1.lean
says which places they can take, and `frameBlocks` makes a segment's three.
What a lot is given. Only the public part, and the segments' records (`Ground`, Ground.lean).
Nothing of a view is handed to a lot. The segments' records hold the request's tokens, in the field
`cov`. A lot says in `letters` whether its blocks depend on them.
  * `letters := false`: the tables are computed once, from the records of a request of zeros
    (Pub.lean: `blankBy`). Limit: the type does not prevent such a block from reading `cov`. It
    would then read zeros at every request.
  * `letters := true`: the proof file's description does not use the lot. Test harnesses take the
    blocks' data from the records of a request of zeros and their functions from those of the
    request at hand.
No default passes a test or says of a lot or a later chain that it is free of `verify-on-bytes`:
`letters`, `okInst`, `fileOk` and `standIns` have no default value. `still` is the exception; its
comment states the limit.

-/
import Johnson.Desc.ProofFile.Pub
import Johnson.Desc.ProofFile.Views
import Johnson.Desc.Block
import Johnson.Desc.Claim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First

/-- The type of a claim. `FileDescription` has one type of claims for all three chains. -/
abbrev Cl : Type := VerifiableInference.Desc.Claim

/-- What `Link.blocksInOrder` hands a segment's batching: a function of the state that runs the lists of
claims that the segment's blocks state. -/
abbrev Gatherer : Type := S → Except String (List Cl × S)

/-- A test that belongs to a lot: something is altered, and the description should then refuse. Only
test harnesses read it. `what`: what is altered, in words. `front`: the name of the place at which
it aims. `turnV`, `turnF`, `turnX`: an alteration of the views, of the description, of the instance.
-/
structure Control where
  id : String
  what : String
  front : String
  turnV : Views → Option Views := some
  turnF : FileDescription Inst → FileDescription Inst := fun F => F
  turnX : Inst → Inst := fun x => x
  /-- blocks that replace the lot's blocks, by place, in the first run: for a test that reads no
  value that a prover sends. They are typed at `Cl`, so that they can state the lists of claims that
  the blocks they replace state; a table of blocks without claims goes through `asCl`.
  `loose`: blocks for a second run of the same alteration, usually the lot's block with one test
  left out. That run should say yes, which shows that this test alone refuses -/
  seat : Ground → List (Block S Cl) := fun _ => []
  loose : Option (Ground → List (Block S Cl)) := none
  /-- what replaces the lot's fields `batch`, `each` and `tests` in the first run. `none`: the lot's
  own stay -/
  batch : Option (Ground → Place → Option (Gatherer → Block S Cl)) := none
  each : Option (Ground → Nat → Option (Nat × String → List Cl → S → Except String Unit)) := none
  tests : Option (Ground → Nat → Option (S → Except String Unit)) := none
  /-- the same for the second run. If one of the three is given, there is a second run whether or
  not `loose` is given -/
  looseBatch : Option (Ground → Place → Option (Gatherer → Block S Cl)) := none
  looseEach : Option (Ground → Nat → Option (Nat × String → List Cl → S → Except String Unit)) :=
    none
  looseTests : Option (Ground → Nat → Option (S → Except String Unit)) := none
  /-- what the first run should say: "NO" (refused) unless stated otherwise -/
  due : String := "NO"

/-- A named table of blocks from one module. -/
structure Lot where
  name : String
  /-- whether its blocks depend on the request's tokens (see the head of this file). No default -/
  letters : Bool
  /-- its blocks that state no claims, one for each place that it takes -/
  own : Ground → List (Block S Unit)
  /-- its blocks that state lists of claims. A place is taken in `own` or here, never in both -/
  hearC : Ground → List (Block S Cl) := fun _ => []
  /-- the batching at a place, as a function of the segment's gatherer (the type of the driver's
  `Blocks.batch`). The claims that are added in that segment are then the lists that its blocks
  state, in the driver's order. A list that the order names and no block states is refused on the
  plan. `none`, the default, means that this lot supplies none; the proof file's description refuses
  if no lot supplies one for a segment (OnlineDescriptionFromBlockTables.lean: `lackingAt`) -/
  batch : Ground → Place → Option (Gatherer → Block S Cl) := fun _ _ => none
  /-- `Link.each` for a segment, by its number: the test after each list of claims, on that list.
  `none`, the default, means that this lot supplies none; `lackingAt` refuses if no lot does. Two
  lots that supply one for one segment are a fault -/
  each : Ground → Nat → Option (Nat × String → List Cl → S → Except String Unit) := fun _ _ => none
  /-- `Link.tests` for a segment: the tests after the adding. By their type they cannot change the
  state. The default, and two lots, as for `each` -/
  tests : Ground → Nat → Option (S → Except String Unit) := fun _ _ => none
  /-- the names of `verify-on-bytes`'s steps at its places that its blocks run. The proof
  file's description does not use a block at such a place. Limit: the default is the empty list, so
  a lot that writes nothing says that it runs none, and nothing tests that. The field changes no
  block's tests; it decides only whether a block is used, and so whether a description is returned
  -/
  still : List String := []
  controls : List Control := []
  /-- for a test harness's trial lots: what the harness should find, as data -/
  rehearsal : List (String × String) := []

/-- A table of blocks that state no claims, at the type `Cl`. `Block.retype` adds a test on the plan
that they state none. -/
def asCl (f : Ground → List (Block S Unit)) : Ground → List (Block S Cl) :=
  fun G => (f G).map fun b => b.retype

/-- All blocks of a lot, at the type `Cl`: `own`, then `hearC`. A lot's blocks are read through this
alone. A block in `own` that does state claims fails its test on the plan. -/
def Lot.blocks (L : Lot) : Ground → List (Block S Cl) := fun G => asCl L.own G ++ L.hearC G

/-- A segment's three blocks of the kind `frame`, for `Lot.own`. None has a round. `lay`: where the
segment starts. `opened`: joined after the block at the segment's first place; `plan` is its test on
the plan, which becomes part of the joined block's. `clear`: where the segment ends. `first`,
`last`:
the pieces of the first place and of the end. The end is piece 13 in a segment with seven hearing
blocks (these, the batching, the block after it, three closing blocks), and 15 in the head's. -/
def frameBlocks (link : Nat) (plan : Bool) (lay opened clear : S → Except String S)
    (first : Nat := 1) (last : Nat := 13) : List (Block S Unit) :=
  [VerifiableInference.Desc.roundlessBlock s!"link {link}: lay" 1 (some link) 0 lay,
   { VerifiableInference.Desc.roundlessBlock s!"link {link}: opened" 1 (some link) first opened with
     planOk := plan },
   VerifiableInference.Desc.roundlessBlock s!"link {link}: clear" 1 (some link) last clear]

/-- The whole shared chain. -/
structure SharedSeat where
  lot : String
  /-- the chain's own state -/
  σ : Type
  start : InstPub → σ
  chain : Chain σ Unit
  /-- what the second chain's start reads of this chain's end; `some` does not show that it ran -/
  ended : σ → Option OnBytes.Proof.SharedEnd
  /-- its tests on the public part of the instance. No default -/
  okInst : InstPub → Bool
  /-- its tests on the plan, besides its blocks' own. No default -/
  fileOk : Bool
  /-- the names of its blocks that run steps of `verify-on-bytes`, by its module's own
  statement. No default. The proof file's description refuses unless it is empty -/
  standIns : List String

/-- The whole second chain. -/
structure SecondSeat where
  lot : String
  σ : Type
  /-- from the first chain's last state and the shared chain's end -/
  start : InstPub → S → OnBytes.Proof.SharedEnd → Except String σ
  chain : Chain σ Unit
  /-- its part of the last test -/
  done : σ → Bool
  /-- as in `SharedSeat` -/
  fileOk : Bool
  /-- as in `SharedSeat` -/
  standIns : List String

end ProofFile
