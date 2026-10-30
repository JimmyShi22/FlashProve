-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/FillCore.lean: from a list of blocks to the first chain. The driver
(Johnson/Desc/First/Driver/Chain.lean) decides which kind of block stands where and in which order;
it asks for each block by its place, through the record `Blocks`. This file fills that record from
a list of blocks, each of which carries its place.
  `fill`     the record `Blocks`: at a place, the block of the list that carries that place
  `chainC`   the driver's chain over that record
  `Gather`   what a segment needs besides blocks: the batching as a function of the segment's
             claims, the segment's two tests, and the test of the guard on the reply
  `Frames`   `Gather`, what is done where a segment starts and ends, and the chain's first block
`chainC` refuses if the driver finds no block at a place that it asks for or rejects the list of
segments, or if the name of a block of the list is not in the chain's flat list.
The file is general in the state. It is used both by the proof file's description (OnlineDescriptionFromBlockTables.lean) and by
test harnesses that put other blocks into the same chain.

-/
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block Chain KindName Place roundlessBlock)
open VerifiableInference.Desc.First (ModelPart Blocks firstChain)

variable {σ Cl : Type}

/-- What is done to the state where a segment starts (`lay`) and where it ends (`clear`). No
default: a function that passes the state on would test nothing, and nothing would show it. -/
structure Frames0 (σ : Type) where
  lay : Nat → σ → Except String σ
  clear : Nat → σ → Except String σ

/-- The name of the chain's first block. -/
def frontName : String := "start:0"

/-- A first block that has no round and tests nothing. -/
def idleFront : Block σ Cl := roundlessBlock frontName 1 none 0 .ok

/-- What a segment needs besides blocks. No field has a default.
`batch`: the batching at a place, as a function of the segment's gatherer, that is, of the function
that `Link.blocksInOrder` hands it, which runs the lists of claims that the segment's blocks state. Where it
is `none`, `fill` takes the block of the list at that place, and that block never sees the gatherer:
the claims would then be added by nobody. The proof file's description does not reach that case:
`lackingAt` (OnlineDescriptionFromBlockTables.lean) refuses if a segment has no such function.
`each`, `tests`: the fields of `Link` of these names, by the segment's number. -/
structure Gather (σ Cl : Type) where
  batch : Place → Option ((σ → Except String (List Cl × σ)) → Block σ Cl)
  each : Nat → Nat × String → List Cl → σ → Except String Unit
  tests : Nat → σ → Except String Unit
  /-- `same before after`: the two states hold the same reply. The driver puts a guard over its
  chain (Johnson/Desc/SeatGuard.lean) that asks this after every step, except the decision at the
  one place that hears the reply, and refuses where the answer is no. There is no default: with a
  test that always says yes the guard would do nothing, and nothing would show it -/
  same : σ → σ → Bool

/-- All that `fill` takes besides the list of blocks. -/
structure Frames (σ Cl : Type) extends Frames0 σ, Gather σ Cl where
  first : Block σ Cl

/-- Nothing is done, nothing is tested, and the guard does nothing. Only for callers that do not run
the chain, such as `shapeOf` (Frames1.lean), which reads the blocks' names and places. -/
def Frames.unguarded : Frames σ Cl :=
  { lay := fun _ s => .ok s, clear := fun _ s => .ok s, batch := fun _ => none
    each := fun _ _ _ _ => .ok (), tests := fun _ _ => .ok (), same := fun _ _ => true
    first := idleFront }

/-- The driver's record, filled from the list `bs`; `sealed` is the chain's last block. At the end
of a segment the driver asks for three blocks, so the list has to hold a block at each of these
places. -/
def fill (bs : List (Block σ Cl)) (sealed : Block σ Cl) (fr : Frames σ Cl) : Blocks σ Cl :=
  { block := fun a => bs.find? fun b => b.place == a
    batch := fun a => fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b
    lay := fr.lay
    clear := fr.clear
    each := fr.each
    tests := fr.tests
    same := fr.same
    first := fr.first
    last := sealed }

/-- The kind of a segment as the planner numbers it (0, 1, other), as the driver's `ModelPart`. -/
def subOf (kind : Nat) : ModelPart :=
  if kind == 0 then .layers else if kind == 1 then .attention else .head

/-- The driver's chain over the list `bs`, whose last block is the chain's last. -/
def chainC (bs : List (Block σ Cl)) (links : List ModelPart) (fr : Frames σ Cl) :
    Except String (Chain σ Cl) :=
  match bs.getLast? with
  | none => .error "the chain: no block is supplied"
  | some z =>
    let several := bs.any fun b => b.place.kind == KindName.K13
    match firstChain (fill bs.dropLast z fr) links several with
    | none =>
      .error "the chain: the driver finds no block at a place, or rejects the list of links"
    | some c =>
      let flat := c.blocksInOrder
      match bs.find? fun b => !(flat.any fun x => x.name == b.name) with
      | some b => .error ("the chain: the supplied block " ++ b.name ++ " is not in the chain")
      | none => .ok c

end ProofFile
