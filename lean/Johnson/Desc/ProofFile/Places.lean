-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Places.lean: the places of a proof file's first chain, computed from the
chain's table of stretches (`cutOf`, Johnson/Desc/First/Driver/Cut.lean). Definitions with code; no
theorem.

The table has one row for each step of `verify-on-bytes`, with the number and the kind of the place
to which the step belongs. `spotsOf` puts the rows of one place together and gives the place the
record `Place` of Johnson/Desc/Block.lean.

  `headOf look`   the part of a step's name before its first dot: "A0" of "A0.2.scores"
  `byPlace cs`    neighbouring rows with the same place number and the same head, together
  `kindName`      the kind of a place, from the table's word for it
  `Spot`          a place: its name, its `Place`, its rows of the table
  `spotsOf cs`    the places in order

A segment is a `Link` of Block.lean; the code and the names in strings say "link". A place's name is
its head and its number under that head: "A0:3". A new segment begins where the head changes. The
heads "F", "M" and "seal" come after the segments and belong to none. Pieces count from 1 inside a
segment, and from 1 after the segments.

What a caller must know:
- `kindName` knows a fixed list of words. At any other word it returns `none`, and then `spotsOf`
  returns `none` too: an unknown step cannot become a place unnoticed.
- The table's row for the seal takes no round. The fold of Block.lean puts the sealing round back,
  empty, and wants the blocks' rounds to be all the plan's entries, so here that row takes one.
- A segment's closing is three places (`closeAddresses`, Johnson/Desc/First/Driver/Chain.lean): one
  of kind K9 named "A0:9.equation", K10's own "A0:9", and one of kind K9 named "A0:9.shut". The two
  of kind K9 have no row of the table: their `cuts` is empty. So a segment has three places of kind
  K9, and only the first, the batching, has rows.

-/
import Johnson.Desc.First.Driver.Cut
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.First (Cut)

/-- The part of a step's name before its first dot. -/
def headOf (look : String) : String := (look.splitOn ".").headD ""

/-- Neighbouring rows with the same place number and the same head, together. -/
def byPlace : List Cut → List (List Cut)
  | [] => []
  | c :: cs =>
    match byPlace cs with
    | (d :: g) :: gs =>
      if d.place == c.place && headOf d.look == headOf c.look then (c :: d :: g) :: gs
      else [c] :: (d :: g) :: gs
    | gs => [c] :: gs

/-- The kind of a place. For the word "chain" the head's first letter decides. `none` at a word
that is not listed. -/
def kindName (head kind : String) : Option KindName :=
  if kind == "send" then some .K1
  else if kind == "sendLoc" then some .K2
  else if kind == "lookupCalls" || kind == "lookupDigits" then some .K3
  else if kind == "chain" then
    (if head.startsWith "A" then some .K5 else if head.startsWith "G" then some .K4 else none)
  else if kind == "headRow" then some .K6
  else if kind == "reply" then some .K7
  else if kind == "rng" then some .K8
  else if kind == "batSigma" then some .K9
  else if kind == "batFold" then some .K10
  else if kind == "merge" then some .K11
  else if kind == "test" then some .K12
  else if kind == "batPsc" then some .K13
  else if kind == "SEAL" then some .frame
  else none

/-- A place with its rows of the table. -/
structure Spot where
  name : String
  place : Place
  cuts : List Cut

/-- Whether a head comes after the segments. -/
def behindLinks (head : String) : Bool := head == "F" || head == "M" || head == "seal"

/-- The places in order. `link`: the current segment's number. `piece`: the next place's number.
`last`: the head of the place before, empty at the start. -/
def spotsFrom : List (List Cut) → (link piece : Nat) → (last : String) → Option (List Spot)
  | [], _, _, _ => some []
  | [] :: gs, link, piece, last => spotsFrom gs link piece last
  | (c :: g) :: gs, link, piece, last =>
    let h := headOf c.look
    let back := behindLinks h
    -- a new segment begins where the head changes; after the segments the count goes on
    let fresh := h != last && !(back && behindLinks last)
    let link' := if fresh && !last.isEmpty && !behindLinks last then link + 1 else link
    let piece' := if fresh then 1 else piece
    (kindName h c.kind).bind fun k =>
      (spotsFrom gs link' (piece' + 1) h).map fun l =>
        let mine : Nat → Spot := fun at' =>
          { name := s!"{h}:{piece'}", place := ⟨1, if back then none else some link', at', k⟩,
            cuts := (c :: g).map fun x => if x.kind == "SEAL" then { x with take := 1 } else x }
        -- The number after the batching's belongs to a block that Block.lean adds itself, so the
        -- closing's three places start one number later.
        if k == KindName.K10 then
          { name := s!"{h}:{piece'}.equation", place := ⟨1, some link', piece' + 1, .K9⟩,
            cuts := [] } :: mine (piece' + 2) ::
          { name := s!"{h}:{piece'}.shut", place := ⟨1, some link', piece' + 3, .K9⟩,
            cuts := [] } :: l
        else mine piece' :: l

/-- The chain's places; `none` if the table has a word that `kindName` does not know. -/
def spotsOf (cs : List Cut) : Option (List Spot) := spotsFrom (byPlace cs) 0 1 ""

end ProofFile
