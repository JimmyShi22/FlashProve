-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardWalkN.lean: the tests of Johnson/Desc/First/Att/GuardN.lean, held
against a description's own blocks.

GuardN.lean walks the attention links of a public record by a formula of its own (attLinksN). Where
the record has no attention segment its list of tests is empty and refuses nothing. The test here
asks that the walk and the description agree: the blocks that bear the kind K5 in their place, in
the description's first chain, stand at just the places of the walk, in its order, and no block of
the two other chains bears that kind. So every block that bears the kind stands at a link that the
tests of GuardN.lean have tested, and an empty walk passes only where no block bears it.

  `k5PlacesN W`: the places of the walk: chain 1, the link, piece 3, kind K5.
  `k5WalkPlacesN W p1 p2 p3`: the test, on the three chains' lists of places.
  `k5WalkN W F`: the test at a description F.
  `k5AsksDescN pol lay KL F`: the tests of k5AsksFilesN, then this one: the form for a list of named
    tests that also has the description in hand.

Whether a verifier asks this test hangs on which list it takes: k5AsksFilesN (GuardFilesN.lean) does not
hold it; k5AsksDescN does. Where a theorem on the text that makes the description gives the same,
the test is not wanted.

Limits. A place is a label. That the block at a place of kind K5 is the kind's own block (k5AtN,
Johnson/Desc/First/Att/SeatN.lean), and that no such block stands under another kind's place, is not
tested here. A place does not name a group either: that the block at link l was made of the plan of
the walk's group is not tested here. These hold, or not, by the text that makes the description. The
test has been run on made-up lists of places alone, at no description: so its comment does not say,
as those of GuardN.lean do, that no file is known at which it says no.
Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.GuardFilesN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (FileDescription Place)

/-- The places of the walk. -/
def k5PlacesN (W : Verify.Public) : List Place :=
  (attLinksN W).map fun y => ⟨1, some y.1, 3, .K5⟩

/-- The test on the three chains' lists of places. -/
def k5WalkPlacesN (W : Verify.Public) (p1 p2 p3 : List Place) : Bool :=
  Decidable.decide ((p1.filter fun q => q.kind == .K5) = k5PlacesN W) &&
    (p2.all fun q => q.kind != .K5) && (p3.all fun q => q.kind != .K5)

/-- The test at a description. -/
def k5WalkN {Xi : Type} (W : Verify.Public) (F : FileDescription Xi) : Bool :=
  k5WalkPlacesN W (F.first.blocksInOrder.map (·.place)) (F.shared.blocksInOrder.map (·.place))
    (F.second.blocksInOrder.map (·.place))

/-- The tests of k5AsksFilesN, then the walk's. -/
def k5AsksDescN {Xi : Type} (pol lay KL : ByteArray) (F : FileDescription Xi) : List (String × Bool) :=
  k5AsksFilesN pol lay KL ++
    -- The blocks of kind K5 stand at just the links that the tests above have walked.
    -- Taken by K05_law_one, which is stated at one block: this says at which blocks it is asked.
    -- It is there for the proof. It has been run at no description yet.
    [("k5-walk: the description's attention blocks are not at the plan's attention links",
      match Model.Verify.publicOf pol KL (some lay) with
      | .ok W => k5WalkN W F
      | .error _ => false)]

end VerifiableInference.Desc.First.Att.P
