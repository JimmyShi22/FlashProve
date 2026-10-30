-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/CutTest.lean: a test with code on the proof file's IOP as written in
Lean: THE CUT of each of its three chains into sub-protocols is one written list of the full size
(`cutFirstFull`, `cutSharedFull`, `cutSecondFull`, Johnson/Desc/Ok/PlanWritten/CutLit.lean),
compared whole. Definitions alone.

What a row of the cut holds, of one sub-protocol b: its name · its place (chain, link, number in the
link, kind) · how many rounds it declares · the length of its field `oracles` · the rounds that tell
a tree, each with its number and all that it tells (each tree's log-length, the words of a symbol,
and its tenants, the oracle messages that share its leaves) · its field `before` (the messages that
must stand fixed before its first draw).

What it is for. Laws on the proof file's IOP read public facts on it: which sub-protocol stands
where, which stretch of the list of rounds is whose, who tells which oracle message. With the pin on
the list of rounds (`seatPinnedProof`, Test.lean) an accept of this test makes each of these a
closed fact on a written list, which Lean's kernel can evaluate outside the verifier. That the IOP
as written has this cut at the public files is no theorem, so the test is meant to be asked at the
run, among the verifier's tests on the public files. This file calls it nowhere.

Why the field `oracles` is not written whole. It has one entry for each declared round, and nearly
all are empty. A list is fixed by its length and its non-empty entries with their places; that
nothing told is left out is a theorem (`toldRounds_flat`,
Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).

Definitions.
  `toldRounds b`: the rounds of b that tell a tree, each with its number, from 0, and what it tells.
  `cutOf bs`: the rows of a list of sub-protocols.
  `sameRow x y`, `sameRows a b`: two rows, two lists of rows, are the same. The comparison is
    written out field by field, by the equality that each field's type bears where it is declared:
    Lean does not find an equality test for the whole row's type by itself, and a file beneath the
    verifier's list of tests is to hold definitions alone. That no field is left out is a theorem
    (`sameRows_iff`, CutTestLaws.lean).
  `cutSame a b c`: three lists of rows are the three written lists.
  `cutIs F`: `cutSame` at F's three chains.
  `cutRow F Z`: the same in the form of a row of the proof file's entry tests
    (Johnson/Desc/Laid/DoorHead.lean: `Desc.Door.atFull M (cutRow F)`): Z, the public part, is not
    read. THE TEST ON THE KEY IS THE ENTRY TESTS' OWN (`atFullKey`): here is none: whoever calls
    `cutIs` at public files of another size gets a reject.

Limits. A place is a label that the sub-protocol's maker lays: which decision stands behind a label
no row says. The rounds themselves are not in the row: only how many. Nothing on the key file's and
the copy's file's IOPs. The full size alone. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open VerifiableInference.Desc

/-- The rounds of a sub-protocol that tell a tree, each with its number and what it tells. -/
def toldRounds {S Cl : Type} (b : Block S Cl) : List (Nat × List Oracle) :=
  (b.oracles.zipIdx.filter fun x => !x.1.isEmpty).map fun x => (x.2, x.1)

/-- The rows of a list of sub-protocols. -/
def cutOf {S Cl : Type} (bs : List (Block S Cl)) :
    List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) :=
  bs.map fun b => (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before)

/-- Two rows are the same: field by field. -/
def sameRow
    (x y : String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) : Bool :=
  decide (x.1 = y.1) && decide (x.2.1 = y.2.1) && decide (x.2.2.1 = y.2.2.1) &&
    decide (x.2.2.2.1 = y.2.2.2.1) && decide (x.2.2.2.2.1 = y.2.2.2.2.1) &&
    decide (x.2.2.2.2.2 = y.2.2.2.2.2)

/-- Two lists of rows are the same: as long, and row by row. -/
def sameRows :
    List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) →
    List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) → Bool
  | [], [] => true
  | x :: a, y :: b => sameRow x y && sameRows a b
  | _, _ => false

/-- Three lists of rows are the three written lists. -/
def cutSame
    (a b c : List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat))) :
    Bool :=
  sameRows a cutFirstFull && sameRows b cutSharedFull && sameRows c cutSecondFull

/-- **The three chains' cuts are the written ones.** -/
def cutIs {Xi : Type} (F : FileDescription Xi) : Bool :=
  cutSame (cutOf F.first.blocksInOrder) (cutOf F.shared.blocksInOrder) (cutOf F.second.blocksInOrder)

/-- **The row for the proof file's entry tests.** The public part is not read. -/
def cutRow (F : FileDescription ProofFile.Inst) (_ : ProofFile.Pub) : Bool := cutIs F

end VerifiableInference.PlanWritten
