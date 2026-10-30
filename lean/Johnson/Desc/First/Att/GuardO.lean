-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardO.lean: the tests on public data at the attention segments of the first
chain (Johnson/Desc/First/Att/GuardN.lean), from the three public files, with the format's second
hash function as a letter.

  `k5AsksFilesO o pol lay KL`: the tests of every attention segment (k5AsksN) of the public record
    that PlanWritten.publicOfO o pol KL (some lay) returns
    (Johnson/Desc/Ok/PlanWritten/PublicAt.lean): the record that the proof file's description is
    made of. Where that refuses, one test fails.
  `K5Asks.masks | usual | calls | nums | pos | units | held o pol lay KL : Bool`: one function a
    row: test number 0 to 6 of the guard's list at every attention link of that record; false where
    the files make no record, or a link has no plan or no place. Where the record has no attention
    link (a proof that does not cover attention) every row is true for nothing, and rightly so: no
    block of the kind stands in the description there. Each row evaluates its own test alone
    (K5Asks.testAt: a second writing of the seven entries of guardListN, so that a compiled row does
    not evaluate the other six; Johnson/Desc/First/Att/GuardAtSeat.lean ties the two: all_of_rows).
    `K5Asks.words`: the words under which a verifier may refuse, row by row. `K5Asks.rows o pol lay
    KL`: the same seven with their words, at one making of the record (the seven functions make it
    once each).

Why a file of its own. k5AsksFilesN (GuardFilesN.lean) makes its record by Model.Verify.publicOf,
which calls the second hash function by name. A verifier whose text takes that hash as a letter o
asks this list. Which hash is reached: none by name: by a search by program through the bodies of
all definitions that k5AsksFilesO, K5Asks.rows and the seven rows reach (some 2,700 constants each):
none of them is the second hash function (OnBytes.secondHashFunction and its helpers) or a part of BLAKE2b
(Run.Blake2b); the tree hash that is reached (Fmt.olderTK) takes its hash as a letter. The same
search at k5AsksFilesN finds both. What the search does not follow: 52 constants whose bodies Lean
does not show, all of Lean's own core. No definition of this file or of GuardN.lean reaches either.
(The base's own modules below publicOfO's file do hold the second hash function's text: by import,
not by a call.) At o := the second hash function itself the two lists are one; and a yes of either
gives the other's wherever both records are returned (Johnson/Desc/First/Att/GuardAtSeat.lean). No
Mathlib is below this file. The tests can only make a verifier refuse more. Definitions with code;
no theorem. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.GuardN
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-- The tests at every attention segment, from the three public files (the policy, the layout, the
file of scales), at the second hash function o. -/
def k5AsksFilesO (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) :
    List (String × Bool) :=
  match VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) with
  | .ok W => k5AsksN W
  | .error _ => [("k5-public-record: the public files make no record", false)]

/-! ## One function a row -/

namespace K5Asks

/-- Test number k, from 0, of the guard's list (guardListN, GuardN.lean), by itself: so that a row
evaluates its own test alone. a: the group's plan; x: the place of the lookup; p: the block's
numbers. -/
def testAt (k : Nat) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place)
    (p : Par) : Bool :=
  match k with
  | 0 => Decidable.decide (x.F.next + FoNums.nMasks x.fs ≤ x.ns)
  | 1 => usualN a.S.cf
  | 2 => callsFitN a.S a.fs
  | 3 => numsN a.S
  | 4 => posN (geoOf a.S)
  | 5 => unitsN a.S a.fs
  | 6 => heldN 128 p
  | _ => false

/-- Test number k at every attention link of the public record W. False where a link has no plan or
no place. Where W has no attention link it is true: there is nothing to test. -/
def rowW (k : Nat) (W : Verify.Public) : Bool :=
  (attLinksN W).all fun y =>
    match W.A[y.2]?, VerifiableInference.Desc.First.Look.lookAt W y.1 false with
    | some a, some x => testAt k a x (parN W y.1 a)
    | _, _ => false

/-- The same from the public files, at the second hash function o. False if they make no record. -/
def rowO (k : Nat) (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool :=
  match VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) with
  | .ok W => rowW k W
  | .error _ => false

/-- At every attention link: the lookup's own scalars lie among the link's slots. -/
def masks (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 0 o pol lay KL

/-- At every attention link: the configuration has the usual four calls and one shift. -/
def usual (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 1 o pol lay KL

/-- At every attention link: the lookup's numbers fit the segment's sizes. -/
def calls (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 2 o pol lay KL

/-- At every attention link: the shape's numbers are those of its sizes. -/
def nums (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 3 o pol lay KL

/-- At every attention link: six numbers of the place are positive. -/
def pos (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 4 o pol lay KL

/-- At every attention link: the place's seven units are the description's seven families of
pieces. -/
def units (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 5 o pol lay KL

/-- At every attention link: at each round of the segment the proved count is within its share. -/
def held (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Bool := rowO 6 o pol lay KL

/-- The words under which a verifier may refuse, row by row. -/
def words : List String :=
  ["an attention segment's lookup has more scalars than the segment has slots left",
   "the attention lookups are not the usual four with one shift",
   "the attention lookups' numbers do not fit the segment's sizes",
   "an attention segment's numbers are not those of its sizes",
   "one of six sizes of an attention segment's tables is 0",
   "an attention segment's pieces do not lie in the lookups as described",
   "an attention segment is too large, or a round's count of bad challenges cannot be weighed \
    or is above its share"]

/-- The seven rows with their words, at one making of the record. -/
def rows (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : List (String × Bool) :=
  match VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) with
  | .ok W => words.zipIdx.map fun x => (x.1, rowW x.2 W)
  | .error _ => words.map fun w => (w, false)

end K5Asks

end VerifiableInference.Desc.First.Att.P
