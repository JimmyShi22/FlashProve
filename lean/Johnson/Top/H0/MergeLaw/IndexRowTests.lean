-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/IndexRowTests.lean: the premises of the equation on the two readings of the
index masks (`index_words`, IndexRow.lean), as tests with code on a verifier's state. Definitions
only; every one of them can be run.

Main names:
  `indexTests q M L cs sh sx b`: twelve tests by name, each with its answer. b: the verifier's
    state. q: the seat (tree, tenant) that the list of rounds gives the index masks' message.
    M, L: the shapes and the seats of the first chain's oracle messages, by the list of rounds.
    cs: the code table. sh, sx: the shape and the seat of the member at which the merge's law reads
    the index masks. The last test (the length of a mask row's message is a power of two) is asked
    by `index_in_msg` alone.
  `indexTestsB`: all twelve.
  `indexFails`: the names of the tests that say no.
  `indexTwins`: NEGATIVE TESTS. For each of the twelve: the names of the tests that say no at an
    input altered in that test's own condition. Due: that test's name alone ("messageThere" may
    bring others with it). `twinsRefusedB`: each is refused by its own test.
  `indexLine`, `twinsLine`: one line of print each. `indexRide`: both at a verifier's state, with
    the two lists taken off the planner's list of the first chain's sendings.

Limits. No law stands here: that a yes of `indexTestsB` gives the premises is
`index_words_of_tests` (IndexRow.lean). Nothing on soundness.
-/
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (Codes OracleShape powerOfTwo)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB)

/-- **The twelve tests by name, each with its answer.** -/
def indexTests (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes) (sh : OracleShape)
    (sx : Nat × Nat) (b : S) : List (String × Bool) :=
  [("msgShapes", msgShapesB M b.st),
    ("bookInOrder", bookInOrderB 0 b.book b.roots),
    ("seatsCarried", seatsCarriedB L b.book),
    ("placesAreMessages", decide (b.book.place.size = b.st.oracles.size)),
    ("placesBelow", placesBelowB L b.book.place.size b.book.trees.size),
    ("messageThere", decide (b.out.indexMasks < b.st.oracles.size)),
    ("bookSeat", decide (b.book.place[b.out.indexMasks]? = some q)),
    ("codes", decide (b.st.codes = cs)),
    ("shape", decide (M[b.out.indexMasks]? = some sh)),
    ("memberSeat", decide (sx = q)),
    ("rowsPowerOfTwo", powerOfTwo sh.maskRows),
    ("lengthPowerOfTwo", powerOfTwo (cs.mask.getD sh.maskCode default).ell)]

/-- All twelve. -/
def indexTestsB (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes) (sh : OracleShape)
    (sx : Nat × Nat) (b : S) : Bool :=
  (indexTests q M L cs sh sx b).all (·.2)

/-- The names of the tests that say no. -/
def indexFails (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes) (sh : OracleShape)
    (sx : Nat × Nat) (b : S) : List String :=
  ((indexTests q M L cs sh sx b).filter fun x => !x.2).map (·.1)

/-- **Negative tests.** For each of the twelve tests: its name, and the names of the tests that say
no at an input altered in that test's own condition. Where the unaltered input passes all twelve,
what is due is that test's name ALONE; at "messageThere" the tests that read the message's number
may say no beside it. -/
def indexTwins (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes) (sh : OracleShape)
    (sx : Nat × Nat) (b : S) : List (String × List String) :=
  let o := b.out.indexMasks
  -- a message other than the index masks'
  let i := if o = 0 then 1 else 0
  let sh3 : OracleShape := { sh with maskRows := 3 }
  let cs3 : Codes := { cs with mask := cs.mask.modify sh.maskCode fun c => { c with ell := 3 } }
  [("msgShapes", -- another message's shape in the list has one answer more
      indexFails q (M.modify i fun x => { x with answers := x.answers + 1 }) L cs sh sx b),
    ("bookInOrder", -- one root more
      indexFails q M L cs sh sx { b with roots := b.roots + 1 }),
    ("seatsCarried", -- the list of seats without its first
      indexFails q M { L with places := L.places.drop 1 } cs sh sx b),
    ("placesAreMessages", -- the book without its last place
      indexFails q M L cs sh sx { b with book := { b.book with place := b.book.place.pop } }),
    ("placesBelow", -- a book without trees, and no root
      indexFails q M L cs sh sx { b with book := { b.book with trees := #[] }, roots := 0 }),
    ("messageThere", -- the number behind the last message
      indexFails q M L cs sh sx { b with out := { b.out with indexMasks := b.st.oracles.size } }),
    ("bookSeat", -- the next tenant, in the list of rounds and at the member
      indexFails (q.1, q.2 + 1) M L cs sh (sx.1, sx.2 + 1) b),
    ("codes", -- one base code more
      indexFails q M L { cs with base := cs.base.push default } sh sx b),
    ("shape", -- the member's shape has one answer more
      indexFails q M L cs { sh with answers := sh.answers + 1 } sx b),
    ("memberSeat", -- the next tree
      indexFails q M L cs sh (sx.1 + 1, sx.2) b),
    ("rowsPowerOfTwo", -- three mask rows: in the state, in the list and at the member
      indexFails q (M.set o sh3) L cs sh3 sx
        { b with st := { b.st with
            oracles := b.st.oracles.modify o fun x => { x with shape := sh3 } } }),
    ("lengthPowerOfTwo", -- mask rows' messages of length 3: in the state and in the code table
      indexFails q M L cs3 sh sx { b with st := { b.st with codes := cs3 } })]

/-- Every negative test is refused by the test whose name it bears. -/
def twinsRefusedB (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes) (sh : OracleShape)
    (sx : Nat × Nat) (b : S) : Bool :=
  (indexTwins q M L cs sh sx b).all fun x => x.2.contains x.1

/-- One line of print: the tag, the verdict, each test with its answer, and the numbers read. -/
def indexLine (tag : String) (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes)
    (sh : OracleShape) (sx : Nat × Nat) (b : S) : String :=
  s!"INDEXROW|{tag}|all {indexTestsB q M L cs sh sx b}|" ++
    " ".intercalate ((indexTests q M L cs sh sx b).map fun x => s!"{x.1}={x.2}") ++
    s!"|indexMasks {b.out.indexMasks}|messages {b.st.oracles.size}|places {b.book.place.size}" ++
    s!"|trees {b.book.trees.size}|the book's seat {b.book.place[b.out.indexMasks]?}" ++
    s!"|maskRows {sh.maskRows}|ell {(cs.mask.getD sh.maskCode default).ell}"

/-- One line of print: whether each negative test is refused by its own test; how many are refused
by that test alone; each with the names of the tests that said no. -/
def twinsLine (tag : String) (q : Nat × Nat) (M : List OracleShape) (L : Laid) (cs : Codes)
    (sh : OracleShape) (sx : Nat × Nat) (b : S) : String :=
  let t := indexTwins q M L cs sh sx b
  s!"INDEXROW-NEG|{tag}|each refused by its own test {twinsRefusedB q M L cs sh sx b}" ++
    s!"|by that test alone {(t.filter fun x => x.2 == [x.1]).length} of {t.length}|" ++
    " · ".intercalate (t.map fun x => s!"{x.1}: {x.2}")

/-- **Both lines at a verifier's state, the two lists off the planner's list of sendings.** c: the
first chain's sendings, as the planner lists them. ix, q: the number and the seat that the list of
rounds gives the index masks' message. sh, sx: the shape and the seat of the member at which the
merge's law reads the index masks: TO BE HANDED IN FROM THAT MEMBER's OWN TERM: whoever hands in the
list's shape at ix and q again makes the tests "shape" and "memberSeat" true by construction. A
first line says what the planner's own lists have at ix. -/
def indexRide (tag : String) (c : Johnson.G.ChainSends) (cs : Codes) (ix : Nat) (q : Nat × Nat)
    (sh : OracleShape) (sx : Nat × Nat) (b : S) : List String :=
  let M := VerifiableInference.Desc.K12.Door.msgsOfChain c
  match VerifiableInference.Desc.K12.Door.laidOfChain c with
  | some L =>
    [s!"INDEXROW-PLAN|{tag}|ix {ix}|shapes {M.length}|seats {L.places.length}" ++
        s!"|the planner's seat at ix is q {decide (L.places[ix]? = some q)}" ++
        s!"|the planner's shape at ix is sh {decide (M[ix]? = some sh)}" ++
        s!"|the state's number is ix {decide (b.out.indexMasks = ix)}",
      indexLine tag q M L cs sh sx b, twinsLine tag q M L cs sh sx b]
  | none => [s!"INDEXROW-PLAN|{tag}|the planner's sendings cannot be laid"]

end VerifiableInference.Desc.First.MergeLaw
