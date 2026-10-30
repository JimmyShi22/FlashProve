-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookTests.lean: the eleven tests that the frame (Johnson/Desc/ProofFile/Honest/Frame.lean)
has on a book of coins, `ProverCoinCounts.clauses`, are defined a second time, as a function `clausesAt` of a
description's rows, and are shown to be the frame's own at every description and every book
(`clauses_rows`). The tests are then evaluated at the book of a small example key file. Three
theorems, none with a hypothesis; definitions that can be evaluated; tests by `#guard`, which Lean's
evaluator runs and its kernel does not check.

Terms. A description (`FileDescription`, Johnson/Desc/Block.lean) has three chains of sub-protocols: the
first, the shared and the second. A place (`Place`) is a sub-protocol's label in it. A chain's rows
are `rowsOf` (Johnson/RunOne/Sound/KeyListsAtFK.lean) of the chain's flat list: for each
sub-protocol its place and its number of rounds. A book (`ProverCoinCounts`, in the frame) is public data that
goes with a description. For each chain it has a table of the prover's parts that have coins of
their own: a part's address (`Addr`: a place, and the part's number there) with its count of coins
(`Due`). The frame calls a line of such a table a row too, as in the names of the first two tests;
below, rows are a description's. A book also has entries and cuts. An entry (`Ahead`) is a named
block of the coins of one part, the owner, that one part, the spender, is given; its field `once`
marks it as spent (true) or as carried (false). A cut gives, for a place, the number of rounds of
each part there. `KeyPub` (E2E/KeyBook.lean) is the structure of public data from which `keyBook`
computes the key file's book. Among its fields are the lookups' faces (`K3.Face`,
Johnson/Desc/First/Look/K3LookupGeneral.lean: the structure of a lookup's public parameters), the stages
of four proximity tests, and six sendings (`Sending`: the oracle messages that one part sends, each
with its counts of coins). The tests are numbered from 1 by their position in the list. Their names
are the frame's strings and are code.

Why. `ProverCoinCounts.clauses` takes a description. At the full size the key file's description is computed
from the public files and is no literal value, so it cannot be given to an evaluation as it is. But
ten of the eleven tests read nothing of the description but its rows. At public files in scope
(`InScope`, Ladder.lean) these rows are three literal lists (`fullFirst`, `fullShared`,
`fullSecond`, E2E/KeyPlaces.lean), under the hypotheses of `places_of_made` (same file) and of
`places_named` (E2E/KeyPlacesNamed.lean).

  `clauses_rows`: at every description F and every book B: `B.clauses F` is `clausesAt` at the rows
    of the three flat lists of F, at the frame's own third test (`masksOk` at each of the three
    chains) and at B
  `word_rows`: the same for the name of the first test that fails: `B.word F` is `wordAt` at these
    arguments
  `clausesAt r₁ r₂ r₃ masks B`: a definition: the eleven tests, each as the frame's name for it and
    a Bool that is true where the test passes. The third test ("a place states more mask words than
    its parts have coins") reads the sub-protocols' oracle messages, not the rows: its answer is the
    parameter `masks`, which the caller supplies
  `wordAt r₁ r₂ r₃ masks B`: a definition: the name of the first test of `clausesAt` that fails;
    `none` if every test passes
  `rows_places`: the places in `rowsOf bs` are the places of the sub-protocols bs, in order
  `KeyPub.rowsFirst`, `KeyPub.rowsShared`, `KeyPub.rowsSecond`: definitions: three lists of rows,
    one for each chain, computed from a `KeyPub`
  `KeyPub.word K B`: a definition: `wordAt` at these three lists and at B, with `masks` set to true
  `toyPub`: a definition: a small example `KeyPub`: two lookups, at `toyFace` (E2E/KeyBookFace.lean)
    and `toyFace₂`; three proximity tests of two stages and one (`rng`) of three
  `toyFace₂`: a definition: `toyFace` with three parts of keys and a table of 4 rows
  `toyBook`: a definition: `keyBook toyPub`, with the carried entries

The tests by `#guard`. At the rows of `toyPub`, with `masks` true, no test fails, at `toyBook` and
at the book without the carried entries (`keyBook toyPub false`). Each of the ten tests that read
rows is made to fail once, by one change: a line of a table, an entry or a cut of the book is added
or replaced; for the fourth test the sending `sIdx` of `toyPub` is replaced. The first test that
fails is then the one that the change aims at. With `masks` false the third test is the first that
fails. The other guards: `toyFace₂.ok`; counts of hidden values, of coins that the lookups take, of
entries, of the first chain's rounds and of tests; the cuts' places.

By what. `clauses_rows` unfolds `clausesAt`, rewrites the rows' places by `rows_places` and closes
by `rfl`, which unfolds `ProverCoinCounts.clauses` and `orderOf` (both in the frame) and `rowsOf`. `word_rows`
unfolds `ProverCoinCounts.word` (in the frame) and `wordAt` and rewrites by `clauses_rows`. `rows_places` is by
`simp` at `rowsOf`. The rows of section 2 are built from the places and `linkRows`
(E2E/KeyPlaces.lean), `spansOf` and `Span.rounds` (E2E/KeyBookFace.lean) and `testCut`
(E2E/KeyBook.lean). The entries that the guards add are built by `spend` and `carry`
(E2E/KeyBook.lean).

Limits.
- `clausesAt` repeats the text of `ProverCoinCounts.clauses` test by test. If the frame's tests are changed,
  `clauses_rows` no longer compiles: that is what the theorem is for.
- That the third test passes is shown of no book and at no description in this file. At the small
  key file its answer is set to true, and in one guard to false. E2E/KeyBookThird.lean and
  E2E/KeyBookThirdNamed.lean are about the third test.
- The three lists of rows of section 2 are definitions: that they are the rows of a description is
  not shown here, and no description is defined for `toyPub`. At the full size `full_rows`
  (E2E/KeyBookPassesNamed.lean) evaluates them to `fullFirst`, `fullShared` and `fullSecond`.
- The counts of coins in `toyPub` are literals chosen for the tests. They are not computed from
  sizes and the parameters of codes (`Codes`), as `KeyPub.of` (E2E/KeyBook.lean) computes them.
- That these tests pass says that the book is consistent with itself and with the rows. It does not
  say that any part of a prover fits the book.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBook

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place FileDescription)
open VerifiableInference.Desc.K3 (Face)
open Johnson.RunOne.Sound (rowsOf)
open ProofFile.Honest (Addr Ahead Due ProverCoinCounts dueAt masksOk)

/-! ## 1 The tests as a function of rows -/

/-- The frame's eleven tests on a book, as a function of rows. r₁, r₂, r₃: the rows of the first,
the shared and the second chain. masks: the third test's answer, which the caller supplies. The Bool
is true where the test passes. -/
def clausesAt (r₁ r₂ r₃ : List (Place × Nat)) (masks : Bool) (B : ProverCoinCounts) : List (String × Bool) :=
  let p₁ := r₁.map (·.1)
  let p₂ := r₂.map (·.1)
  let p₃ := r₃.map (·.1)
  let all := p₁ ++ p₂ ++ p₃
  let rows := B.first ++ B.shared ++ B.second
  let spent := (B.ahead.filter (·.once)).zipIdx
  let es := B.ahead.zipIdx
  let sizes := r₁ ++ r₂ ++ r₃
  [("a row stands at no place of its chain",
      B.first.all (fun r => p₁.contains r.1.place) &&
        B.shared.all (fun r => p₂.contains r.1.place) &&
        B.second.all fun r => p₃.contains r.1.place),
    ("a part has two rows", rows.all fun r => (rows.filter fun q => q.1 == r.1).length == 1),
    ("a place states more mask words than its parts have coins", masks),
    ("an entry's run is not within its owner's count", B.ahead.all fun a =>
      decide (a.start.f + a.count.f ≤ (dueAt rows a.owner).f) &&
        decide (a.start.e + a.count.e ≤ (dueAt rows a.owner).e)),
    ("an entry's spender does not stand behind its owner", B.ahead.all fun a =>
      all.contains a.owner.place && all.contains a.spender.place &&
        a.owner.before all a.spender),
    ("the shared chain is handed a coin of the first chain", B.ahead.all fun a =>
      !(p₁.contains a.owner.place && p₂.contains a.spender.place)),
    ("a coin stands in two entries that spend it", spent.all fun p => spent.all fun q =>
      p.2 == q.2 || !p.1.shares q.1),
    ("a coin that a part spends is handed to a part in front of it, or to itself as carried",
      es.all fun p => !p.1.once || es.all fun q =>
        p.2 == q.2 || !p.1.shares q.1 ||
          !(q.1.spender.before all p.1.spender || (q.1.spender == p.1.spender && !q.1.once))),
    ("a coin of the shared chain is spent outside it", B.ahead.all fun a =>
      !(a.once && p₂.contains a.owner.place && !p₂.contains a.spender.place)),
    ("a cut stands at no place, stands twice, has a part without a round or does not add up",
      B.cuts.all fun c =>
        sizes.lookup c.1 == some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
          (B.cuts.filter fun d => d.1 == c.1).length == 1),
    ("two entries bear one name", B.ahead.all fun a =>
      (B.ahead.filter fun b => b.name == a.name).length == 1)]

/-- The name of the first test that fails; `none` if every test passes. -/
def wordAt (r₁ r₂ r₃ : List (Place × Nat)) (masks : Bool) (B : ProverCoinCounts) : Option String :=
  ((clausesAt r₁ r₂ r₃ masks B).find? (!·.2)).map (·.1)

theorem rows_places {S Cl : Type} (bs : List (VerifiableInference.Desc.Block S Cl)) :
    (rowsOf bs).map (·.1) = bs.map (·.place) := by
  simp [rowsOf, List.map_map, Function.comp_def]

/-- **The frame's tests at a description are `clausesAt` at its rows** and at the frame's own third
test. -/
theorem clauses_rows {Xi : Type} (F : FileDescription Xi) (B : ProverCoinCounts) :
    B.clauses F =
      clausesAt (rowsOf F.first.blocksInOrder) (rowsOf F.shared.blocksInOrder) (rowsOf F.second.blocksInOrder)
        (masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared &&
          masksOk F.second.blocksInOrder B.second) B := by
  unfold clausesAt
  simp only [rows_places]
  rfl

/-- The same for the name of the first test that fails. -/
theorem word_rows {Xi : Type} (F : FileDescription Xi) (B : ProverCoinCounts) :
    B.word F =
      wordAt (rowsOf F.first.blocksInOrder) (rowsOf F.shared.blocksInOrder) (rowsOf F.second.blocksInOrder)
        (masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared &&
          masksOk F.second.blocksInOrder B.second) B := by
  unfold ProverCoinCounts.word wordAt
  rw [clauses_rows]

/-! ## 2 The rows, computed from a `KeyPub` -/

/-- The first chain's rows. A lookup's number of rounds is the sum over its spans (`spansOf`,
E2E/KeyBookFace.lean); a proximity test's is the sum of its cut (`testCut`, E2E/KeyBook.lean). -/
def KeyPub.rowsFirst (K : KeyPub) : List (Place × Nat) :=
  [(idxPlace, 2), (msgPlace, 2)] ++
    K.faces.zipIdx.flatMap (fun x => linkRows x.2 ((spansOf x.1).map Span.rounds).sum) ++
    [(rowsPlace, 0), (rngPlace, (testCut K.rng).sum), (battPlace, 2 + K.kCol), (wPlace, 2),
      (sealPlace, 1)]

/-- The shared chain's rows. -/
def KeyPub.rowsShared (K : KeyPub) : List (Place × Nat) :=
  [(frontPlace, 0), (pointPlace, 1), (foldedPlace, 2), (gammaPlace, 0), (locPlace, 1),
    (omegaPlace, 2), (joinsPlace, 0), (zetaPlace, 1), (splitPlace, 1),
    (foldedTestPlace, (testCut K.folded).sum), (omegaTestPlace, (testCut K.omega).sum),
    (sharedSealPlace, 1)]

/-- The second chain's rows. -/
def KeyPub.rowsSecond (K : KeyPub) : List (Place × Nat) :=
  [(tableSecondPlace, 0), (sourcesPlace, 0), (ownTestPlace, (testCut K.own).sum), (endPlace, 0)]

/-- The name of the first test that fails at a book B, at the rows computed from K, with the third
test's answer set to true. -/
def KeyPub.word (K : KeyPub) (B : ProverCoinCounts) : Option String :=
  wordAt K.rowsFirst K.rowsShared K.rowsSecond true B

/-! ## 3 A small example key file -/

/-- A second small face: `toyFace` (E2E/KeyBookFace.lean) with three parts, of 4, 2 and 2 keys, and
a table of 4 rows. -/
def toyFace₂ : Face := { toyFace with parts := [2, 1, 1], d := 2 }

/-- A small example key file. The counts of coins are literals chosen for the tests. -/
def toyPub : KeyPub :=
  { faces := [toyFace, toyFace₂], kCol := 2
    rng := [⟨0, 0, 2, 1⟩, ⟨1, 1, 1, 0⟩, ⟨2, 2, 0, 0⟩]
    folded := [⟨0, 0, 3, 0⟩, ⟨2, 2, 0, 0⟩]
    omega := [⟨0, 0, 1, 0⟩, ⟨2, 2, 0, 0⟩]
    own := [⟨0, 0, 2, 1⟩, ⟨2, 2, 0, 0⟩]
    sIdx := [⟨0, 0, 16, 3⟩]
    sMsg := [⟨4, 0, 160, 6⟩, ⟨0, 0, 5, 4⟩]
    sW := [⟨0, 2, 8, 3⟩, ⟨0, 0, 5, 6⟩]
    sFolded := [⟨0, 7, 0, 0⟩, ⟨0, 0, 7, 3⟩]
    sOmega := [⟨0, 5, 0, 0⟩, ⟨0, 0, 4, 3⟩]
    sOwnMask := [⟨0, 0, 3, 3⟩]
    rRng := ⟨0, 40⟩, rFolded := ⟨0, 20⟩, rOmega := ⟨0, 20⟩, rOwn := ⟨0, 20⟩ }

/-- The small key file's book, with the carried entries. -/
def toyBook : ProverCoinCounts := keyBook toyPub

#guard toyFace₂.ok
-- the two faces have 59 (a `#guard` in E2E/KeyBookFace.lean) and 84 hidden values (`Face.slots`).
-- The two lookups' entries take 55 + 78 coins of their first owner, `⟨msgPlace, 0⟩`, and 10 of the
-- second, `⟨idxPlace, 0⟩`: 59 + 84 in all
#guard toyFace₂.slots == 84
#guard (lookups toyPub.faces 0 0 0).2 == (55 + 78, 10)
#guard toyPub.spent.length == 17 + 23 + 5 && toyPub.carried.length == 20
-- the first chain's numbers of rounds, added up; the book's cuts are at those places of the three
-- lists of rows that have a round, in the rows' order
#guard (toyPub.rowsFirst.map (·.2)).sum == 2 + 2 + 41 + 57 + 12 + 4 + 2 + 1
#guard toyPub.cuts.map (·.1) ==
  ((toyPub.rowsFirst ++ toyPub.rowsShared ++ toyPub.rowsSecond).filter (·.2 != 0)).map (·.1)

-- eleven tests; with `masks` true none fails, at the book with the carried entries and without
#guard (clausesAt toyPub.rowsFirst toyPub.rowsShared toyPub.rowsSecond true toyBook).length == 11
#guard toyPub.word toyBook == none
#guard toyPub.word (keyBook toyPub false) == none

-- each of the ten tests that read rows is once the first that fails; the third is at `masks` false
#guard toyPub.word { toyBook with first := (⟨ownTestPlace, 0⟩, ⟨0, 1⟩) :: toyBook.first } ==
  some "a row stands at no place of its chain"
#guard toyPub.word { toyBook with first := (⟨idxPlace, 0⟩, ⟨0, 99⟩) :: toyBook.first } ==
  some "a part has two rows"
#guard wordAt toyPub.rowsFirst toyPub.rowsShared toyPub.rowsSecond false toyBook ==
  some "a place states more mask words than its parts have coins"
-- of the index-mask message's mask table the lookups take 10 coins and the batching's sumcheck
-- `1 + 2 * kCol`, here 5: with 15 coins in the sending no test fails, with 14 the fourth does
#guard toyPub.word (keyBook { toyPub with sIdx := [⟨0, 0, 15, 0⟩] }) == none
#guard toyPub.word (keyBook { toyPub with sIdx := [⟨0, 0, 14, 0⟩] }) ==
  some "an entry's run is not within its owner's count"
#guard toyPub.word { toyBook with
    ahead := spend "x" "sum" ⟨wPlace, 0⟩ 0 1 ⟨battPlace, 1⟩ :: toyBook.ahead } ==
  some "an entry's spender does not stand behind its owner"
#guard toyPub.word { toyBook with
    ahead := carry ⟨idxPlace, 0⟩ toyPub.sIdx 0 ⟨foldedTestPlace, 0⟩ :: toyBook.ahead } ==
  some "the shared chain is handed a coin of the first chain"
#guard toyPub.word { toyBook with
    ahead := toyBook.ahead ++ [spend "x" "sum" ⟨idxPlace, 0⟩ 14 1 ⟨wPlace, 0⟩] } ==
  some "a coin stands in two entries that spend it"
-- message 0 of the sending with the multiplicities, carried to part 1 of lookup 0: that part and
-- later parts spend coins of it
#guard toyPub.word { toyBook with
    ahead := carry ⟨msgPlace, 0⟩ toyPub.sMsg 0 ⟨lookPlace 0, 1⟩ :: toyBook.ahead } ==
  some "a coin that a part spends is handed to a part in front of it, or to itself as carried"
-- (at the book without the carried entries: with them the eighth test fails first)
#guard toyPub.word { keyBook toyPub false with
    ahead := (keyBook toyPub false).ahead ++
      [spend "x" "sum" ⟨omegaPlace, 0⟩ 6 1 ⟨ownTestPlace, 0⟩] } ==
  some "a coin of the shared chain is spent outside it"
#guard toyPub.word { toyBook with cuts := (wPlace, [1, 2]) :: toyBook.cuts.erase (wPlace, [2]) } ==
  some "a cut stands at no place, stands twice, has a part without a round or does not add up"
#guard toyPub.word { toyBook with
    ahead := toyBook.ahead ++ [{ spend "x" "sum" ⟨idxPlace, 0⟩ 15 1 ⟨wPlace, 0⟩ with
      name := (toyBook.ahead.map (·.name)).headD "" }] } ==
  some "two entries bear one name"

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.clauses_rows
#print axioms AtPublicFiles.KeyBook.word_rows
#print axioms AtPublicFiles.KeyBook.clausesAt
#print axioms AtPublicFiles.KeyBook.wordAt
#print axioms AtPublicFiles.KeyBook.rows_places
#print axioms AtPublicFiles.KeyBook.KeyPub.rowsFirst
#print axioms AtPublicFiles.KeyBook.KeyPub.rowsShared
#print axioms AtPublicFiles.KeyBook.KeyPub.rowsSecond
#print axioms AtPublicFiles.KeyBook.KeyPub.word
#print axioms AtPublicFiles.KeyBook.toyFace₂
#print axioms AtPublicFiles.KeyBook.toyPub
#print axioms AtPublicFiles.KeyBook.toyBook
