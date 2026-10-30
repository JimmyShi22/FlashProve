-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookPassesNamed.lean: the key file's book of coins at the full size passes the tests that the
frame (Johnson/Desc/ProofFile/Honest/Frame.lean) has on a book, at the key file's description at the
public files, if the third of these tests passes there: `book_named`. The book is `keyBook K`
(E2E/KeyBook.lean) at the K that `fullPub` returns (E2E/KeyBookAtWritten.lean). K is a `KeyPub`, the
public data from which the book is computed, and `fullPub` is the one at the library's sizes of the
full size (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean). The theorem is at the full size
only; it is general in the public files Z in scope and in the X, N, P with `KeyNamed Z X N P`. It
joins `places_named` (E2E/KeyPlacesNamed.lean) with `passes` (E2E/KeyBookPasses.lean), whose two
hypotheses are obtained here by evaluation in Lean's kernel (`decide +kernel`). The third test is
proved in E2E/KeyBookThirdNamed.lean, which then calls `book_named`. One definition, theorems, and
one negative test.

Terms. A description (`FileDescription`, Johnson/Desc/Block.lean) is the IOP of a file as written in Lean.
It has three chains of sub-protocols: the first, the shared and the second. A place (`Place`) is a
sub-protocol's label. A chain's rows (`rowsOf`, Johnson/RunOne/Sound/KeyListsAtFK.lean) are, for
each sub-protocol, its place and its number of rounds; `fullFirst`, `fullShared` and `fullSecond`
(E2E/KeyPlaces.lean) are three literal lists of such rows. A book (`ProverCoinCounts`, in the frame) is public
data that goes with a description: a table for each chain, entries and cuts. A row of a table is the
address of a part of the prover (`Addr`: a place, and the part's number there) with that part's
count of coins (`Due`: f of the base field, e of the extension field). An entry (`Ahead`) is a named
block of the coins of one part, the owner, that one part, the spender, is given; its field `once`
marks it as spent (true) or as carried (false). A cut gives, for a place, the number of rounds of
each part there. The frame has eleven tests on a book at a description (`ProverCoinCounts.clauses`). `ProverCoinCounts.word`
is the name of the first test that fails; `none`: every test passes. `wordAt`
(E2E/KeyBookTests.lean) is the same as a function of three lists of rows, of the third test's answer
and of the book: the other ten tests read nothing of a description but its rows. A face (`K3.Face`,
Johnson/Desc/First/Look/K3LookupGeneral.lean) is the structure of a lookup's public parameters; `K.faces`
has one for each lookup. A sending (`Sending`, E2E/KeyBook.lean) is the list of the oracle messages
that one part sends, each with its counts of coins. `atFull f` (E2E/KeyBookAtWritten.lean) is f at
the K that `fullPub` returns, and false if `fullPub` is `none`.

  `book_named`: under the four hypotheses below: `(keyBook K).word (keyFileDescription X N P) = none`. In this
    form `Owed` (Johnson/Desc/ProofFile/Honest/Owed.lean, the field `book`) and theorems under
    Johnson/Desc/ProofFile/Honest/Law/Rule/ take it as a hypothesis on a book
  `book_rows`: if `fullPub = some K`, then
    `wordAt fullFirst fullShared fullSecond true (keyBook K) = none`: at the three literal lists of
    rows, and with the third test's answer set to true, no test fails at the book
  `thirdAt F B`: a definition: the frame's third test ("a place states more mask words than its
    parts have coins") at a description F and a book B: `masksOk` (in the frame) at each of the
    three chains. It reads the sub-protocols' oracle messages, not the rows
  `full_small`, `full_rows`, `full_two`: at the K of `fullPub`: the Boolean `small K`
    (E2E/KeyBookPasses.lean) is true; the rows that E2E/KeyBookTests.lean computes from K
    (`K.rowsFirst`, `K.rowsShared`, `K.rowsSecond`) are the three literal lists; K has two faces.
    Each is stated by `atFull` and proved by evaluation in Lean's kernel
  `full_small_no`: a negative test, by the kernel too: `small` is false at that K with `sIdx`, the
    sending of the index-mask message, replaced by one message of 84 coins, all in its mask table.
    That is one coin fewer than the book's spent entries take of that table: the lookups' take 48
    and the batching's takes `1 + 2 * K.kCol`. That the sum is 85 is not tested here: a `#guard` has
    that at the K of `fullPub` the table has 256 coins (E2E/KeyBookAtWritten.lean)
  `full_made`: there is a K with `fullPub = some K`. By evaluation in Lean's kernel
  `of_atFull`: if `atFull f = true` and `fullPub = some K`, then `f K = true`

What is evaluated, and what is not. Of the book, `small K` reads the ten rows of the three tables.
It reads the 18 cuts; the two lookups' cuts are lists of 935 and 920 numbers, which are added up. It
reads the next unused coins of the lookups' two owners (`K.top`); for these the coins that the two
lookups take, 34885 and 48, are counted in two lists that have one flag for each coin. And it reads
the 25 entries that are not the lookups' (`K.others`): each by itself, each pair of them, and each
compared with the lookups' entries as a whole: a spent one with four numbers (for each of the two
owners, the first coin that the lookups take and the next unused coin after them), a carried one
with the two lookups' places. It reads nothing of the lookups' 983 + 967 entries themselves
(`K.looks`), and it compares no names. What the tests say of these entries, of their pairs and of
all names is proved in E2E/KeyBookPasses.lean at any two faces, from the theorems of
E2E/KeyBookTile.lean and E2E/KeyBookNames.lean. The numbers 935, 920, 34885, 48 and 983 + 967 are
expected values of `#guard`s in E2E/KeyBookAtWritten.lean; ten, 18 and 25 are read off the
definitions `keyBook`, `KeyPub.cuts` (at two faces) and `KeyPub.others`.

By what. `book_named` rewrites `ProverCoinCounts.word` at the description by `word_rows` (E2E/KeyBookTests.lean)
to `wordAt` at the description's rows and at the frame's third test. It rewrites these rows to the
three literal lists by `places_named` (E2E/KeyPlacesNamed.lean), and the third test's answer to true
by the hypothesis third; what is left is `book_rows`. `book_rows` is `passes`
(E2E/KeyBookPasses.lean) at K: its hypothesis `K.faces = [f₀, f₁]` comes from `full_two`, its
hypothesis `small K = true` is `full_small`, and `full_rows` rewrites the rows computed from K to
the literal lists. `of_atFull`, which unfolds `atFull`, takes each of the three from `atFull` to K.

Hypotheses of `book_named`. scope: `InScope Z = true` (Ladder.lean): the three public files Z are in
the scope of the library's goals; among other things the layout file is that of the stored full-size
example. h: `KeyNamed Z X N P` (E2E/KeyProtocolOverDescription.lean): X, N, P are what the key file's description
at Z is made of: the library's `Key.descAt` (Johnson/Desc/Key/Road.lean) returns `keyFileDescription X N P` at
the files of Z, and the description's own three tests accept. hK: `fullPub = some K`; `full_made`
shows that there is such a K. third: `thirdAt (keyFileDescription X N P) (keyBook K) = true`.

Limits.
- The third test is a hypothesis of `book_named`, and `book_rows` has its answer set to true.
  Nothing on it is shown in this file. `third_named` (E2E/KeyBookThirdNamed.lean) proves it under
  the three other hypotheses of `book_named`, and `book_passes` there is `book_named` without it.
  The test says of every sub-protocol of the three chains: the mask words that its oracle messages
  declare (`maskWords`, in the frame) are at most f + 3 e of the rows at its place in the chain's
  table, added up. At a place without a row that bound is 0.
- The book is `keyBook K` with its carried entries (`KeyPub.carried`). These entries rest on a
  reading: see the head of E2E/KeyBook.lean, whose limits on them and on the book's counts apply.
  The theorems hold of the book with them.
- That the tests pass says that the book is consistent with itself and with the description's rows.
  It does not say that any part of a prover fits the book.
- The full size only: `fullPub`, `fullFirst`, `fullShared` and `fullSecond` are values at the full
  size, and `InScope` fixes the layout file. Nothing is shown at another size.
- K is computed from the library's value `keyFull`. The description enters `book_named` by its rows
  and by the hypothesis third only: that `KeyPub.of` returns the same K at the sizes from which the
  description at Z is made is not stated here. `pub_of_made` (E2E/KeyBookSourced.lean) states it,
  under hypotheses of its own.
- `KeyNamed` is a hypothesis: no X, N, P that meet it are shown here. `key_named`
  (E2E/KeyProtocolOverDescription.lean) shows some where the IOP's own test on the public files accepts.
- The negative test is one example, and it does not say which conjunct of `small` is false. It is
  stated by `atFull`, which is false also where `fullPub` is `none`; `full_made` shows that it is
  not `none`.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookPasses
import E2E.KeyPlacesNamed
import E2E.KeyBookAtWritten

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open VerifierAndGoals (PublicFiles InScope)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open ProofFile.Honest (ProverCoinCounts masksOk)

/-- The frame's third test at a description F and a book B: `masksOk`
(Johnson/Desc/ProofFile/Honest/Frame.lean) at each of the three chains. -/
def thirdAt {Xi : Type} (F : FileDescription Xi) (B : ProverCoinCounts) : Bool :=
  masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared && masksOk F.second.blocksInOrder B.second

/-! ## 1 At the library's sizes of the full size -/

theorem full_small : atFull small = true := by decide +kernel

theorem full_rows : atFull (fun K =>
    K.rowsFirst == fullFirst && K.rowsShared == fullShared &&
      K.rowsSecond == fullSecond) = true := by
  decide +kernel

theorem full_two : atFull (fun K => K.faces.length == 2) = true := by decide +kernel

/-- A negative test: `small` is false at the K of `fullPub` with the sending `sIdx` replaced by one
message of 84 coins. That is one coin fewer than the book's spent entries take of the index-mask
message (see this file's head). -/
theorem full_small_no : atFull (fun K => small { K with sIdx := [⟨0, 0, 84, 0⟩] }) = false := by
  decide +kernel

theorem of_atFull {f : KeyPub → Bool} (h : atFull f = true) {K : KeyPub} (hK : fullPub = some K) :
    f K = true := by
  unfold atFull at h
  rw [hK] at h
  exact h

/-- **At the literal rows, with the third test's answer set to true, no test fails at the book.**
The rows are `fullFirst`, `fullShared` and `fullSecond`; the book is `keyBook K` at the K of
`fullPub`. -/
theorem book_rows (K : KeyPub) (hK : fullPub = some K) :
    wordAt fullFirst fullShared fullSecond true (keyBook K) = none := by
  have h2 := of_atFull full_two hK
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using h2)
  have hr := of_atFull full_rows hK
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  have := passes K f₀ f₁ hf (of_atFull full_small hK)
  rwa [hr.1.1, hr.1.2, hr.2] at this

/-! ## 2 At the key file's description at the public files -/

/-- **At the key file's description no test fails at the book, if the third test passes there.** At
public files Z in scope and every X, N, P with `KeyNamed Z X N P`; the book is `keyBook K` at the K
of `fullPub`. -/
theorem book_named {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (scope : InScope Z = true) (h : KeyNamed Z X N P) (K : KeyPub) (hK : fullPub = some K)
    (third : thirdAt (keyFileDescription X N P) (keyBook K) = true) :
    (keyBook K).word (keyFileDescription X N P) = none := by
  obtain ⟨h1, h2, h3⟩ := places_named scope h
  unfold thirdAt at third
  rw [word_rows, h1, h2, h3, third]
  exact book_rows K hK

/-- There is a K with `fullPub = some K`: `KeyPub.of` returns a value at the library's sizes of the
full size. -/
theorem full_made : ∃ K, fullPub = some K := Option.isSome_iff_exists.1 (by decide +kernel)

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.full_small
#print axioms AtPublicFiles.KeyBook.full_rows
#print axioms AtPublicFiles.KeyBook.full_two
#print axioms AtPublicFiles.KeyBook.full_small_no
#print axioms AtPublicFiles.KeyBook.book_rows
#print axioms AtPublicFiles.KeyBook.book_named
#print axioms AtPublicFiles.KeyBook.full_made
#print axioms AtPublicFiles.KeyBook.thirdAt
#print axioms AtPublicFiles.KeyBook.of_atFull
