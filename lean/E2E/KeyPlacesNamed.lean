-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyPlacesNamed.lean: the theorems of E2E/KeyPlaces.lean and E2E/KeyBookTests.lean on the rows of
a description, at the key file's description at three public files Z in scope (`InScope`,
Ladder.lean). A description (`FileDescription`, Johnson/Desc/Block.lean) is a file's IOP as written in
Lean. It has three chains, the first, the shared and the second. Each gives a flat list of
sub-protocols, each at a place (`Place`: a label of chain, link, piece and kind). The rows of a flat
list (`rowsOf`, Johnson/RunOne/Sound/KeyListsAtFK.lean) are, for each sub-protocol, its place and
its number of rounds. The key file's description at Z is `keyFileDescription X N P` at any X, N, P with
`KeyNamed Z X N P` (both in E2E/KeyProtocolOverDescription.lean). `KeyNamed` is a structure of propositions: what
the library's `kseat_name` (Johnson/Goal/Description/KeySeat.lean) says of X, N, P, and one more
field. The theorems are general in Z, X, N, P, in the place p and in the book B. Theorems only.

Why X, N, P are parameters. A statement "there is a description with these rows" could not be joined
with another statement that begins "there is a description": the two need not be the same, because a
decision and rounds' data do not fix a description's sub-protocols. So no description is chosen
here. The theorems hold at all X, N, P that meet `KeyNamed`, and a file that has such X, N, P from
another theorem gets the rows of that same description.

  `places_named`: under scope and h: the rows of the three flat lists of `keyFileDescription X N P` are
    `fullFirst`, `fullShared` and `fullSecond` (E2E/KeyPlaces.lean): three literal lists of places
    and numbers of rounds, at the full size
  `clauses_named`: under scope and h, at every book B: `B.clauses (keyFileDescription X N P)`, the eleven tests
    that the frame (Johnson/Desc/ProofFile/Honest/Frame.lean) has on a book, is `clausesAt`
    (E2E/KeyBookTests.lean) at the three literal lists, at the frame's own third test at
    `keyFileDescription X N P`, and at B. A book (`ProverCoinCounts`, in the frame) is public data that goes with a
    description: for each chain a table of the prover's parts that have coins of their own; entries;
    cuts (these terms: the head of E2E/KeyBookTests.lean). The third test is `masksOk` (in the
    frame) at each chain's flat list and the table of B for that chain. It reads the sub-protocols'
    oracle messages, which the rows do not have, so it is not rewritten
  `start_named₁`, `start_named₂`, `start_named₃`: under scope and h, at every place p:
    `roundsInFront` (Johnson/Desc/ProofFile/Honest/ForKinds.lean: the number of a chain's rounds
    before the sub-protocol at a place) at the first, the shared and the second flat list of
    `keyFileDescription X N P` is `startIn` (E2E/KeyPlaces.lean) of `fullFirst`, `fullShared` and `fullSecond`
  `named_exists`: where the IOP's own test on the public files accepts
    (`protocolDataWellFormed (asDescriptionFiles Z) = true`; `protocolDataWellFormed`: Johnson/Goal/Description/Live.lean), there are X, N, P
    with `KeyNamed Z X N P`. It does not have the hypothesis scope

By what. `places_named` takes X₀ and m from the field `named` of h, unfolds `Key.descAt`
(Johnson/Desc/Key/Road.lean) to get that `Key.descriptionFromPlan` (Johnson/Desc/Key/Desc.lean) returns
`keyFileDescription X N P` at m, and calls `places_of_made` (E2E/KeyPlaces.lean) with the fields `plan` and
`wanted`. The three theorems on `roundsInFront` rewrite by `roundsInFront_rows` (E2E/KeyPlaces.lean)
and `places_named`; `clauses_named` rewrites by `clauses_rows` (E2E/KeyBookTests.lean) and
`places_named`. `named_exists` is `key_named` (E2E/KeyProtocolOverDescription.lean).

Hypotheses. scope: `InScope Z = true`: the three public files Z are in the scope of the library's
goals; among other things the layout file is that of the stored full-size example. h:
`KeyNamed Z X N P`: X, N, P are what the key file's description at Z is made of.

Limits.
- `KeyNamed` does not say that X, N, P are the only such. Its field `named` says that `Key.descAt`
  returns `keyFileDescription X N P` at what the library's `publicOfO`
  (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) returns at the files of Z, the layout file and the
  constant `Key.fixedDigest`. So any two triples that meet it give one and the same description; no
  theorem states that.
- Whether the third test passes is not shown in this file, of any book. `third_named`
  (E2E/KeyBookThirdNamed.lean) shows, under scope and h, that it passes at `keyFileDescription X N P` and one
  book: `keyBook K` at the K that `fullPub` returns.
- `KeyNamed` is a hypothesis. Values that meet it are shown only where `protocolDataWellFormed` accepts
  (`named_exists`). That it accepts is a theorem of the side library at the written files `storedPublicFiles`
  and `zGap` (`theLive_zFull`, AtFullSide/Top/LiveAtFull.lean; `theLive_zGap`,
  AtFullSide/Top/LiveAtPolicies.lean), which this file does not call. Both are in scope
  (`VerifierAndGoals.inScope_full`, `inScope_gap`, Johnson/Goal/Files/ScopeExample.lean).
- The full size only: the three literal lists are values at the full size, and `InScope` fixes the
  layout file.
- All limits of E2E/KeyPlaces.lean and E2E/KeyBookTests.lean.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookTests
import E2E.KeyProtocolOverDescription

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces descAt)
open Johnson.RunOne.Sound (rowsOf)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription key_named)
open ProofFile.Honest (ProverCoinCounts roundsInFront masksOk)

variable {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **In scope the rows of the key file's description are the three literal lists**: places and
numbers of rounds, in order. At every X, N, P with `KeyNamed Z X N P`. -/
theorem places_named (scope : InScope Z = true) (h : KeyNamed Z X N P) :
    rowsOf (keyFileDescription X N P).first.blocksInOrder = fullFirst ∧
      rowsOf (keyFileDescription X N P).shared.blocksInOrder = fullShared ∧
      rowsOf (keyFileDescription X N P).second.blocksInOrder = fullSecond := by
  obtain ⟨X₀, m, h0, hm, hd, -⟩ := h.named
  have hF : VerifiableInference.Desc.Key.descriptionFromPlan m = .ok (keyFileDescription X N P) := by
    unfold descAt at hd
    rw [hm] at hd
    exact hd
  exact places_of_made scope h0 hm hF h.plan h.wanted

/-- The number of the first chain's rounds before a place p is `startIn fullFirst p`. -/
theorem start_named₁ (scope : InScope Z = true) (h : KeyNamed Z X N P) (p : Place) :
    roundsInFront (keyFileDescription X N P).first.blocksInOrder p = startIn fullFirst p := by
  rw [roundsInFront_rows, (places_named scope h).1]

/-- The same for the shared chain, with `fullShared`. -/
theorem start_named₂ (scope : InScope Z = true) (h : KeyNamed Z X N P) (p : Place) :
    roundsInFront (keyFileDescription X N P).shared.blocksInOrder p = startIn fullShared p := by
  rw [roundsInFront_rows, (places_named scope h).2.1]

/-- The same for the second chain, with `fullSecond`. -/
theorem start_named₃ (scope : InScope Z = true) (h : KeyNamed Z X N P) (p : Place) :
    roundsInFront (keyFileDescription X N P).second.blocksInOrder p = startIn fullSecond p := by
  rw [roundsInFront_rows, (places_named scope h).2.2]

/-- **The frame's tests on a book B at the key file's description are `clausesAt` at the three
literal lists** and at the frame's own third test at that description. -/
theorem clauses_named (scope : InScope Z = true) (h : KeyNamed Z X N P) (B : ProverCoinCounts) :
    B.clauses (keyFileDescription X N P) =
      clausesAt fullFirst fullShared fullSecond
        (masksOk (keyFileDescription X N P).first.blocksInOrder B.first &&
          masksOk (keyFileDescription X N P).shared.blocksInOrder B.shared &&
          masksOk (keyFileDescription X N P).second.blocksInOrder B.second) B := by
  obtain ⟨h1, h2, h3⟩ := places_named scope h
  rw [clauses_rows, h1, h2, h3]

/-- Where the IOP's own test on the public files accepts, there are X, N, P with `KeyNamed Z X N P`.
It is `key_named` (E2E/KeyProtocolOverDescription.lean); it does not have the hypothesis scope. -/
theorem named_exists (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : ∃ X N P, KeyNamed Z X N P :=
  key_named Z live

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.places_named
#print axioms AtPublicFiles.KeyBook.start_named₁
#print axioms AtPublicFiles.KeyBook.start_named₂
#print axioms AtPublicFiles.KeyBook.start_named₃
#print axioms AtPublicFiles.KeyBook.clauses_named
#print axioms AtPublicFiles.KeyBook.named_exists
