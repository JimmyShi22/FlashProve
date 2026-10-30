-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotOwners.lean: the honest side of the kind "lookup" (K3): tests on
public data on who owns a borrowed matrix. Definitions with code; nothing is evaluated in this file.

Terms. Honest/K3/GLOSSARY.md ("owner, borrowed matrix", "sources"). In this file: a link's list of
matrices holds matrices to which an earlier link has committed. The sources of keys and bits read
such a matrix under its owner's segment and name. They make both of the plan's field aId (`ownerOf`,
Honest/K3/WitOwner.lean). How aId names an owner was read there in the programs that make the plans'
lists. Here the owner so named is compared, at a public part, with its own list.

What is defined.
  `borrowedAt`: the borrowed matrices of a link's list, each with its number in the list.
  `ownerMat`: the entry of the owner's list that a borrowed matrix's aId names.
  `ownerTests` (`ownerAll`: at all links): the tests at one borrowed matrix, each with its name: the
    owner's segment stands in front of the link (this test also asks 256 ≤ aId, which its name does
    not tell: below 256 the subtraction in `ownerMat` would land on group 0); the owner's list has
    an entry at the number that aId names, and it bears a name; the sources read the matrix under
    that entry's name (the text of `ownerOf` against that of `ownerMat`); that entry is the owner's
    own (not borrowed in its turn); it has as many rows, and columns enough from the first column on
    that the borrower reads; it bears the borrower's aId.
  `ownerLines`: all links' borrowed matrices as lines for a print, the tests' count, and four
    alterations.

Users. Honest/K3/SeatFits.lean imports this file.

Limits. The tests are functions: they show something only where a program evaluates them at a public
part. They do not tell two entries of one shape apart: where the owner's list has a neighbour of its
own with as many rows and columns, an aId that names the neighbour passes: the first alteration
counts how many altered numbers are caught, and no number of them is due. `ownerOf` and `ownerMat`
are two texts of one reckoning: the third test compares one with the other, and neither with a third
thing. What compares the reckoning with the plan's own data is the last test: the plan's makers give
an owner's entry and its borrower one aId. The tests compare numbers and names of two lists of one
plan: that the reader of cells answers under the owner's segment and name is the reader's matter.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitOwner
import Johnson.Desc.ProofFile.Honest.K3.LotSheet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

/-- The borrowed matrices of a link's list, each with its number in the list. -/
def borrowedAt (X : OnBytes.Model.Verify.Public) (link : Nat) :
    List (OnBytes.Model.TMat × Nat) :=
  (tlOf X link).mats.toList.zipIdx.filter fun x => x.1.kind == 1

/-- The entry of the owner's list that a borrowed matrix's aId names. -/
def ownerMat (X : OnBytes.Model.Verify.Public) (M : OnBytes.Model.TMat) :
    Option OnBytes.Model.TMat :=
  (tlOf X (linkG X (M.aId / 256 - 1))).mats[M.aId % 256]?

/-- **The tests at one borrowed matrix**, each with its name. Here own is an alteration of the
owner's entry as it is fetched. What the last test can tell: the owner's entry is fetched by the
borrower's aId (its two halves read as group and number); so "it bears the borrower's aId" compares
that reckoning with the plan's own data. It does not tell which entry is meant: an aId that lands on
another own entry whose aId is made by the same rule passes it. -/
def ownerTests (X : OnBytes.Model.Verify.Public) (link : Nat) (M : OnBytes.Model.TMat)
    (own : OnBytes.Model.TMat → OnBytes.Model.TMat := id) : List (String × Bool) :=
  let at' := s!"link {link}, {M.name}: "
  let O? := (ownerMat X M).map own
  [(at' ++ "the owner's segment stands in front of the link",
      decide ((ownerOf X link M).1 < link) && decide (256 ≤ M.aId)),
   (at' ++ "the owner's list has an entry at the number that aId names, and it bears a name",
      O?.any fun O => O.name != ""),
   (at' ++ "the sources read the matrix under that entry's name",
      O?.any fun O => O.name == (ownerOf X link M).2),
   (at' ++ "that entry is the owner's own", O?.any fun O => O.kind == 0),
   (at' ++ "it has as many rows, and columns enough",
      O?.any fun O => O.m == M.m && decide (M.ttOff + M.k ≤ O.k)),
   (at' ++ "it bears the borrower's aId", O?.any fun O => O.aId == M.aId)]

/-- The tests at all borrowed matrices of the links below n. Here turn is an alteration of a matrix,
and own an alteration of the owner's entry. -/
def ownerAll (X : OnBytes.Model.Verify.Public) (n : Nat)
    (turn : OnBytes.Model.TMat → OnBytes.Model.TMat := id)
    (own : OnBytes.Model.TMat → OnBytes.Model.TMat := id) : List (String × Bool) :=
  (List.range n).flatMap fun link =>
    (borrowedAt X link).flatMap fun x => ownerTests X link (turn x.1) own

/-- **All links' borrowed matrices as lines**: for each: the link, its number in the list, its name,
rows and columns, aId, and the segment and name under which it is read; how many tests accept; those
that reject, by name; four alterations: every aId one more (another entry of the owner's list): how
many of the altered matrices have a failing test, with no number due; every aId 256 times the links'
number more (an owner that is not there): all six tests of every matrix are due to fail; every
owner's entry under another name: one test for each matrix; every owner's entry with its aId one
more: one test for each matrix. -/
def ownerLines (Z : Pub) : List String :=
  let X := Z.p.X
  let n := linkH X + 1
  let all := (List.range n).flatMap fun link => (borrowedAt X link).map fun x => (link, x)
  let ts := ownerAll X n
  [s!"links {n} · matrices in their lists " ++
     s!"{(List.range n).map fun l => (tlOf X l).mats.size} · borrowed {all.length}"] ++
  (all.map fun y =>
    s!"link {y.1} · matrix number {y.2.2} · {y.2.1.name} · {y.2.1.m} rows, {y.2.1.k} columns · " ++
      s!"aId {y.2.1.aId} · read under segment {(ownerOf X y.1 y.2.1).1}, name " ++
      s!"{(ownerOf X y.1 y.2.1).2}, from column {y.2.1.ttOff}") ++
  [s!"OWNERS: yes {ts.length - (failing ts).length} of {ts.length}"] ++
  (failing ts).map ("NO: " ++ ·) ++
  [s!"BEND: every aId one more: caught at {(all.filter fun y =>
      !(failing (ownerTests X y.1 { y.2.1 with aId := y.2.1.aId + 1 })).isEmpty).length} of " ++
      s!"{all.length} matrices (no number is due)",
   bendLine "every aId 256 times the links' number more" (6 * all.length)
     (failing (ownerAll X n fun M => { M with aId := M.aId + 256 * n })),
   bendLine "every owner's entry under another name" all.length
     (failing (ownerAll X n id fun O => { O with name := O.name ++ "?" })),
   bendLine "every owner's entry with its aId one more" all.length
     (failing (ownerAll X n id fun O => { O with aId := O.aId + 1 }))]

end ProofFile.Honest.K3
