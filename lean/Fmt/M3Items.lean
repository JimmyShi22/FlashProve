-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Items.lean: the two parameter items "codes" and "the link" of an entry file's hash chain,
spelled from the sizes.

An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link (Fmt/M3Entry.lean says more). The first hash
query of an entry file's chain takes in the digest of the parameter bytes: the format's version, the
plan (Fmt/M3Plan.lean), the digest of the public files, and two further items. The item "codes"
lists the codes of the proximity test. The item "the link" lists the sizes of the link protocol.
This file spells both from the record `Par` of Fmt/M3Types.lean and puts the complete description
together. It has definitions that compute and uses no Mathlib, neither directly nor
through its imports.
To spell a value is to write it as the bytes that the format fixes for it. A word is a number
written in eight bytes, the lowest first (`u64n`, Fmt/Rules1.lean). The description that this file
puts together is a Lean value (`SpecX`, Fmt/Rules8X.lean), which the strict reader (`wholeChainX`)
takes beside the chain's bytes. On the group, a record and a folded row's tail see the head of
Fmt/M3Types.lean.

Sources. Written from the description of the entry file that belongs to the programs (the C++
implementation that comes with this Lean code), in its part on an entry and the link, the section on
the chain's first query. There the item "the link" is given word by word: the tables' shape (depth,
l, r; v; s; the salt bytes of a leaf; and, in editions of the format page that have it,
the tree's number); nu0; nuj; the number of the group's code in "codes"; the number of its mask
code; R; the
layout word "rows high"; the leaf class; "masks ahead"; the later stages (a length, then four words
for each stage); "the masks ride". The format page (docs/format/FORMAT.md, which comes with the
programs; this file has not been held against the page as it ships) has both items as rules:
R13.5 and R13.9. `linkWords` without
the tree's number was compared with R13.9, word for word (by reading, not machine-checked).

Why the tables' code is not in "codes". The description says that "codes" holds all codes of the
chain and gives no order. With `tabIn` the tables' own code comes first among the base codes. Three
reasons speak against that form: R12.2 fills the two lists stage by stage (a code is listed at the
first stage that uses it), and the tables' code belongs to no stage; "the link" spells that code by
its own three words, while the group's codes are numbers in "codes"; and the description gives 2,554
bytes for the parameters of the programs' entry of 19 rounds, where this file gives 2,578 with the
tables' code in the list and 2,554 without it (no test in this library checks these two counts). By
the programs' answer, read off the bytes, the tables' code does not stand in "codes". It stands
once, as the first three words of "the link". The other form is available through the switch
`tabIn`, for one set of files of this library's own Python reference.
The same answer gives, at the programs' own sizes, the order of the words, the leaf class 0, the
value 1 of "masks ahead" and of "the masks ride", and 40 salt bytes.
The file's sources include no entry file of the programs.
Not independent of this library's own Python reference. Nothing here shows that the reading is
right.

1. What the file contains.
   `baseCodes P tabIn`, `maskCodes P`: The two lists of the item "codes": the stages' codes in the
     order of the stages, each once. With `tabIn` the tables' code comes first (the other form).
   `linkWords P withTree tabIn tsalt`, `linkBytes`: The item "the link" as a list of numbers and as
     bytes. `withTree` adds the word for the tree's number (the form of the editions of the
     format page that have it).
   `nameLink`, `itemsOf P withTree tabIn tsalt`.
   `entrySpec P cfg root0 rootj tsalt`: The complete description: `specX` of Fmt/M3Plan.lean with
     `itemsOf` at its defaults for `withTree` and `tabIn` (both `false`).








   `tsalt` is the number of salt bytes in a leaf of a stored table. By R13.10 it belongs to the
   table's shape (the sixth word of the item), not to the plan (its third word). The record `Par`
   has one salt length only, so `tsalt` is an argument of its own, with `P.salt` as its default. At
   the programs' sizes both numbers are 40.

2. What is checked when the file compiles. No test stands in this file.














3. Theorems. None in this file. One statement is stated in Fmt/M3ParOfLaws.lean and proved in
Fmt/M3ParOfLawsProofs.lean: `par_back`. Under the hypothesis stated there, the sizes and `tsalt`
can be read back from the parameters. The hypothesis is `P.small` (a test on the sizes).



Notation:
   `T`: a `Code` (Fmt/M1Codes.lean): the tables' code (a, l, r);
   `v`, `s`, `nu0`, `nuj`, `R`: fields of `Par`, natural numbers, told in the head of
       Fmt/M3Types.lean;
     `v`: the tables have 2^v rows;
     `nu0`, `nuj`: how many columns of the first table and of the copy are drawn;
     `R`: the message that holds a folded row has R main rows;
   `high`: a `Bool`: the layout word "rows high" (`hiAt`, Fmt/M3Types.lean);
   `formatHash 169 0 1 zero32`: the parameters' digest (`paramsDigest`, Fmt/Rules4.lean).

4. What is not claimed.

   A table's name and the commitment ID (FORMAT.md, R4.10, R4.11) are not spelled here.
   Tables with a record (s > 0), a leaf class other than 0, and the value 0 of "masks ahead" or of
   "the masks ride" are not covered; `linkWords` writes these constants (0, 1 and 1; `P.s` is
   written as it is).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M3Plan
import Fmt.M1ParOf
import Fmt.M2Items

namespace Fmt
namespace M3
open Fmt.M1 Fmt.M2

def nameLink : String := "the link"

/-- The chain's base codes, each once: the tables' code first, if `tabIn`; then the stages'. -/
def baseCodes (P : Par) (tabIn : Bool) : List Code :=
  onceL ((if tabIn then [P.T] else []) ++ P.stages.map (·.C))
def maskCodes (P : Par) : List Code := onceL (P.stages.map (·.Z))

/-- The item "the link", as words. -/
def linkWords (P : Par) (withTree : Bool) (tabIn : Bool := false) (tsalt : Nat := P.salt) :
    List Nat :=
  [P.T.a, P.T.l, P.T.r, P.v, P.s, tsalt] ++ (if withTree then [0] else []) ++
  [P.nu0, P.nuj, noIn (baseCodes P tabIn) P.C, noIn (maskCodes P) P.Z, P.R, if P.high then 1 else 0,
    0, 1, P.stages.length - 1] ++
  ((P.stages.drop 1).flatMap fun s =>
      [noIn (baseCodes P tabIn) s.C, noIn (maskCodes P) s.Z, s.k, s.h]) ++ [1]

def linkBytes (P : Par) (withTree : Bool) (tabIn : Bool := false) (tsalt : Nat := P.salt) :
    ByteArray :=
  cat ((linkWords P withTree tabIn tsalt).map u64n)

/-- The two further items, from the sizes. -/
def itemsOf (P : Par) (withTree : Bool := false) (tabIn : Bool := false) (tsalt : Nat := P.salt) :
    List (String × ByteArray) :=
  [(nameCodes, codesBytes (baseCodes P tabIn) (maskCodes P)),
    (nameLink, linkBytes P withTree tabIn tsalt)]

/-- The description with its items. One number `tsalt` goes into the item's sixth word and into the
reader's field (`Stored.salt`, Fmt/Rules8X.lean). -/
def entrySpec (P : Par) (cfg root0 rootj : ByteArray) (tsalt : Nat := P.salt) : SpecX :=
  specX P cfg (itemsOf P false false tsalt) root0 rootj 8 tsalt























end M3
end Fmt
