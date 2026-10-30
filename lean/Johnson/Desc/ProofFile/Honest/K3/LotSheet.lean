-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotSheet.lean: a sheet for a program to print: the tests of
Honest/K3/Lot.lean at a proof file's description as it is made of three public files (policy.txt,
layout.txt, KL.bin). Definitions with code; no theorem; nothing is evaluated in this file.

Terms. Honest/K3/GLOSSARY.md ("lot", "site", "half", "description"). In this file: a sheet is a list
of lines of text: the sites, and each test's outcome.

What is defined.
  `sheetOf`: the sheet's lines, as a function of a public part, the segments' structures, a
    description's first chain and a lot's honest side (helpers: `bendLine`, `joinTwo`).
  `sheetLines`: the same, as a function of the three files: the public part as the description
    itself makes it (`pureRoad.pub`), the segments' structures of a request of zeros (`blankBy`),
    the description itself (`onlineDescription`).
Both are plain functions to lists of lines: no file is read and nothing is printed here.

What a print holds. The lookups' sites, one line each, with the number of rounds in front as a
number; the addresses at which no site could be made; how many of the tests accept, and the names of
those that reject; how many lots of the description have no honest side when this one alone is
given, and whether this lot is among them;
and four alterations, each with the number of tests that it makes fail and the number that is due:
every site's count of rounds in front one more; the round that samples a smallness test's matrix one
later; the first half's first two parts as one; another name for the lot. An alteration that makes
another number of tests fail than is due is marked.

Limits. The row is an argument: with `idleRow` (Lot.lean) the tests on the half's rounds and cut
test the stages' numbers alone, and nothing that a prover sends. The description is made at a
function that stands for the format's second hash function, which the caller passes. A print shows something
of the files that were read, and of no others.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block)

variable {V W X S Cl : Type}

/-- An alteration's line: what was altered, how many tests it makes fail, how many are due. -/
def bendLine (what : String) (due : Nat) (red : List String) : String :=
  s!"BEND: {what}: red {red.length}, due {due}" ++
    (if red.length == due then "" else " · NOT AS DUE: " ++ "; ".intercalate red)

/-- The first two parts of a row as one, by the stand-in's part: the rounds stay, the cut changes.
-/
def joinTwo : List (Part V W X) → List (Part V W X)
  | p :: q :: l => idlePart (p.moves.length + q.moves.length) :: l
  | l => l

/-- **The sheet's lines.** Here bs is the description's first chain as a flat list. -/
def sheetOf (Z : Pub) (G : Ground) (bs : List (Block S Cl)) (L : HLot V W X) : List String :=
  let sites := lookSites Z
  let hs := L.halves Z G
  let names := (onlineFirstChainBlockTables Z).map (·.name)
  let n := (K3Lot.addresses Z).length
  let ts := lotTests names n bs sites L.name hs
  let red := failing ts
  let up := sites.map fun s => { s with at_ := { s.at_ with base := s.at_.base + 1 } }
  let late := sites.map fun s => { s with rng := s.rng.map (· + 1) }
  let cut := match hs with
    | h :: l => { h with parts := joinTwo h.parts } :: l
    | [] => []
  [s!"links {Z.first.shape.link.length} · addresses {n} · sites {sites.length} · halves " ++
     s!"{hs.length} · blocks of the first chain {bs.length}, of them of the kind K3 " ++
     s!"{(bs.filter fun b => b.place.kind == .K3).length} · rounds of the first chain " ++
     s!"{(bs.map (·.rounds.length)).sum}"] ++
  sites.map siteLine ++
  (lookMisses Z).map ("NO SITE: " ++ ·) ++
  [s!"TESTS: yes {ts.length - red.length} of {ts.length}"] ++
  red.map ("NO: " ++ ·) ++
  [s!"lots of the description: {names.length}; without an honest side of their name, this one " ++
     s!"alone laid: {(lotsLacking Z [L]).length}; ours among them: " ++
     (if (lotsLacking Z [L]).contains L.name then "YES" else "no"),
   bendLine "every site's rounds in front one more" sites.length
     (failing (lotTests names n bs up L.name hs)),
   bendLine "the round that draws the matrix one later" (sites.filter (·.digits)).length
     (failing (lotTests names n bs late L.name hs)),
   bendLine "the first half's first two parts as one" 1
     (failing (lotTests names n bs sites L.name cut)),
   bendLine "another name for the lot" 1
     (failing (lotTests names n bs sites (L.name ++ "?") hs))]

/-- **The sheet's lines, as a function of the three public files.** Here o stands for the format's
second hash function. -/
def sheetLines (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (L : HLot V W X) : List String :=
  match pureRoad.pub o pol lay KL with
  | .error e => ["NO PUBLIC PART: " ++ e]
  | .ok Z =>
    match blankBy pureRoad.links Z with
    | none => ["NO RECORDS OF THE SEGMENTS for a request of zeros"]
    | some G =>
      match onlineDescription o pol lay KL with
      | .error e => ["NO DESCRIPTION: " ++ e]
      | .ok F => sheetOf Z G F.first.blocksInOrder L

end ProofFile.Honest.K3
