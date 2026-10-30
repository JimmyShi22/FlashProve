-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Plan.lean: the rounds of the second toy's hash chain, as a description for the strict reader
of proof files, for arbitrary sizes.

The second toy is a chain of links: x_(m+1) = x_m * b_m, link by link. In the programs' files the
chain has three links; this file is written for any number L of links. A proof file for it holds the
prover's messages, proof-of-work nonces and Merkle openings of one hash chain. The strict reader of
such a file (`wholeChain` in Fmt/Rules8.lean) is generic. It takes a description (`Fmt.Spec`) that
says, round by round, how many bytes the prover sends, what the verifier draws, how much proof of
work is asked, and which Merkle trees are opened. This file builds that description from the sizes
of the protocol (the record `Par` of Fmt/M2Types.lean). It has definitions that compute, with tests,
and uses no Mathlib, neither directly nor through its imports.

Sources. Written from a revised version of the description of this toy that belongs to the programs
(the C++ implementation that comes with this Lean code): its sections 1 to 3 (the statement, the
codes and stages at the full and at the tiny parameters, the plan's two tables, the trees) and its
part on the frame, for the order of the prover's messages. The file's sources include no rules of
the format page (docs/format/FORMAT.md, which comes with the programs) on these matters. The page's
rules on them: R12.16 (the groups; k and h
follow from
the parameter item), R12.17 (the
rounds, and how each message is cut), R12.18 (what stands in a tree; the widths). This file has not
been held against the page as it ships, and may differ from it.
The page's test vector for the 58 rounds at the tiny parameters is
checked in Fmt/M2Items.lean. One difference in presentation only: R12.17 tells the rounds "SEND
seed, LOC" at the front of each later link, and here they close the link before. The sequence of
rounds is the same.

Why the sizes have one home. A group's members, the number k of its fold's rounds, the width of its
tree's columns, the length of a seed, the number of answers and the number of rows batched are all
taken from Fmt/M2Types.lean (memsOf, kOf, widthOf, seedLen, nAns, nRowsAt), and so are the sizes at
the full and at the tiny parameters (toyPar, tinyPar). The decision (Fmt/M2Dec.lean) uses the same
`memsOf`, `kOf` and `seedLen`, so in these plan and decision cannot drift apart. It does not use
`widthOf`, `nAns` or `nRowsAt`.

The programs' description numbers the rounds from 1, as the chain does. Its round i is the entry at
place i - 1 of the lists here.

1. What the file contains.
   The rounds, for L links and groups m = 1, .., L + 1 (the last group holds what the last link
   carries on), with V the number of variables of a link's sum-check:
   The first sending: SEND seed (the root of tree 0; the seed of group 1's samples). SEND answer
   (one answer for each sampled member of group 1; nothing is drawn).
   For each link m: ZERO (V field elements). PSC epsilon. V times PSC round. PSC Y (one nonzero
   element). PSC values. BAT (one element; `nRowsAt P m` rows are batched). FOLD epsilon. k_m times
   FOLD round. SEND seed (the root of tree m; the seed of group m + 1's samples). LOC (one answer
   for each sampled member of group m + 1; proof of work; t positions below 2^a; no field element).
   After LOC's nonce the file has the opening of tree m - 1.
   The last group: BAT, then the rounds of the first toy's proximity test from its first stage on
   (`laterRounds` in Fmt/M1Plan.lean). Its first tree is tree L.
   The rounds that the first toy also has are taken from Fmt/M1Plan.lean unchanged. Those taken are
   `rZero`, `rEps`, `rTwo`, `rY`, `rValues` and `laterRounds`.
   The definitions:
   `planOf P nonceB`: the plan (the part of the parameters that lists the rounds).
   `specOf P cfg others nonceB`: the description. The chain's label is 2, the statement is empty,
     the file begins with 32 random bytes, positions are not listed in the file, and a sample has
     one answer.
   `Par.planOK`: at least one link and at least two stages; the first stage is the last group's (the
     links' codes, the last group's k, no fold of masks, the links' number of positions).

2. What is checked when the file compiles (12 #guard tests). At the full and at the tiny parameters
   (`toyPar`: 76 rounds; `tinyPar`: 58 rounds) the rounds are, line for line, the table in a
   wording of the programs' description, not held against the description as it ships: name, kind,
   prover's bytes, roots, answers, elements drawn, how many of these must be nonzero, positions,
   range, work, rows batched. Both tables were copied into this file by a program. For each of the
   six trees: after which round it is opened, its number, depth and width. `Spec.ok` at both.

3. Theorems. None in this file. The sizes and the description, at the items of Fmt/M2Items.lean
   (`itemsOf P`), can be read back from the parameter bytes (`par_back`, `read_back`, `spec_back`:
   stated in Fmt/M2ParOfLaws.lean, proved in Fmt/M2ParOfLawsProofs.lean), under the hypotheses
   stated there (`P.small`, a test on the sizes; for the later statements also that the parameters
   fit and that the description is admissible).

4. What is not claimed.
   The other items of the parameters ("codes", "the chain of links") and the digest of the public
   file are arguments here. Fmt/M2Items.lean spells the items and the public file, by FORMAT.md,
   R12.12 to R12.15.
   The decision is not in this file (Fmt/M2Dec.lean).
   No file of the programs is compared with anything in this file. Their parameter bytes, their own
   table of the plan and every round of their proofs are compared elsewhere (Fmt/M2Theirs.lean and
   the files on their proofs, Fmt/M2Engine*.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1Plan

namespace Fmt
namespace M2
open Fmt.M1

/-- a seed's elements but the last, for group m -/
def seedOfGroup (P : Par) (m : Nat) : Nat :=
  seedLen (Nat.log2 P.C.l) (Nat.log2 P.Z.l) (memsOf P.links m)

/-! ## The kinds of rounds that this file adds to those of Fmt/M1Plan.lean -/

def rSeedN (n : Nat) : Round :=
  { entry := { name := "SEND seed", msg := 32, roots := 1, drawE := n + 1, drawNZ := 1 },
    kind := .seeds, items := [.root] }
def rAnswers (n : Nat) : Round :=
  { entry := { name := "SEND answer", msg := 24 * n, answers := n },
    kind := .nothing, items := List.replicate n .answer }
def rBatN (rows : Nat) : Round :=
  { entry := { name := "BAT", drawE := 1, rows := rows }, kind := .elems }
def rLoc (work t a n tree W : Nat) : Round :=
  { entry := { name := "LOC", work := work, msg := 24 * n, answers := n, poss := t, logN := a },
    kind := .positions, items := List.replicate n .answer,
    opens := [({ a := a, W := W, tree := tree }, .own tree)] }

/-- a link's sub-proof (ZERO to PSC values), its group's closing (BAT, FOLD epsilon, the FOLD
rounds), the next group's sending (SEND seed, LOC) -/
def linkRounds (P : Par) (m : Nat) : List Round :=
  [rZero P.V, rEps "PSC epsilon"] ++ List.replicate P.V (rTwo "PSC round") ++ [rY, rValues] ++
  [rBatN (nRowsAt P m), rEps "FOLD epsilon"] ++
    List.replicate (kOf (memsOf P.links m)) (rTwo "FOLD round") ++
  [rSeedN (seedOfGroup P (m + 1)),
    rLoc P.work P.t P.C.a (nAns P (m + 1)) (m - 1) (widthOf (memsOf P.links m) 1)]

/-- The rounds. -/
def roundsOf (P : Par) : List Round :=
  match P.stages with
  | [] => []
  | s :: rest =>
    [rSeedN (seedOfGroup P 1), rAnswers (nAns P 1)] ++
      (List.range P.links).flatMap (fun i => linkRounds P (i + 1)) ++
    [rBatN (nRowsAt P (P.links + 1))] ++
      laterRounds P.work P.links (widthOf (memsOf P.links (P.links + 1)) 1) s rest

def Par.planOK (P : Par) : Bool :=
  decide (1 ≤ P.links) && decide (2 ≤ P.stages.length) &&
  (match P.stages with
    | s :: _ =>
      s.C == P.C && s.Z == P.Z &&
        s.k == kOf (memsOf P.links (P.links + 1)) && s.h == 0 && s.t == P.t
    | [] => false)

/-- The plan. -/
def planOf (P : Par) (nonceB : Nat := 8) : Plan where
  field := P.fld
  salt := P.salt
  nonce := nonceB
  posB := 0
  samples := 1
  saved := 1
  entries := (roundsOf P).map (·.entry)

/-- The description. -/
def specOf (P : Par) (cfg : ByteArray) (others : List (String × ByteArray)) (nonceB : Nat := 8) :
    Spec where
  label := 2
  plan := planOf P nonceB
  params := paramsBytes (planOf P nonceB) cfg others
  statement := ByteArray.empty
  rand := .inFile
  cfg := cfg
  rounds := roundsOf P

/-- the bytes of a file but for its openings: the random bytes, the messages, the nonces -/
def fixedLen (P : Par) (nonceB : Nat := 8) : Nat :=
  32 + ((roundsOf P).map fun r => r.entry.msg + (if r.entry.work = 0 then 0 else nonceB)).sum

/-! ## Tests, at the text's two editions (Fmt/M2Types.lean: toyPar, tinyPar) -/

/-- a round as a line of the two tables below: name, kind, prover's bytes, roots, answers, elements
drawn, of these not 0, positions, range, work, rows batched -/
def line (r : Round) : String × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (r.entry.name, r.kind.num, r.entry.msg, r.entry.roots, r.entry.answers, r.entry.drawE,
    r.entry.drawNZ, r.entry.poss, r.entry.logN, r.entry.work, r.entry.rows)

#guard toyPar.planOK && tinyPar.planOK
#guard (toyPar.V, tinyPar.V) == (11, 5)
#guard [1, 2, 3, 4].map (fun m => (seedOfGroup toyPar m + 1, nAns toyPar m, nRowsAt toyPar m)) == [(15, 2, 5), (14, 4, 301), (14, 4, 301), (14, 1, 221)]
#guard [1, 2, 3, 4].map (fun m => (seedOfGroup tinyPar m + 1, nAns tinyPar m, nRowsAt tinyPar m)) == [(9, 2, 5), (8, 4, 21), (8, 4, 21), (8, 1, 11)]

-- the table of the full edition in a wording of the text, line for line: 76 rounds
#guard (roundsOf toyPar).map line == [
  ("SEND seed", 3, 32, 1, 0, 15, 1, 0, 0, 0, 0),
  ("SEND answer", 7, 48, 0, 2, 0, 0, 0, 0, 0, 0),
  ("ZERO", 1, 0, 0, 0, 11, 0, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 5),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 14, 1, 0, 0, 0, 0),
  ("LOC", 4, 96, 0, 4, 0, 0, 73, 15, 20, 0),
  ("ZERO", 1, 0, 0, 0, 11, 0, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 301),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 14, 1, 0, 0, 0, 0),
  ("LOC", 4, 96, 0, 4, 0, 0, 73, 15, 20, 0),
  ("ZERO", 1, 0, 0, 0, 11, 0, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 301),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 14, 1, 0, 0, 0, 0),
  ("LOC", 4, 24, 0, 1, 0, 0, 73, 15, 20, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 221),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 14, 1, 0, 0, 0, 0),
  ("CS", 4, 24, 0, 1, 1, 0, 73, 15, 20, 221),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 13, 1, 0, 0, 0, 0),
  ("CS", 4, 24, 0, 1, 1, 0, 74, 14, 20, 224),
  ("BASE lambda", 1, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("BASE", 4, 77280, 0, 0, 0, 0, 74, 14, 20, 0)]
-- the table of the tiny edition in a wording of the text, line for line: 58 rounds
#guard (roundsOf tinyPar).map line == [
  ("SEND seed", 3, 32, 1, 0, 9, 1, 0, 0, 0, 0),
  ("SEND answer", 7, 48, 0, 2, 0, 0, 0, 0, 0, 0),
  ("ZERO", 1, 0, 0, 0, 5, 0, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 5),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 8, 1, 0, 0, 0, 0),
  ("LOC", 4, 96, 0, 4, 0, 0, 3, 9, 6, 0),
  ("ZERO", 1, 0, 0, 0, 5, 0, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 21),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 8, 1, 0, 0, 0, 0),
  ("LOC", 4, 96, 0, 4, 0, 0, 3, 9, 6, 0),
  ("ZERO", 1, 0, 0, 0, 5, 0, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 21),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 8, 1, 0, 0, 0, 0),
  ("LOC", 4, 24, 0, 1, 0, 0, 3, 9, 6, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 0, 11),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 8, 1, 0, 0, 0, 0),
  ("CS", 4, 24, 0, 1, 1, 0, 3, 9, 6, 11),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 9, 1, 0, 0, 0, 0),
  ("CS", 4, 24, 0, 1, 1, 0, 3, 9, 6, 11),
  ("BASE lambda", 1, 24, 0, 0, 1, 0, 0, 0, 0, 0),
  ("BASE", 4, 3984, 0, 0, 0, 0, 3, 10, 6, 0)]
-- the trees: after which round (counted from 1) each is opened; its number, depth, width
#guard ((roundsOf toyPar).zipIdx.flatMap fun x => x.1.opens.map fun o => (x.2 + 1, o.1.tree, o.1.a, o.1.W)) == [(22, 0, 15, 9), (43, 1, 15, 15), (65, 2, 15, 15), (70, 3, 15, 9), (74, 4, 14, 18), (76, 5, 14, 12)]
#guard ((roundsOf tinyPar).zipIdx.flatMap fun x => x.1.opens.map fun o => (x.2 + 1, o.1.tree, o.1.a, o.1.W)) == [(16, 0, 9, 9), (31, 1, 9, 15), (47, 2, 9, 15), (52, 3, 9, 9), (56, 4, 9, 18), (58, 5, 10, 12)]
-- the roots: one each, in these rounds (counted from 1)
#guard ((roundsOf toyPar).zipIdx.filter fun x => x.1.entry.roots != 0).map (fun x => (x.2 + 1, x.1.entry.roots)) == [(1, 1), (21, 1), (42, 1), (64, 1), (69, 1), (73, 1)]
#guard ((roundsOf tinyPar).zipIdx.filter fun x => x.1.entry.roots != 0).map (fun x => (x.2 + 1, x.1.entry.roots)) == [(1, 1), (15, 1), (30, 1), (46, 1), (51, 1), (55, 1)]
-- the reader's own conditions on a description
#guard (specOf toyPar zero32 []).ok && (specOf tinyPar zero32 []).ok
#guard (specOf toyPar zero32 []).label == 2

end M2
end Fmt
