-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Plan.lean: the rounds of an entry file's hash chain, as a description for this development's
strict reader, for arbitrary sizes.

An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link (Fmt/M3Entry.lean says more). This library's
strict reader of such a file (`wholeChainX` in Fmt/Rules8X.lean) is generic. It takes a description
(`SpecX`) that says, round by round, how many bytes the prover sends, what the verifier draws, how
much proof of work is asked, and which Merkle trees are opened. This file builds that description
from the sizes of the protocol (the record `Par` of Fmt/M3Types.lean). Its list of rounds is the
list before the record's rows are added (`recordFmt`, OnBytes/Params/EntryDryRecord.lean). It has
definitions that compute and uses no Mathlib, neither directly nor through its imports.
The hash chain is the chain of hash values from which the verifier's challenges are drawn.

Sources. Written from the description of the entry file that belongs to the programs (the C++
implementation that comes with this Lean code): its overview of the entry file and its list of the
new rounds' names and kinds (its sections 3 and 4), and, in its part on an entry and the link, the
sections on what an entry says, on the file, on what the reader forms, on the first query, on the
rounds, and on trees and lists. Also from an answer (not a text that comes with this code) to a
question about the round named LINK, and from a restatement of an edition of the format page that is
not the one that ships (FORMAT.md; this file is not held against the page that ships):
R7.4 (the tree of every stored table has the number 0), R7.19 and R8.7 (the positions drawn in one
round are cut into parts, one for each stored tree), R4.6 (a stored table is opened under the root
that stands in the statement). The sources of the rounds here do not include the page's section 13
(present in a second edition, also not the one that ships), which in that edition rules the
same matters: R13.3 (the parts of an entry file), R13.5 (the items of the first query), R13.10 (the
rounds; the first stage of the proximity test is not written in the parameters but is the group
itself, with k = 1 + clog R and h = 0; the width of tree 0). The rounds here were compared with
R13.10, in an edition that is not the one that ships, in a second, independent reading, and no
difference was found.
In a third edition, also not the one that ships and not held against it, R13.10 also says what the
word "mask ahead" in the parameters means. This file renders the
value 1 (the fresh mask of the first fold is sent in tree 0).
The file's sources include no entry file of the programs.

Not independent of this library's own Python reference. Agreement with that reference is therefore
not agreement of two independent readings.

1. What the file contains.
   The rounds, in order:
   LINK point: The verifier draws v field elements, the point at which the rows of both tables are
     folded. The prover sends nothing.
   SEND seed: The prover sends the root of tree 0, which holds both folded rows and the fresh mask
     of the first fold. The verifier draws the seed of both samples: aR + aP coordinates and a
     nonzero factor.
   SEND answer: The prover sends two answers. Nothing is drawn.
   LINK: Proof of work. The verifier draws nu0 + nuj positions below 2^(the tables' depth) in one
     message, and no field element. Behind the nonce the file has the openings of the two stored
     trees: the first table's at the list made from the first nu0 positions, the copy's at the list
     made from the last nuj.
   LINK phi: The verifier draws clog l field elements, the point of comparison. The prover sends
     nothing.
   BAT: The verifier draws one field element. 1 + 2 + nu0 + nuj rows are batched.
   Then the rounds of the first toy's proximity test, from its first stage on (`laterRounds` in
   Fmt/M1Plan.lean). Its first tree is tree 0, whose columns have 3 (2 R + 1) elements of the base
   field. The rounds that the earlier toys also have are taken from Fmt/M1Plan.lean and
   Fmt/M2Plan.lean unchanged.
   The definitions:
   `rLinkPoint`, `rLink`, `rLinkPhi`, `nRows`, `width0`, `roundsOf P`, `planOf P`, `shT P`,
     `labelLink`, `stmOf root0 rootj`.
   `specOf P cfg others root0 rootj`: The description without the stored trees. The chain begins
     with 32 random bytes from the file.
   `specX P cfg others root0 rootj nonceB tsalt`: The description with the two stored trees at the
     round LINK. They belong to the statement's items 0 and 1 (`stmOf`) and to the parts (0, nu0)
     and (nu0, nuj) of the positions drawn. The roots stand in the statement only; the reader takes
     them from there (R4.6). `tsalt` is the number of salt bytes in a leaf of a stored table. By
     R13.10 that number belongs to the table's shape, not to the plan, so it is an argument of its
     own. Its default is `P.salt`, the one salt length that the record `Par` has, which is the
     plan's.
   `line`: A round as a row of numbers.


2. What is checked when the file compiles. No test stands in this file.




3. Theorems. None in this file.

The sizes can be read back from the parameters (`par_back`: stated in Fmt/M3ParOfLaws.lean, proved
in Fmt/M3ParOfLawsProofs.lean), under the hypothesis stated there (`P.small`, a test on the sizes).



4. What is not claimed.
   The first 40 bytes of an entry file (tag, version, the copy's root) stand in front of the chain
   and are not read here; see Fmt/M3Entry.lean.
   Tables with a record (s > 0) are not covered. For them the plan has a further first entry
   (FORMAT.md, R13.15), more rows are batched, and answers stand in the file and in the statement.
   The value 0 of "mask ahead" is not covered.
   The other items of the parameters are in Fmt/M3Items.lean, the decision in Fmt/M3Dec.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M3Types
import Fmt.M2Plan
import Fmt.Rules8X

namespace Fmt
namespace M3
open Fmt.M1 Fmt.M2

def rLinkPoint (v : Nat) : Round :=
  { entry := { name := "LINK point", drawE := v }, kind := .elems }
def rLink (work n a : Nat) : Round :=
  { entry := { name := "LINK", work := work, poss := n, logN := a }, kind := .positions }
def rLinkPhi (a : Nat) : Round := { entry := { name := "LINK phi", drawE := a }, kind := .elems }

/-- The number of rows under BAT: the equality row; the two sample rows; a row for each draw. -/
def nRows (P : Par) : Nat := 1 + 2 + P.nu0 + P.nuj

/-- The number of elements of the base field in a column of tree 0. -/
def width0 (P : Par) : Nat := M2.widthOf P.mems 1

/-- The rounds; none if `P.stages` is empty. -/
def roundsOf (P : Par) : List Round :=
  match P.stages with
  | [] => []
  | s :: rest =>
    [rLinkPoint P.v, rSeedN (P.aR + P.aP), rAnswers 2, rLink P.work (P.nu0 + P.nuj) P.T.a,
        rLinkPhi P.aPhi, rBatN (nRows P)] ++
      laterRounds P.work 0 (width0 P) s rest

/-- The plan. -/
def planOf (P : Par) (nonceB : Nat := 8) : Plan where
  field := P.fld
  salt := P.salt
  nonce := nonceB
  posB := 0
  samples := 1
  saved := 1
  entries := (roundsOf P).map (·.entry)

def labelLink : Nat := 0x4c4e4b01

/-- the statement: both tables' items -/
def stmOf (root0 rootj : ByteArray) : ByteArray :=
  tableItem "the first table" root0 [] ++ tableItem "the further table" rootj []

/-- The description, but for the stored trees. -/
def specOf (P : Par) (cfg : ByteArray) (others : List (String × ByteArray))
    (root0 rootj : ByteArray) (nonceB : Nat := 8) : Spec where
  label := labelLink
  plan := planOf P nonceB
  params := paramsBytes (planOf P nonceB) cfg others
  statement := stmOf root0 rootj
  rand := .inFile
  cfg := cfg
  rounds := roundsOf P

/-- the stored trees' one shape -/
def shT (P : Par) : Shape := { a := P.T.a, W := 2 ^ P.v, stored := true, tree := 0 }

/-- The description with its two stored trees. -/
def specX (P : Par) (cfg : ByteArray) (others : List (String × ByteArray)) (root0 rootj : ByteArray)
    (nonceB : Nat := 8) (tsalt : Nat := P.salt) : SpecX where
  base := specOf P cfg others root0 rootj nonceB
  stored := (roundsOf P).map fun r =>
    if r.entry.name == "LINK" then [⟨shT P, tsalt, 0, 0, P.nu0⟩, ⟨shT P, tsalt, 1, P.nu0, P.nuj⟩]
    else []

/-- A round as a line of a table: name, work, prover's bytes, roots, answers, elements drawn, of
these not 0, positions, range, rows batched. -/
def line (r : Round) : String × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (r.entry.name, r.entry.work, r.entry.msg, r.entry.roots, r.entry.answers, r.entry.drawE,
    r.entry.drawNZ, r.entry.poss, r.entry.logN, r.entry.rows)

/-! ## Tests -/

namespace PlanT
end PlanT








end M3
end Fmt
