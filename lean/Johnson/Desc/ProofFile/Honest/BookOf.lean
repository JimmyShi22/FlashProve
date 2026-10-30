-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookOf.lean: functions that compute a part of the book of coins
(`ProverCoinCounts`, Honest/Frame.lean) from public data alone. The book is the public table that says how the
rounds at each place are cut into parts and how many coins each part gets. This file computes the
cut and some counts of scalars; the book's rows and entries are computed by the other files of this
group (Honest/BookRows.lean to Honest/BookWhole.lean). Executable
definitions, and tests on made-up lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

Why it is a file of its own. A book is a check on the prover's sides only if it is made
independently of them. So this file reads a protocol description and names no prover's side: of this
folder it imports Honest/Frame.lean alone, for the types.

  1  `unitLen`, `unitsOf`, `cutOfNames`, `partsCut`, `partsCutFits`, `cutsIn`, `cutsOf`   the cut:
     into how many parts a place's rounds are cut, and how many rounds each part has, from the names
     of the plan's entries
  2  `scalarsIn`, `partsScalars`, `frameNames`, `segmentScalars`   the scalars: how many elements
     of the extension field a round, a part and a segment's own rounds send

The cut. Each entry of the plan (the protocol's list of rounds) has a name, and a sub-protocol
declares its rounds with their entries (`Block.rounds`). The names are read from the left, one unit
at a time:
  a masked sumcheck   "PSC epsilon", the "PSC round"s, then "PSC Y" and "PSC values" if present
  a sending           "SEND seed", then, if present, the round whose message holds its sample's
                      answers: "SEND answer", "LOC" or "CS" (docs/format/10-proof-file.md, 10.6)
  a fold              "FOLD epsilon", the "FOLD round"s; a "BAT" just before it belongs to it
  a base case         "BASE lambda", then "BASE" if present
  any other round     a unit by itself
Each unit is a part, except that a proximity test (the kind K12) has at most two parts. Its first
part is the first unit: the batching with the first fold if the names begin "BAT", "FOLD epsilon",
and the "BAT" alone if another name follows it. Its second part is all the rest.

The scalars. A round's entry states the bytes of its message, and how many roots and sample answers
are among them; the rest are scalars of 24 bytes. By the format's pages every scalar of a segment's
own rounds has a number, from 0, in the order of sending, and the segment's mask row has an entry
for each number (docs/format/11-1-machinery.md, "Scalars and their numbers"; segment, merge and
index-mask message are terms of these pages). So a book's entries are to be computed from these
counts, with one exception that the format names. At a merge the end value's mask is an entry of the
request's index-mask message, and the mask row's entry of that number masks nothing: there a part's
count is one more than what it spends of the mask row. The rounds that are not a segment's own are
recognised by their names (`frameNames`).

Limits.
  * The cut follows the rounds' names, not what a round does. A round under another name than the
    planner's is cut differently, and nothing here compares the names with the planner's. (The
    planner computes the plan from the public files.)
  * A caller's lead scalars are sent in a sumcheck's first message, so they count in its part.
  * `scalarsIn` subtracts and divides without a remainder: a message that is not made of roots,
    answers and whole scalars is counted as if it were.
  * `segmentScalars` skips a round by its name (`frameNames`): a scalar that was sent in such a
    round would not be counted.
  * No property of a prover or a protocol is stated.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place KindName)

/-! ## 1 The cut -/

/-- How many names at the start of the list equal `s`. -/
def headRun (s : String) (ns : List String) : Nat := (ns.takeWhile (· == s)).length

/-- 1 if the list begins with `s`, else 0. -/
def headOne (s : String) (ns : List String) : Nat := if ns.head? == some s then 1 else 0

/-- The number of rounds of a masked sumcheck after its "PSC epsilon". -/
def sumTail (ns : List String) : Nat :=
  let a := headRun "PSC round" ns
  let b := headOne "PSC Y" (ns.drop a)
  a + b + headOne "PSC values" (ns.drop (a + b))

/-- **The unit at the start of a list of names**: how many rounds it has. 0 for the empty list only.
-/
def unitLen : List String → Nat
  | [] => 0
  | n :: l =>
    if n == "PSC epsilon" then 1 + sumTail l
    else if n == "SEND seed" then
      1 + (if ["SEND answer", "LOC", "CS"].contains (l.headD "") then 1 else 0)
    else if n == "FOLD epsilon" then 1 + headRun "FOLD round" l
    else if n == "BAT" && l.head? == some "FOLD epsilon" then 2 + headRun "FOLD round" l.tail
    else if n == "BASE lambda" then 1 + headOne "BASE" l
    else 1

/-- A list of names, unit by unit: each unit's number of rounds. `k`: at most so many units. -/
def unitsOf : Nat → List String → List Nat
  | 0, _ => []
  | _, [] => []
  | k + 1, ns => unitLen ns :: unitsOf k (ns.drop (unitLen ns))

/-- **The cut of a place's rounds into parts**: each part's number of rounds, from the place's kind
and its rounds' names. -/
def cutOfNames (kind : KindName) (ns : List String) : List Nat :=
  match unitsOf ns.length ns with
  | [] => []
  | a :: rest =>
    if kind == .K12 then (if rest.isEmpty then [a] else [a, rest.foldl (· + ·) 0]) else a :: rest

variable {S Cl : Type}

/-- The cut at a sub-protocol. -/
def partsCut (b : Block S Cl) : List Nat := cutOfNames b.place.kind (b.rounds.map (·.entry.name))

/-- The parts' rounds add up to the sub-protocol's, and every part has a round. -/
def partsCutFits (b : Block S Cl) : Bool :=
  (partsCut b).foldl (· + ·) 0 == b.rounds.length && (partsCut b).all (· != 0)

/-- The cut at each sub-protocol of a list that has a round. -/
def cutsIn (bs : List (Block S Cl)) : List (Place × List Nat) :=
  (bs.filter fun b => !b.rounds.isEmpty).map fun b => (b.place, partsCut b)

/-- **The book's field `cuts`** for a description: the cut at every sub-protocol that has a round.
-/
def cutsOf {Xi : Type} (F : FileDescription Xi) : List (Place × List Nat) :=
  cutsIn F.first.blocksInOrder ++ cutsIn F.shared.blocksInOrder ++ cutsIn F.second.blocksInOrder

/-! ## 2 The scalars -/

/-- The number of scalars in a round's message: its bytes, less 32 for each root and 24 for each
sample answer, divided by 24. -/
def scalarsIn (r : Fmt.DeclaredRound) : Nat :=
  (r.entry.msg - 32 * r.entry.roots - 24 * r.entry.answers) / 24

/-- The sums of consecutive stretches of the first list; the second gives the stretches' lengths. -/
def sumsBy : List Nat → List Nat → List Nat
  | _, [] => []
  | l, k :: ks => (l.take k).foldl (· + ·) 0 :: sumsBy (l.drop k) ks

/-- How many scalars each part of a sub-protocol sends. -/
def partsScalars (b : Block S Cl) : List Nat := sumsBy (b.rounds.map scalarsIn) (partsCut b)

/-- The names of the rounds that are not a segment's own. -/
def frameNames : List String :=
  ["SEND seed", "SEND answer", "BAT", "FOLD epsilon", "FOLD round", "CS", "BASE lambda", "BASE",
    "LOC", "LINK", "LINK point", "LINK phi", "LIN point", "LIN zeta", "SPLIT", "REPLY", "SEAL",
    "LAST", "RECORD"]

/-- **The number of scalars in a segment's own rounds**, over the sub-protocols of the list whose
place has the link number `l`. -/
def segmentScalars (bs : List (Block S Cl)) (l : Nat) : Nat :=
  ((bs.filter fun b => b.place.link == some l).flatMap (·.rounds)).foldl
    (fun n r => if frameNames.contains r.entry.name then n else n + scalarsIn r) 0

/-! ### Tests on made-up lists -/

-- a sumcheck with ends; one without; two sumchecks, with a round before them and one between them
#guard cutOfNames .K3 ["PSC epsilon", "PSC round", "PSC round", "PSC Y", "PSC values"] == [5]
#guard cutOfNames .K3 ["PSC epsilon", "PSC round"] == [2]
#guard cutOfNames .K3 ["LKP", "PSC epsilon", "PSC round", "PSC Y", "PSC values", "ZERO",
  "PSC epsilon", "PSC round", "PSC round"] == [1, 4, 1, 3]
-- "PSC values" without "PSC Y" still ends the sumcheck; a second "PSC values" is a unit by itself
#guard cutOfNames .K3 ["PSC epsilon", "PSC round", "PSC values", "PSC values"] == [3, 1]
-- a sending with its answers in a "LOC"; a "LOC" with no sending before it; a sending with a
-- "SEND answer"; a sending without answers; two sendings around another round
#guard cutOfNames .K2 ["SEND seed", "LOC"] == [2]
#guard cutOfNames .K14 ["LOC"] == [1]
#guard cutOfNames .K1 ["SEND seed", "SEND answer"] == [2]
#guard cutOfNames .K1 ["SEND seed"] == [1]
#guard cutOfNames .K2 ["SEND seed", "SEND answer", "RNG", "SEND seed", "SEND answer"] == [2, 1, 2]
-- a "BAT" belongs to the fold that follows it; a round of another name is a unit by itself; so is a
-- "BAT" with no fold after it
#guard cutOfNames .K10 ["BAT", "FOLD epsilon", "FOLD round", "FOLD round"] == [4]
#guard cutOfNames .K9 ["BAT-sigma"] == [1]
#guard cutOfNames .K10 ["BAT", "PSC epsilon", "PSC round"] == [1, 2]
-- a proximity test: the batching with the first fold, then all the rest; the same names at another
-- kind
#guard cutOfNames .K12 ["BAT", "FOLD epsilon", "FOLD round", "SEND seed", "CS", "FOLD epsilon",
  "FOLD round", "FOLD round", "SEND seed", "CS", "BASE lambda", "BASE"] == [3, 9]
#guard cutOfNames .K10 ["BAT", "FOLD epsilon", "FOLD round", "SEND seed", "CS", "FOLD epsilon",
  "FOLD round", "FOLD round", "SEND seed", "CS", "BASE lambda", "BASE"] == [3, 2, 3, 2, 2]
-- a proximity test of one stage: the batching, then the base case
#guard cutOfNames .K12 ["BAT", "BASE lambda", "BASE"] == [1, 2]
-- no round: no part; one round: one part
#guard cutOfNames .frame [] == []
#guard cutOfNames .K7 ["REPLY"] == [1]

-- the scalars: a message of three scalars; of a root and nothing else; of one answer; of a root,
-- an answer and two scalars
#guard scalarsIn { entry := { name := "PSC round", msg := 72 } } == 3
#guard scalarsIn { entry := { name := "SEND seed", msg := 32, roots := 1 } } == 0
#guard scalarsIn { entry := { name := "SEND answer", msg := 24, answers := 1 } } == 0
#guard scalarsIn { entry := { name := "CS", msg := 104, roots := 1, answers := 1 } } == 2
#guard sumsBy [1, 2, 3, 4, 5] [2, 1, 2] == [3, 3, 9]

end ProofFile.Honest
