-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Where.lean: where in the plans of a key file's three chains the rounds of each
part of the protocol lie, found from the names of the plans' entries and from the shapes alone.
Definitions with code; public data only: no view and no value of the field is read.

A key file has three chains (`KeyChains`, OnBytes/Params/Chains.lean). In this folder they are
numbered: the first is the one-time chain (`oneTime`), the second the shared chain (`shared`), the
third the field that the program calls `second`. The parameter bytes of each hold a plan: a list of
entries, one for each round, with the round's name and eleven numbers (`Fmt.Entry`, Fmt/Plan.lean).
The tests on these entries (Johnson/Desc/Key/Plan/) must know at which round a part begins. Here the
numbers of these rounds, counted from 0, are computed, and the plan is refused where the names do
not stand in the order that the protocol has.

Main names.
  `SharedPub`, `sharedPub`: what is read of a shared chain's parameters.
  `roundsNamed`, `nameAt`: the rounds of one name; the name of one round.
  `testLen`, `testNames`: how many rounds a proximity test has behind its batching round, and
    their names, from its stages.
  `WhereOmega`, `whereOmega`: the shared chain: the message with Omega, LIN zeta, SPLIT, and the
    batching round of the test on Omega's group.
  `WhereFolded`, `whereFolded`: the shared chain: the same, with LIN point, the message with the
    folded row, LOC, and the batching round of the test on the folded row's group.
  `firstBat`, `behindTest`: the one-time chain: the batching round of its proximity test, and the
    first round behind that test.
  `lookupLen`, `firstLookupAt`, `lookupsAt`: the one-time chain: the lookups, each with its first
    round.

Limits. Names and counts alone: that an entry's numbers are what the shapes ask is the matter of
Johnson/Desc/Key/Plan/. `whereOmega` and `whereFolded` compare the names behind a batching round
with the stages' names. Both are written for the shape that splits (the folded row and Omega have a
test each: SPLIT and two rounds BAT): any other shape is refused. `firstBat`, `behindTest` and
`lookupsAt` compare nothing and refuse nothing: they only point. `firstLookupAt` is a written 4. No
theorem. Nothing on soundness.

-/
import OnBytes.Key.OneTime
import OnBytes.Iop.Lin
import OnBytes.Iop.Bat
import OnBytes.Params.Chains

set_option autoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-! ## The shared chain -/

/-- What the tests on a shared chain's plan read of its parameters. -/
structure SharedPub where
  /-- the codes of the chain -/
  codes : Codes
  /-- the shape of the test on the table -/
  S : LinShape
  /-- the answers to each sample -/
  samples : Nat
  /-- the plan's rounds -/
  e : List Fmt.Entry

/-- These four values, of what the parameter bytes of a shared chain hold. -/
def sharedPub (s : Shared) : SharedPub := ⟨s.codes, s.lin, s.given.plan.samples, s.given.rounds⟩

/-- The numbers of the plan's rounds of one name. -/
def roundsNamed (es : List Fmt.Entry) (name : String) : List Nat :=
  (es.zipIdx.filter fun e => e.1.name == name).map (·.2)

/-- The name of round i; "(no round)" behind the plan's end. -/
def nameAt (es : List Fmt.Entry) (i : Nat) : String := ((es[i]?).map (·.name)).getD "(no round)"

/-- How many rounds a proximity test has behind its batching round. -/
def testLen (st : List IoppStage) : Nat := (st.dropLast.map fun s => s.k + 3).sum + 2

/-- The names of these rounds. -/
def testNames (st : List IoppStage) : List String :=
  (st.dropLast.flatMap fun s =>
    "FOLD epsilon" :: List.replicate s.k "FOLD round" ++ ["SEND seed", "CS"]) ++
    ["BASE lambda", "BASE"]

/-- Where the rounds that the test on Omega's group reads lie in the shared chain. -/
structure WhereOmega where
  /-- the seeds of the prover's message with Omega; the answers come in the next round -/
  seed : Nat
  /-- the round LIN zeta -/
  zeta : Nat
  /-- the round SPLIT -/
  split : Nat
  /-- the batching round of the test on Omega's group: the plan's second round BAT -/
  bat : Nat
  deriving Repr

/-- The places, from the plan's names alone. Refused unless the plan has one round LIN zeta, with
SEND seed and SEND answer in front of it and SPLIT behind it, and two rounds BAT, the second
followed by the names that the stages of the test on Omega's group ask. -/
def whereOmega (P : SharedPub) : Except String WhereOmega := do
  let [z] := roundsNamed P.e "LIN zeta" | throw "the plan has not just one round LIN zeta"
  if z < 2 then throw "LIN zeta comes too early"
  if nameAt P.e (z - 2) != "SEND seed" || nameAt P.e (z - 1) != "SEND answer" then
    throw "the two rounds before LIN zeta are not SEND seed, SEND answer"
  if nameAt P.e (z + 1) != "SPLIT" then throw "the round behind LIN zeta is not SPLIT"
  let [_, b] := roundsNamed P.e "BAT" | throw "the plan has not just two rounds BAT"
  if ((P.e.drop (b + 1)).take (testLen P.S.testOmega)).map (·.name) != testNames P.S.testOmega then
    throw "the plan's rounds behind the second BAT have other names than the stages ask"
  pure ⟨z - 2, z, z + 1, b⟩

/-- Where the rounds that the test on the folded row's group reads lie in the shared chain. -/
structure WhereFolded where
  /-- the round LIN point -/
  point : Nat
  /-- the seeds of the prover's message with the folded row; the answers come in the next round -/
  seedU : Nat
  /-- the round LOC -/
  loc : Nat
  /-- the seeds of the prover's message with Omega -/
  seedO : Nat
  /-- the round LIN zeta -/
  zeta : Nat
  /-- the round SPLIT -/
  split : Nat
  /-- the batching round of the test on the folded row's group: the plan's first round BAT -/
  bat : Nat
  deriving Repr

/-- The places, from the plan's names alone. Refused where `whereOmega` refuses, and unless the
plan has one round LIN point, followed by SEND seed, SEND answer, LOC and then the message with
Omega, and the first BAT follows SPLIT and is followed by the names that the stages of the test on
the folded row's group ask. -/
def whereFolded (P : SharedPub) : Except String WhereFolded := do
  let W ← whereOmega P
  let [p] := roundsNamed P.e "LIN point" | throw "the plan has not just one round LIN point"
  if nameAt P.e (p + 1) != "SEND seed" || nameAt P.e (p + 2) != "SEND answer" ||
      nameAt P.e (p + 3) != "LOC" then
    throw "the three rounds behind LIN point are not SEND seed, SEND answer, LOC"
  if p + 4 != W.seed then throw "the message with Omega does not follow LOC"
  let [b, _] := roundsNamed P.e "BAT" | throw "the plan has not just two rounds BAT"
  if b != W.split + 1 then throw "the first BAT does not follow SPLIT"
  if ((P.e.drop (b + 1)).take (testLen P.S.testU)).map (·.name) != testNames P.S.testU then
    throw "the plan's rounds behind the first BAT have other names than the stages ask"
  pure ⟨p, p + 1, p + 3, W.seed, W.zeta, W.split, b⟩

/-! ## The one-time chain -/

/-- The number of the plan's first round BAT. -/
def firstBat (one : OneTime) : Option Nat := (roundsNamed one.given.rounds "BAT").head?

/-- The number of the first round behind the test: the batching of the pending rows, or, where
there is none, the last sending. -/
def behindTest (one : OneTime) : Option Nat :=
  match roundsNamed one.given.rounds "BAT-sigma" with
  | i :: _ => some i
  | [] => (roundsNamed one.given.rounds "SEND seed").getLast?

/-- The number of rounds of a lookup. -/
def lookupLen (S : Lkp.Public) : Nat := (Lkp.roundsOf 0 S).length

/-- The number of the first round of the first lookup: before it the index-mask message and the
message with the multiplicities are sent and sampled, in two rounds each. -/
def firstLookupAt : Nat := 4

/-- The lookups as the lookup argument takes them, each with the number of its first round and the
number of mask entries that the lookups before it have taken of the index-mask message. -/
def lookupsAt (one : OneTime) : List (Lkp.Public × Nat × Nat) :=
  ((Wf.lookupsOf one.ranges (Wf.matrixOf one.lin)).foldl
    (fun (acc : Nat × Nat × List (Lkp.Public × Nat × Nat)) S =>
      (acc.1 + lookupLen S, acc.2.1 + Lkp.keyMasks S, (S, acc.1, acc.2.1) :: acc.2.2))
    (firstLookupAt, 0, [])).2.2.reverse

end VerifiableInference.Desc.Key
