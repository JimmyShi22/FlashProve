-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Frame.lean: the proximity test (the kind K12) as a block (Johnson/Desc/Block.lean):
its frame: in which order its parts stand, which rounds are whose, and the three tests that are the
frame's own. Definitions with code; no theorem.

  the test := the front (no round) · the batching (1 round) · is the group the first stage's? ·
              for each stage but the last: the fold (1 + k rounds) · the code switch (2 rounds) ·
                the batching behind it (no round) · has the next mask come? ·
              the base case (2 rounds).

ROUNDS, and with them READS, come of the numbers of the place, for the whole test at once
(`H2U.roundsOfNums`, `H2U.testOracles`: Johnson/Desc/K12/TestEntries.lean); the frame cuts that list
among the parts by the counts above. A part (`Part`) is its decision on its own rounds and columns,
and what it asks of the plan.
THE LOOP OVER THE STAGES RUNS WHERE THE BLOCK IS MADE, NOT WHERE IT DECIDES: the stages are numbers
of the place. So "the present stage" and "the stages behind it" are in no carried record.
The parts are fields of a record (`Parts`), filled in other files, over one record T that lives
inside the test. The frame reads T through two of that record's fields alone.
THE FRONT STANDS INSIDE THE KIND: the schedule's state at the test's front, and the clauses on the
claims that lie open on the group, are asked once, by the block's first part, wherever the kind is
seated: no chain's own door has to remember them.
The frame's own tests:
  on the plan alone: the stages' sizes fit together (`sizesOk`, Johnson/Desc/K12/Sizes.lean); the
    numbers give rounds, and as many as the counts above add up to (`roundsIn`); the place's oracle
    messages have the log-lengths and widths that the numbers give (`H2U.testOracles`);
  on the carried record, behind the batching: the group's two codes and its tables' k and h are the
    first stage's (`firstFits`);
  on the carried record, behind each stage: if the masks come early, the message that holds the next
    stage's mask has come.
None of them reads a value that a prover sends.
Limits: how T is entered from a chain's record and left again: `Block.inside`, with two functions
that are not here. No part is here, and nothing has run on a proof. The rounds' maker serves one
answer to a sample and masks that come early (its own limits); `answers` and `early` are fields all
the same: where they say otherwise, the file's test of the rounds against the plan is what refuses.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.Desc.K12.Sizes
import Johnson.Desc.K12.TestEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open Fmt.M1 (Code Stage)

/-- The numbers of a place at which a proximity test stands. -/
structure P12 where
  place : Place
  /-- the stages, and what the rounds need beside them -/
  nums : H2U.TestNums
  /-- for each stage: the numbers of its main code and its mask code in the record's lists of codes
  (the frame does not read them: the parts do) -/
  idx : List (Nat × Nat)
  /-- for each round of the test, for each root that it sends: the oracle message beneath it, with
  who shares a symbol -/
  oracles : List (List Oracle)
  /-- the oracle messages that must have been sent before the test's first draw: the chain, and the
  message's number in its chain's order of sending -/
  before : List (Nat × Nat)
  /-- the answers to an out-of-domain sample -/
  answers : Nat
  /-- the masks come early: each stage's mask is sent with the message that makes the stage -/
  early : Bool

/-- A part: what it asks of the plan alone; and, from the record, its own rounds as a view shows
them and the columns that it is owed, the next record, or a refusal under the name of the test that
refused (as `Block.decide`). -/
structure Part (T : Type) where
  planOk : Bool := true
  decide : T → List Fmt.RoundView → List (List (Nat × List UInt64)) → Except String T

/-- **The parts.** T: the record inside the test. The number: the stage's, from 0. The list: the
declared rounds that the frame has cut for the part. -/
structure Parts (T : Type) where
  /-- what is asked of the record before anything is spent: it has no round -/
  front : P12 → Part T
  /-- all pending claims of the group become one -/
  bat : P12 → List Fmt.DeclaredRound → Part T
  /-- the stage's rows become three single rows -/
  fold : P12 → Nat → Stage → List Fmt.DeclaredRound → Part T
  /-- from a stage to the next; the flag: the next is the last -/
  switch : P12 → Nat → Stage → Stage → Bool → List Fmt.DeclaredRound → Part T
  /-- all claims on the stage that was entered become one; it has no round of its own: the list is
  the switch's, whose last entry counts these claims -/
  batBehind : P12 → Nat → Stage → List Fmt.DeclaredRound → Part T
  base : P12 → Nat → Stage → List Fmt.DeclaredRound → Part T
  /-- the group under test as the record has it: its two codes; its tables' k and h -/
  group : T → Option (Code × Code × Nat × Nat)
  /-- the message that holds the present stage's mask has come -/
  maskCame : T → Bool

variable {T Cl : Type}

/-- Rounds, each with what `Block.oracles` says of it. -/
abbrev Laid : Type := List (Fmt.DeclaredRound × List Oracle)

/-- A part at its rounds. -/
def Part.at (x : Part T) (name : String) (place : Place) (l : Laid) : Block T Cl :=
  { name := name, place := place, planOk := x.planOk, rounds := l.map (·.1)
    oracles := l.map (·.2), before := [], decide := x.decide, claims := [], after := [] }

/-- A block without a round that asks one thing of the record. name: the refusal's words, so it says
what is wrong where the answer is no. -/
def asks (name : String) (place : Place) (ok : T → Bool) : Block T Cl :=
  { name := name, place := place, planOk := true, rounds := [], oracles := [], before := []
    decide := fun t _ _ => (need name (ok t)).map fun _ => t, claims := [], after := [] }

/-- The group's two codes and its tables' k and h are the stage's. -/
def firstFits (s : Stage) (g : Code × Code × Nat × Nat) : Bool :=
  g.1 == s.C && g.2.1 == s.Z && g.2.2.1 == s.k && g.2.2.2 == s.h

/-- The test's name at a place: so that a refusal says which of a file's tests it is. -/
def nameAt (place : Place) : String :=
  s!"the proximity test (chain {place.chain}, piece {place.piece})"

/-- The rounds of a test: 1, then k + 3 for each stage but the last, then 2. -/
def roundsIn (stages : List Stage) : Nat := 1 + (stages.dropLast.map (·.k + 3)).sum + 2

/-- The stages from number j on: cur, then the stages behind it; l: the rounds still to be dealt. -/
def stagesFrom (X : Parts T) (p : P12) : Nat → Stage → List Stage → Laid → Block T Cl
  | j, cur, [], l => (X.base p j cur (l.map (·.1))).at "the base case" p.place l
  | j, cur, next :: rest, l =>
    let lf := l.take (1 + cur.k)
    let ls := (l.drop (1 + cur.k)).take 2
    (((((X.fold p j cur (lf.map (·.1))).at "the fold" p.place lf).andThen "a stage"
      ((X.switch p j cur next rest.isEmpty (ls.map (·.1))).at "the switch" p.place ls)).andThen
      "a stage" ((X.batBehind p (j + 1) next (ls.map (·.1))).at "the batching behind the switch"
        p.place [])).andThen
      "a stage"
      (asks "the next mask has not come" p.place fun t => !p.early || X.maskCame t)).andThen
      "the stages" (stagesFrom X p (j + 1) next rest (l.drop (cur.k + 3)))

/-- **The proximity test.** Where there is no stage, or the numbers give no rounds: a block whose
test on the plan fails. -/
def proximityTestKind (X : Parts T) : Kind P12 T Cl := fun p =>
  match p.nums.stages, H2U.roundsOfNums p.nums, H2U.testOracles p.nums with
  | first :: rest, some rs, some os =>
    let l : Laid := rs.zip p.oracles
    let b : Block T Cl := ((((X.front p).at "the front" p.place []).andThen "the front"
      ((X.bat p ((l.take 1).map (·.1))).at "the batching" p.place (l.take 1))).andThen
      "the batching"
      (asks "the group is not the first stage's" p.place fun t =>
        (X.group t).any (firstFits first))).andThen "the test"
      (stagesFrom X p 0 first rest (l.drop 1))
    { b with
      name := nameAt p.place, place := p.place, before := p.before
      planOk := sizesOk p.nums.stages p.answers && rs.length == roundsIn p.nums.stages &&
        p.oracles.length == rs.length &&
        p.oracles.map (·.map fun o => (o.logLength, o.words)) == os && b.planOk }
  | _, _, _ => { asks (nameAt p.place) p.place (fun _ => false) with planOk := false }

end VerifiableInference.Desc.K12
