-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/TestEntries.lean: the declared rounds of one proximity test, made from numbers of
its place. Definitions only, all computable; nothing is proved here. It imports Fmt/ and Decl/
alone.

Why. A description's test on the plan holds the rounds that its blocks declare against the plan's
own (Johnson/Desc/Block.lean, `FileDescription.planOk`). That test can fail only if a block's rounds are
not themselves taken from the plan. So no entry and no declared round of a plan goes in here: only
numbers of the place, with one exception: `first`, the trees that the first round of positions
opens, is a list of shapes with their sources. Whoever fills it for a proof file (`firstsOfPlan`,
Johnson/Desc/K12/Plan/NumsOfPlan.lean) makes it by `frameOpens`, `sharedOpens` and `secondOpens`
(Johnson/G/RoundsOfPlan.lean), by which the plan's own declared rounds are filled: at that round's
openings the test holds the rule against itself.

How made.
  No new rule and no new maker of a round. The rounds behind "BAT" are
    `Fmt.M1.laterRounds` (Fmt/M1Plan.lean: the first toy's own plan, over `rEps`, `rTwo`, `rSeed`,
    `rCs`, `rLambda`, `rBase`) at the place's stages (`Fmt.M1.Stage`: the two codes' a, l, r; k; h;
    t) and bits of work. "BAT" is `rBat` with the place's number of batched rows.
  Three things part from the toy, each laid over that list. (1) The first round of positions opens
    the trees that are handed in, not one tree. (2) Where the first fold sends its own mask, its
    round has a root more (32 bytes in front; one root), and that tree is opened at the first round
    of positions too. (3) An own tree number n has the number firstTree + n in its leaves' hashes.
  The later trees' shapes are the toy's: depth the new stage's C.a; width `wMid`, at the last stage
    `wLast`. The own mask's: depth the first stage's Z.a; width 3 · 2 ^ h.

Main names.
  `TestNums`: the numbers of a place. `layOpens`: the toy's rounds with the lists of trees laid in.
  `roundsOfNums`: the declared rounds. `testEntries`: their entries. `testOracles`: for each round,
  for each root that it sends: the log-length and the words of a symbol.
  Nothing (an Option): fewer than two stages; a round of positions that would open nothing.

Limits. One answer to a sample, one slot a main row, masks that ride, a mask at every stage: as the
toy has them. Where a plan parts from that, these rounds part from the plan's, and the test against
the plan says so. The namespace is H2U, under which the files that stand on this one name it.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Fmt.M1Plan
import Decl.Declared

set_option autoImplicit false

namespace H2U

/-- The numbers of a proximity test's place. -/
structure TestNums where
  /-- the rows that "BAT" batches -/
  rows : Nat
  /-- the bits of work at a round of positions -/
  work : Nat
  /-- the stages: the two codes' a, l, r; k; h; the positions t -/
  stages : List Fmt.M1.Stage
  /-- the first fold sends its own mask -/
  ownMask : Bool
  /-- the trees of the test's group, and of a mask that came earlier -/
  first : List (Fmt.Shape × Fmt.TreeSource)
  /-- the first free own number: the roots that the chain has received in front of "BAT" -/
  free : Nat
  /-- the number in the leaves' hashes of the chain's own tree number 0 -/
  firstTree : Nat

/-- The own tree number n. -/
def TestNums.own (N : TestNums) (a W n : Nat) : Fmt.Shape × Fmt.TreeSource :=
  (⟨a, W, false, N.firstTree + n⟩, .own n)

/-- The trees that the test sends, in order: depth and width. -/
def TestNums.sent (N : TestNums) : List (Nat × Nat) :=
  (match N.ownMask, N.stages with
    | true, s :: _ => [(s.Z.a, 3 * 2 ^ s.h)]
    | _, _ => []) ++
  (N.stages.drop 1).zipIdx.map fun s =>
    (s.1.C.a, if s.2 + 2 == N.stages.length then Fmt.M1.wLast s.1 else Fmt.M1.wMid s.1)

/-- The toy's rounds as declared rounds, with the lists of trees at the rounds that open a tree, in
order. own: the first "FOLD epsilon" has a root more. seen: a "FOLD epsilon" has gone by. Nothing
unless the lists are as many as these rounds, and none is empty. -/
def layOpens (own : Bool) : Bool → List Fmt.Round → List (List (Fmt.Shape × Fmt.TreeSource)) →
    Option (List Fmt.DeclaredRound)
  | _, [], [] => some []
  | _, [], _ :: _ => none
  | seen, r :: rs, l =>
    let eps := r.entry.name == "FOLD epsilon"
    let e := if own && !seen && eps then { r.entry with msg := 32 + r.entry.msg, roots := 1 }
      else r.entry
    if r.opens.isEmpty then (layOpens own (seen || eps) rs l).map (⟨e, [], []⟩ :: ·)
    else
      match l with
      | x :: t =>
        if x.isEmpty then none else (layOpens own (seen || eps) rs t).map (⟨e, [], x⟩ :: ·)
      | [] => none

/-- **The declared rounds of a proximity test, from the numbers of its place.** -/
def roundsOfNums (N : TestNums) : Option (List Fmt.DeclaredRound) :=
  match N.stages with
  | s :: next :: rest =>
    let told := N.sent.zipIdx.map fun t => N.own t.1.1 t.1.2 (N.free + t.2)
    let mask := if N.ownMask then told.take 1 else []
    let later := if N.ownMask then told.drop 1 else told
    layOpens N.ownMask false
      ({ Fmt.M1.rBat with entry := { Fmt.M1.rBat.entry with rows := N.rows } } ::
        Fmt.M1.laterRounds N.work 0 0 s (next :: rest))
      ((N.first ++ mask) :: later.map ([·]))
  | _ => none

/-- Their entries. -/
def testEntries (N : TestNums) : Option (List Fmt.Entry) := (roundsOfNums N).map (·.map (·.entry))

/-- For each round, for each root that it sends: the log-length, the words of a symbol. -/
def testOracles (N : TestNums) : Option (List (List (Nat × Nat))) :=
  (roundsOfNums N).map fun l =>
    (l.foldl (fun (acc : List (List (Nat × Nat)) × List (Nat × Nat)) r =>
      (acc.2.take r.entry.roots :: acc.1, acc.2.drop r.entry.roots)) ([], N.sent)).1.reverse

end H2U
