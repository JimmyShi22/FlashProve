-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyGroup.lean: tests (`#guard`) at two small made-up examples of a
proximity test, below: the two toys. The hypotheses of the two theorems on the test's first stage
(`hy_atFirst_rows`, Johnson/Desc/K12/Honest/FirstRows.lean; `first_V`,
Johnson/Desc/K12/Honest/FirstValues.lean), written as functions to Bool, are true together at each
toy, but for one hypothesis: an equation that is a theorem and is not evaluated (see "What is
checked"). `hy_atFirst_test` (Johnson/Desc/K12/Honest/FirstTest.lean) and `first_V_test`
(Johnson/Desc/K12/Honest/FirstValuesTest.lean) derive the two theorems' conclusions from the value
true of these functions, the second with that equation as a further hypothesis. Here the functions
are evaluated, through the definitions of Johnson/Desc/ProofFile/Honest/K12/ToyAt.lean, at the
values of Johnson/Desc/ProofFile/Honest/K12/Toy.lean (one tree; the fresh table came earlier) and of
Johnson/Desc/ProofFile/Honest/K12/ToyOwn.lean (two trees; the first fold sends its own table).
Computable definitions and evaluations; no theorem. Made-up numbers only.

Terms. A place (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a proximity test, among
them its stages (`Fmt.M1.Stage`, Fmt/M1Types.lean). Each toy has a place of its own; "both places"
in the limits means these two. A job (`TestJob`, Johnson/Desc/ProofFile/Honest/K12/Test.lean) is
what a caller supplies for its test; the group's members are the oracle messages that it lists,
numbered from 0. The front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is what precedes the
test. The plain rows (`PlainRows`, FirstRows.lean) are the members' rows, the fresh table's rows and
all their tails, as functions of numbers. The book is the book of trees (`TreeBook`,
OnBytes/Iop/Ground.lean) in the group's data (`At.plain`, ToyAt.lean). The claim is the one that the
state after the batching passes on (`At.claim`, ToyAt.lean). The range is the positions below
2 ^ `a.C.a`, where a is the first stage. The two lists of challenges are `list₁` and `list₂` of
Toy.lean.

  `one ds w`, `own ds w`: the two toys' values (`At`, ToyAt.lean) at the list of challenges ds and
    the prover's input w, which is 0 unless it is given. `one` has the job and the front of Toy.lean
    and, put for the coins (`TestCoins`, Test.lean), the values of that file's written lists
    `senderList` and `restList`. `own` has the job and the front of ToyOwn.lean and, put for the
    coins, the values of that file's `senderList` and `ownList` and of `restList`. The state on
    entry to the test is computed at the input 0 (`At.t`, ToyAt.lean), so at another w the claim is
    on other tables than the prover's
  `lay`: how the members' rows are read from the first stage's state (`At.lay`, ToyAt.lean)
  `far ds`, `flat ds`: the list ds with one challenge changed, for two negative tests: a sampled
    position of the first switch set to 1000; the factor of the first switch's seed set to 0

What is checked.
- At both toys and both lists of challenges: `firstB` and `valuesB` are true; `stateB` is a clause
  of `valuesB`. Their value true gives all hypotheses of `hy_atFirst_rows` and of `first_V` but the
  equation on the packing (hpk in `first_V`: the state's fresh table is `packedN` at `K.W`), which
  is `first_packs` (Johnson/Desc/ProofFile/Honest/K12/FreshCols.lean). The conclusion of `first_V`
  (`endB`), evaluated by itself at the list of trees that the theorem's statement has, is true.
- At both toys, at the first list only: `stateB` by itself, the claim and `oldOkB` are true. The
  job's trees are as many and as deep as the book states: one tree at `one`, two at `own`.
- At `one`, at the first list only: `csFitB` is true at the first two stages.
- Negative tests of `firstB`, each with one thing changed, at both toys, at the first list only:
  entry 0 of row 0 of member 0, or of the fresh table, one larger in the plain rows · word 0 of a
  tree's column one larger, at all positions, for each tree · by `far`, a sampled position out of
  the range · by `flat`, the seed's factor 0 (there the verifier's own switch rejects). What
  `hy_atFirst_test` concludes of the switch (`Did`, Johnson/Desc/K12/Law/SwDid.lean) has the field
  `factor`: the seed's factor is not 0. That the clause of `firstB` that is false at `flat` is the
  switch's `decide` is by reading: no guard evaluates that clause by itself.
- Negative tests of what `valuesB` adds, each with one thing changed, at the first list only. The
  prover's tables at another input than the claim's (w = 1), at both toys: `firstB` and `stateB`
  stay true, the clause on the claim is false, `valuesB` is false, and `endB` is false. `stateB`
  with an entry one larger in the plain rows only: member 0's at `one`, the fresh table's at `own`.
  `stateB` with an entry one larger in the state only: of member 0's row 0 at `one`; of a row that
  no member has, so that it is other than 0: row 3 at `one`, row 7 at `own`. `csFitB` at the first
  stage paired with itself, at `one`. `oldOkB` with the number of the second stage's main code one
  larger, at both toys.

Limits.
- A `#guard` is an evaluation by Lean's evaluator, outside the kernel: it leaves no theorem.
- At both places both members stand in one tree (the second toy's second tree holds the fresh table
  alone), and the first stage has h = 0: one fresh row; the mask table is all 0.
- Not met at these two: members in two trees · a member's mask rows · rows over the base field · a
  tree shorter than the range · a fresh table of two rows or more. All five are met in
  Johnson/Desc/ProofFile/Honest/K12/ToyWide.lean.
- Two lists of challenges and one set of values for the coins. Every negative test is at the first
  list only.
- No negative test is next to the guards on the number of trees (`At.places`) and on `At.depths`.
- The state on entry is what the job's own function gives at the input 0 (read by `TestJob.recB`,
  Test.lean); nothing here compares it with a verifier's state. `firstB` has clauses that say that a
  `decide` returns no error (`firstYesB`, FirstTest.lean): their value true at an example is no
  statement of completeness.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyOwn
import Johnson.Desc.ProofFile.Honest.K12.ToyAt

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyGroup
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS)
open ProofFile.Honest.K12.Toy (csOf restList list₁ list₂)

/-- How the members' rows are read from the first stage's state, at both toys.
Member j has the rows 4 j, 4 j + 1, 4 j + 2 of a table of eight; no mask row. -/
def lay (P : PS) : PlainRows where
  M := fun j i e => P.tabM (4 * j + i + 8 * e)
  T := fun j i q => P.tM (4 * j + i) q
  Z := fun _ _ _ => 0
  ZT := fun _ _ _ => 0
  F := P.fM
  FT := P.fT

/-- The toy whose fresh table came earlier: the job and the front of Toy.lean, with the same values
put for the coins as in `Toy.whole`. ds: the list of challenges. w: the prover's input. -/
def one (ds : List Fmt.Drawn) (w : ℕ := 0) : At :=
  let S := stretchOf (csOf 23 Toy.senderList none)
  ⟨Toy.J, Toy.fr,
    ⟨fun i => S.e (14 + i), fun _ q => S.e (21 + q),
      fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩, (stretchOf (csOf 125 restList none)).e⟩, ds,
    lay, w⟩

/-- The toy whose first fold sends its own table: the job and the front of ToyOwn.lean, with the
values of `ToyOwn.senderList`, `ToyOwn.ownList` and `restList` put for the coins. ds and w: as in
`one`. -/
def own (ds : List Fmt.Drawn) (w : ℕ := 0) : At :=
  let S := stretchOf (csOf 14 ToyOwn.senderList none)
  let O := stretchOf (csOf 9 ToyOwn.ownList none)
  ⟨ToyOwn.J, ToyOwn.fr,
    ⟨fun i => O.e i, fun _ q => O.e (7 + q),
      fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩, (stretchOf (csOf 125 restList none)).e⟩, ds,
    lay, w⟩

/-- Position number 0 of round 6, the first switch's round of positions, set to 1000: out of the
range. -/
def far (ds : List Fmt.Drawn) : List Fmt.Drawn :=
  ds.modify 6 fun d => { d with poss := d.poss.modify 0 fun _ => 1000 }

/-- The last element sampled in round 5, the round of the first switch's seed, set to 0. That
element is the seed's factor. -/
def flat (ds : List Fmt.Drawn) : List Fmt.Drawn :=
  ds.modify 5 fun d => { d with elems := d.elems.dropLast ++ [(0, 0, 0)] }

-- the group's data lists one tree at `one` and two at `own`; the job's trees are as many, and as
-- deep, as the book states (`At.depths`)
#guard (one list₁).places.length == 1 && (own list₁).places.length == 2
#guard (one list₁).depths && (own list₁).depths
-- `firstB` is true, at both toys and both lists
#guard (one list₁).test none false false && (one list₂).test none false false
#guard (own list₁).test none false false && (own list₂).test none false false
-- `stateB` by itself: the state holds the plain rows at the layout's blocks, and 0 elsewhere
#guard (one list₁).state false false && (own list₁).state false false
-- `valuesB` is true, at both toys and both lists
#guard (one list₁).values none false false && (one list₂).values none false false
#guard (own list₁).values none false false && (own list₂).values none false false
-- and so is the conclusion of `first_V` (`endB`), evaluated by itself
#guard (one list₁).ends && (one list₂).ends && (own list₁).ends && (own list₂).ends
-- negative tests of `firstB`: an entry of a member's row one larger in the plain rows; of the fresh
-- table
#guard !(one list₁).test none true false && !(own list₁).test none true false
#guard !(one list₁).test none false true && !(own list₁).test none false true
-- word 0 of a tree's column one larger, at all positions, for each tree
#guard !(one list₁).test (some 0) false false
#guard !(own list₁).test (some 0) false false && !(own list₁).test (some 1) false false
-- a sampled position out of the range (`far`); the seed's factor 0 (`flat`)
#guard !(one (far list₁)).test none false false && !(own (far list₁)).test none false false
#guard !(one (flat list₁)).test none false false && !(own (flat list₁)).test none false false
-- negative tests of what `valuesB` adds. The prover's tables at another input than the claim's:
-- `firstB` and `stateB` stay true; the claim, `valuesB` and `endB` are false; at the input 0 the
-- claim is true
#guard (one list₁ 1).test none false false && (one list₁ 1).state false false
#guard !(one list₁ 1).claim && !(one list₁ 1).values none false false && !(one list₁ 1).ends
#guard (own list₁ 1).test none false false && (own list₁ 1).state false false
#guard !(own list₁ 1).claim && !(own list₁ 1).values none false false && !(own list₁ 1).ends
#guard (one list₁).claim && (own list₁).claim
-- `stateB`: an entry one larger in the plain rows only (a member's; the fresh table's); in the
-- state only: a member's entry; an entry of a row that no member has (rows 3 and 7)
#guard !(one list₁).state true false && !(own list₁).state false true
#guard !(one list₁).stateUp 0 && !(one list₁).stateUp 3 && !(own list₁).stateUp 7
-- the first two stages fit (`csFitB`); the first paired with itself does not
#guard (one list₁).fits && !csFitB (H2K.Pub.sgOf (one list₁).a) (H2K.Pub.sgOf (one list₁).a)
-- `oldOkB` is true; it is false at a code's number one larger
#guard (one list₁).old 0 && (own list₁).old 0 && !(one list₁).old 1 && !(own list₁).old 1

end ProofFile.Honest.K12.ToyGroup

#print axioms ProofFile.Honest.K12.ToyGroup.lay
#print axioms ProofFile.Honest.K12.ToyGroup.one
#print axioms ProofFile.Honest.K12.ToyGroup.own
#print axioms ProofFile.Honest.K12.ToyGroup.far
#print axioms ProofFile.Honest.K12.ToyGroup.flat
