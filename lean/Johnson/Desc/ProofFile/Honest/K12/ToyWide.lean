-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyWide.lean: tests (`#guard`) at one small made-up example of a
proximity test. Two things are evaluated. The hypotheses of the theorems on the first stage
(`hy_atFirst_rows`, Johnson/Desc/K12/Honest/FirstRows.lean; `first_V`,
Johnson/Desc/K12/Honest/FirstValues.lean), written as functions to Bool, are true together, but for
one hypothesis that is not evaluated (see the limits). And the test's own block accepts what
`testAll` (Test.lean) shows. In the example the first stage has h = 1, and the group has three
members in three trees, one of them over the base field; with the first fold's own tree there are
four trees. Definitions and evaluations; no theorem. Made-up numbers only. The example's own
definitions are in ToyWideJob.lean.

  `lay`          how the members' rows are read from the first stage's state (`At.lay`, ToyAt.lean)
  `four`         the example's values (`At`, ToyAt.lean). n selects the list of challenges. w is the
                 prover's input; the state on entry is computed at the input 0. upZ: see `lay`. da
                 is added to the first answer in the state on entry (`stateAt`, ToyWideJob.lean)

How it is built: as ToyTrees.lean is. `madeAt` and `stateAt` (ToyWideJob.lean) compute a state on
entry to the test by calling the description's own functions, at tables written out by hand and at
the answers and the target that these tables give.

The group: member 0 has three main rows over the base field, in a tree of depth 5. Member 1 has two
main rows over the extension field and one mask row, in a second tree of depth 5. Member 2 has one
mask row alone, in a tree of depth 4. The first fold sends its own fresh table of two rows, in a
tree of depth 4. The stage's main table has eight rows: member 0's from row 0 on, member 1's from
row 4 on; rows 3, 6 and 7 are no member's. Its mask table has two rows: member 1's and member 2's.
Three stages, with (k, h) = (3, 1), (1, 1), (0, 0).

What is checked: what ToyTrees.lean checks at its example, with the corresponding negative tests,
among them a changed word in the columns of each of the four trees; and `csFitB` and `oldOkB` by
themselves. The claim, `firstB`, `valuesB`, `endB` and the block's acceptance are evaluated at two
lists of challenges; the trees' depths, `stateB`, `csFitB`, `oldOkB` and every negative test at the
first list alone. All negative tests but one, those on the trees' columns among them, evaluate the
functions to Bool (`firstB`, `stateB`, `valuesB`, `endB` and single clauses of them, through
ToyAt.lean), not the block. The block's decision is tested for a rejection once: with the prover's
tables at another input than the claim's.

Limits. `#guard` runs compiled code outside Lean's kernel and leaves no theorem. One example.
`testAll` is evaluated whole; it is not played part by part, with random values given out by a book
(`play`, `ProverCoinCounts`, Johnson/Desc/ProofFile/Honest/Frame.lean). "The block accepts" means the check of
the rounds' form (`roundsFit`) and the block's decision (`At.accepts`, ToyAt.lean): the third check
of a block's step (`Block.step`, Johnson/Desc/Block.lean), on the columns' keys, positions and
widths, is not evaluated. That the block accepts is a test at one example, no word on completeness.
`valuesB` gives all the hypotheses of `first_V` but one (`first_V_test`,
Johnson/Desc/K12/Honest/FirstValuesTest.lean): that the state's fresh table is the packing of the
hiding polynomial is not evaluated; the state here is `TestJob.first` (Test.lean), whose definition
sets that table to `packedN` of `hideAt`. The example is not a proximity test of the key file.
Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyAt
import Johnson.Desc.ProofFile.Honest.K12.ToyWideJob

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyWide
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS wordsOf wr mainSym maskSym)
open H2K.Pub (sgOf)

/-- How the members' rows are read from the first stage's state. upZ: entry 0 of member 2's mask row
is made one larger. -/
def lay (upZ : Bool) (P : PS) : PlainRows where
  M := fun j i e =>
    if j = 0 then P.tabM (i + 8 * e) else if j = 1 then P.tabM (4 + i + 8 * e) else 0
  T := fun j i q => if j = 0 then P.tM i q else if j = 1 then P.tM (4 + i) q else 0
  Z := fun j i e =>
    (if j = 1 then P.tabZ (i + 2 * e) else if j = 2 then P.tabZ (1 + i + 2 * e) else 0) +
      (if upZ ∧ j = 2 ∧ i = 0 ∧ e = 0 then 1 else 0)
  ZT := fun j i q => if j = 1 then P.tZ i q else if j = 2 then P.tZ (1 + i) q else 0
  F := P.fM
  FT := P.fT

/-- The example's values. Nothing precedes the test, and the example stands where no column is
handed: `Seen.bare []`. -/
def four (n : ℕ) (w : ℕ := 0) (upZ : Bool := false) (da : E := zeroE) : At :=
  ⟨J da, ⟨[], (), Seen.bare []⟩, coins, genOf declared n, lay upZ, w⟩

/-! ## 4 What is checked (sections 1 to 3 are in ToyWideJob.lean) -/

-- `madeAt` returns no error at answers and target 0; the sending's and the test's `planOk` are true
#guard word (madeAt (fun _ => zeroE) fun _ => zeroE) == "ok"
#guard (K1.sendOwn (Cl := Unit) send).planOk && (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk
-- four trees, of the depths that the group's data states (`At.depths`)
#guard (four 0).places.length == 4 && (four 0).depths
-- the claim in the state after the batching is true at the written tables
#guard (four 0).claim && (four 1).claim
-- `firstB`, `stateB`, `valuesB`, and the conclusion of `first_V` (`endB`)
#guard (four 0).test none false false && (four 1).test none false false
#guard (four 0).state false false
#guard (four 0).values none false false && (four 1).values none false false
#guard (four 0).ends && (four 1).ends
-- the test's block accepts what `testAll` shows
#guard (four 0).accepts && (four 1).accepts
-- negative tests: word 0 of every column of one tree made one larger, for each of the four trees
#guard !(four 0).test (some 0) false false && !(four 0).test (some 1) false false
#guard !(four 0).test (some 2) false false && !(four 0).test (some 3) false false
-- an entry made one larger: in member 0's row (base field); the fresh table; member 2's mask row
#guard !(four 0).test none true false && !(four 0).test none false true
#guard !(four 0 0 true).test none false false && !(four 0 0 true).state false false
-- the prover's tables at another input than the claim's
#guard (four 0 1).test none false false && (four 0 1).state false false
#guard !(four 0 1).claim && !(four 0 1).values none false false && !(four 0 1).ends
#guard !(four 0 1).accepts
-- an entry of a main row that is no member's (rows 3, 6, 7) made one larger in the state
#guard !(four 0).stateUp 3 && !(four 0).stateUp 6 && !(four 0).stateUp 7
-- a false answer to a sample in the state on entry
#guard !(four 0 0 false oneE).claim && !(four 0 0 false oneE).values none false false
-- `csFitB` at the first two stages; `oldOkB`, and that it is false at a code's number one larger
#guard (four 0).fits && (four 0).old 0 && !(four 0).old 1

end ProofFile.Honest.K12.ToyWide

#print axioms ProofFile.Honest.K12.ToyWide.lay
#print axioms ProofFile.Honest.K12.ToyWide.four
