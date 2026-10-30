-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyAt.lean: a tool for tests at small made-up examples of a
proximity test. The hypotheses of two theorems on the test's first stage (`hy_atFirst_rows`,
Johnson/Desc/K12/Honest/FirstRows.lean; `first_V`, Johnson/Desc/K12/Honest/FirstValues.lean), and
the conclusion of the second, are written as functions to Bool in
Johnson/Desc/K12/Honest/FirstTest.lean (`firstB`), FirstStateTest.lean (`stateB`) and
FirstValuesTest.lean (`valuesB`, `endB`), but for one hypothesis (see the limits). This file defines
a structure, `At`, that holds one example's values: a job, what precedes the test, values for the
coins, and a list of challenges. It applies the functions to these values, whole and clause by
clause, with arguments that each change one value, for negative tests. Definitions only, none marked
`noncomputable`: no theorem, no evaluation. The evaluations are in the files that import this one,
ToyGroup.lean and ToyTrees.lean in this folder among them.

Terms. A place (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a proximity test, among
them its stages (`Fmt.M1.Stage`, Fmt/M1Types.lean). A job (`TestJob`, Test.lean in this folder) is
what a caller supplies for its test: the place, who sent the group's oracle messages (the group's
members, numbered from 0) and the first fold's fresh table, and functions that give the state on
entry to the test (`rec₀`), the first stage's rows and the trees. The front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean) is what precedes the test. The term is `testAll`
(Test.lean). The test's own block is `proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/Frame.lean, JoinGuarded.lean).
The format's test is `roundsFit` (Johnson/Desc/Block.lean). The plain rows (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean) are the members' rows, the fresh table's rows and all their
tails, as functions of numbers. The book is the book of trees (`TreeBook`,
OnBytes/Iop/Ground.lean) in the field `book` of the group's data (`At.plain`).

  `At`: a structure: one example's values. `J`: the job; the prover's input is a natural number.
    `fr`: the front. `C`: the values put for the coins that the term reads (`TestCoins`, Test.lean).
    `ds`: the sampled challenges, by the round's number in the test. `lay`: how the prover's rows
    are read from the first stage's state. `w`: the prover's input, 0 unless it is given; the state
    on entry is computed at the input 0, so at another `w` the claim is on other tables than the
    prover's
  `At.test`, `At.state`, `At.values`, `At.ends`: `firstB`, `stateB`, `valuesB`, `endB` at these
    values. `endB` is applied to the list of trees that the statement of `first_V_test`
    (FirstValuesTest.lean) has (`groupTrees`, Johnson/Desc/K12/Honest/GroupState.lean, at
    `At.cols none`), not to `At.trees`
  `At.claim`, `At.fits`, `At.old`, `At.stateUp`: single clauses of `valuesB`. `claim`: the claim
    that the state after the batching passes on is true at the two tables of the first stage's
    state. `fits`: the first two stages fit (`csFitB`). `old dn`: `oldOkB`, with dn added to the
    number of the second stage's main code. `stateUp n`: `stateB` with entry n of the state's main
    table one larger
  `At.accepts`: the test's own block accepts all that the term shows, and the rounds pass the
    format's test
  `At.plain`: the group's data (`Plain`, computed by `gpOf`, Johnson/Desc/K12/Law/FirstOk.lean)
    from the state after the batching; `none` where that state passes on no claim, or `gpOf` gives
    `none`
  `At.places`: the indices, in the book, of the trees that the group's data lists (`Plain.ts`)
  `At.cols`: the trees' column functions by a tree's index in the book: tree number i of the job's
    own list of trees is put at entry number i of `At.places`
  `At.depths`: the job's trees are as many, and as deep, as the book states at these indices
  `At.rows`: the plain rows: `lay` at the first stage's state
  `At.D`, `At.stages`, `At.a`, `At.next`, `At.K`, `At.t`, `At.P`, `At.trees`: the values that the
    definitions above use: the challenges by the round's number; the place's stages, the first and
    the second; `coinsOf` (Coins.lean in this folder) at `C.hide` and `C.rest`; the state after the
    batching (`TestJob.recB`) at the input 0; the first stage's state (`TestJob.first`) and the
    job's list of trees (`trees₀`), both at the input `w`

Limits. Nothing is checked here: no definition is evaluated at a value. The state on entry is the
job's `rec₀` at the input 0. Nothing here compares it with a verifier's state. In `At.accepts`,
"accepts" means that `Block.decide`, started from that state and given the term's rounds and opened
columns, returns no error. The term there is at the input `w`, and computes its own state after the
batching from `rec₀` at `w`; `At.no`, `At.yes` and `At.acc` (ToyAll.lean) take `rec₀` at `w` too.
`rec₀` at 0 and `rec₀` at `w` are one state where the job's `rec₀` does not read its input; `At`
does not ask that. At a job whose `rec₀` reads it, another `w` can change the claim in these three
together with the prover's tables. `Block.step` (Johnson/Desc/Block.lean) is not called. A "true" at
an example is no statement of completeness. `first_V_test` has one hypothesis besides
`valuesB ... = true`, an equation of two functions on the state's fresh table. No definition here
tests it. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Test
import Johnson.Desc.K12.Honest.FirstValuesTest

set_option autoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS BCoins μOf)
open H2K.First (gpOf Plain logAt)
open H2K.Pub (sgOf)
open H2K.JointK (laidS)

/-- The values of one small made-up example: the job, the front, the values put for the coins, the
challenges by the round's number, how the prover's rows are read from the first stage's state, and
the prover's input. -/
structure At where
  J : TestJob ℕ Unit
  fr : Front Unit
  C : TestCoins
  ds : List Fmt.Drawn
  lay : PS → PlainRows
  w : ℕ := 0

namespace At
variable (A : At)

/-- What round number r of the test sampled; nothing where the list has no entry number r. -/
def D (r : ℕ) : Fmt.Drawn := A.ds.getD r ⟨[], [], [], none⟩
/-- The place's stages. -/
def stages : List Fmt.M1.Stage := A.J.p.nums.stages
/-- The first stage; `default` where there is none. -/
def a : Fmt.M1.Stage := A.stages.headD default
/-- The second stage; `default` where there is none. -/
def next : Fmt.M1.Stage := A.stages.getD 1 default
/-- `coinsOf` (Coins.lean) at the place's stages, `C.hide` and `C.rest`. -/
def K : BCoins := coinsOf A.stages A.C.hide A.C.rest
/-- The state after the batching (`TestJob.recB`, Test.lean), at the input 0. -/
def t : T12 := A.J.recB 0 A.fr (A.D 0)
/-- The first stage's state (`TestJob.first`, Test.lean), at the input `w`. -/
def P : PS := A.J.first A.w A.fr A.C
/-- The job's list of trees (`trees₀`), at the input `w`. -/
def trees : List Tree := A.J.trees₀ A.w A.fr A.C.mem A.P

/-- The group's data (`Plain`), computed by `gpOf` (Johnson/Desc/K12/Law/FirstOk.lean) from the
state after the batching; `none` where that state passes on no claim, or `gpOf` gives `none`. -/
def plain : Option Plain :=
  match A.t.pass with
  | .claim _ L => gpOf A.J.p A.t A.a L
  | _ => none

/-- The indices, in the book, of the trees that `plain` lists; no index where it is `none`. -/
def places : List ℕ := (A.plain.map (·.ts)).getD []

/-- The column at position x of the tree whose index in the book is u: that of the job's tree at the
number that u has in `places` (`List.idxOf`); the empty column where the list has no such tree.
up: one more on word 0 of every column of the tree at that number in the list. -/
def cols (up : Option ℕ) (u x : ℕ) : List UInt64 :=
  let i := A.places.idxOf u
  let c := (A.trees.getD i (0, fun _ => [])).2 x
  if up = some i then c.modify 0 (· + 1) else c

/-- The job's trees are as many, and as deep, as the book states at `places`. -/
def depths : Bool :=
  match A.plain with
  | some Dp => A.trees.map (·.1) == Dp.ts.map (logAt Dp.book)
  | none => false

/-- The plain rows: `lay` at the first stage's state.
upM, upF: one more on entry 0 of row 0 of member 0; of the fresh table. -/
def rows (upM upF : Bool) : PlainRows :=
  let R := A.lay A.P
  { R with
    M := fun j i e => R.M j i e + (if upM ∧ j = 0 ∧ i = 0 ∧ e = 0 then 1 else 0)
    F := fun b e => R.F b e + (if upF ∧ b = 0 ∧ e = 0 then 1 else 0) }

/-- `stateB` at these values; false where `plain` is `none`. upM, upF: see `rows`. -/
def state (upM upF : Bool) : Bool :=
  match A.plain with
  | some Dp => stateB A.a Dp A.P (A.rows upM upF)
  | none => false

/-- `stateB` with entry n of the state's main table one larger; the plain rows as they were. -/
def stateUp (n : ℕ) : Bool :=
  match A.plain with
  | some Dp =>
    stateB A.a Dp { A.P with tabM := fun i => A.P.tabM i + (if i = n then 1 else 0) }
      (A.rows false false)
  | none => false

/-- `firstB` at these values. up: see `cols`. upM, upF: see `rows`. -/
def test (up : Option ℕ) (upM upF : Bool) : Bool :=
  firstB A.J.p A.K (A.stages.drop 2) A.a A.next 1 A.t A.P A.D (A.cols up) (A.rows upM upF)

/-- `valuesB` at these values. up: see `cols`. upM, upF: see `rows`. -/
def values (up : Option ℕ) (upM upF : Bool) : Bool :=
  valuesB A.J.p A.K (A.stages.drop 2) A.a A.next 1 A.t A.P A.D (A.cols up) (A.rows upM upF)

/-- `endB` at these values and at `groupTrees` of `cols none`; false where `plain` is `none`. -/
def ends : Bool :=
  match A.plain with
  | some Dp =>
    endB A.J.p A.K (A.stages.drop 2) A.a A.next 1 A.t A.P A.D
      (groupTrees Dp.ts (logAt Dp.book) (A.cols none))
  | none => false

/-- The claim that `t` passes on is true at the two tables of `P`; false where it passes on none. -/
def claim : Bool :=
  match A.t.pass with
  | .claim row L => holdsB (sgOf A.a) (stmGk (sgOf A.a) L.k L.h row) (μOf (sgOf A.a) A.P)
  | _ => false

/-- The first two stages fit (`csFitB`). -/
def fits : Bool := csFitB (sgOf A.a) (sgOf A.next)

/-- `oldOkB` at the state after the first fold. dn: added to the second stage's main code number. -/
def old (dn : ℕ) : Bool :=
  match stageAt A.J.p 1 A.next, (t1At A.J.p A.K 0 A.a (laidS A.J.p) 1 A.t A.P A.D).pass with
  | some nx, .single rows _ =>
    oldOkB (sgOf A.a) (sgOf A.next) (t1At A.J.p A.K 0 A.a (laidS A.J.p) 1 A.t A.P A.D).st.codes
      rows (nx.code + dn) nx.maskCode
  | _, _ => false

/-- `roundsFit` is true, and `Block.decide` returns no error, at the term's rounds and columns. -/
def accepts : Bool :=
  let B := testAll A.J A.w A.fr A.C A.D
  roundsFit (proximityTestKind guardedProximityTestParts A.J.p : Block T12 Unit).rounds B.rs &&
    Except.isOk ((proximityTestKind guardedProximityTestParts A.J.p : Block T12 Unit).decide (A.J.rec₀ 0 A.fr)
      (B.rs.map noDigest) B.gs)

end At

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.At
#print axioms ProofFile.Honest.K12.At.D
#print axioms ProofFile.Honest.K12.At.stages
#print axioms ProofFile.Honest.K12.At.a
#print axioms ProofFile.Honest.K12.At.next
#print axioms ProofFile.Honest.K12.At.K
#print axioms ProofFile.Honest.K12.At.t
#print axioms ProofFile.Honest.K12.At.P
#print axioms ProofFile.Honest.K12.At.trees
#print axioms ProofFile.Honest.K12.At.plain
#print axioms ProofFile.Honest.K12.At.places
#print axioms ProofFile.Honest.K12.At.cols
#print axioms ProofFile.Honest.K12.At.depths
#print axioms ProofFile.Honest.K12.At.rows
#print axioms ProofFile.Honest.K12.At.state
#print axioms ProofFile.Honest.K12.At.stateUp
#print axioms ProofFile.Honest.K12.At.test
#print axioms ProofFile.Honest.K12.At.values
#print axioms ProofFile.Honest.K12.At.ends
#print axioms ProofFile.Honest.K12.At.claim
#print axioms ProofFile.Honest.K12.At.fits
#print axioms ProofFile.Honest.K12.At.old
#print axioms ProofFile.Honest.K12.At.accepts
