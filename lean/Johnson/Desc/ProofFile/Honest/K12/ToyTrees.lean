-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyTrees.lean: tests (`#guard`) at one small made-up example of a
proximity test. Two things are evaluated. The hypotheses of the theorems on the first stage
(`hy_atFirst_rows`, Johnson/Desc/K12/Honest/FirstRows.lean; `first_V`,
Johnson/Desc/K12/Honest/FirstValues.lean), written as functions to Bool, are true together, but for
one hypothesis that is not evaluated (see the limits); and the test's own block accepts the term
there. The example is a place whose group has two members in two trees of different depths; with the
first fold's own tree there are three trees. Definitions, none marked `noncomputable`, and
evaluations; no theorem. Made-up numbers only.

Terms. A place (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a proximity test, among
them its stages (`Fmt.M1.Stage`, Fmt/M1Types.lean: main code, mask code, k, h, number of positions).
A job (`TestJob`, Test.lean in this folder) is what a caller supplies for its test: the place, who
sent the group's oracle messages (the group's members, numbered from 0) and the first fold's fresh
table, and functions that give the state on entry to the test (`rec₀`), the first stage's rows and
the trees. The term is `testAll` (Test.lean). The front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean) is what precedes the test. The test's block is
`proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/Frame.lean, JoinGuarded.lean). The format's test is `roundsFit`
(Johnson/Desc/Block.lean). The plain rows (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean) are
the members' rows, the fresh table's rows and all their tails, as functions of numbers. The book of
trees is the field `book` (`TreeBook`, OnBytes/Iop/Ground.lean) of the group's data (`At.plain`,
ToyAt.lean). A book of coins is a `ProverCoinCounts` (Johnson/Desc/ProofFile/Honest/Frame.lean). The claim is
the one that the state after the batching passes on (`TestJob.recB`, Test.lean; `At.claim`,
ToyAt.lean).

How it is constructed. The place, its numbers and the order of the calls in `madeAt` are those of
the example in Johnson/Desc/K12/Honest/OwnFoldOmega.lean (not in the library yet), namespace
`OmToy`, written again here with true values. There the answers and the target are arbitrary. Here
the two members are tables given by written formulas, and the two answers to the sending's samples
and the open row's target are what these tables give (`valOf`).

The group: member 0 has five main rows over the extension field, in a tree of depth 5; member 1 has
one mask row and no main row, in a tree of its own of depth 4; the first fold sends its own fresh
table, in a tree of depth 4. Three stages, (k 3, h 0), (k 1, h 1), (k 0, h 0).

  `three n w upZ da`: the example's values (`At`, ToyAt.lean): the job `J da`, an empty front,
    `coins`, the challenges `gen n`, `lay upZ`, and the prover's input w. The state on entry is
    computed at the input 0, so at another w the claim is on other tables than the prover's
  `J da`: the job: the place `p`; the two members, both sent by `sender`; no earlier sender of the
    fresh table; the state on entry `stateAt da`; the rows `rowsAt w`; three trees, of depths 5, 4
    and 4
  `mainE`, `mainTlE`, `maskE`, `maskTlE`: the two members' tables and tails
  `valOf`: the value of a row's left side at these tables, at the input 0, by the row's own
    coefficients
  `madeAt`, `sampleOf`, `stateAt`, `tTrue`: a state computed by the description's own functions
    (`K1.decideSend`, Johnson/Desc/K1/Own.lean; `Ground.newGroupP`, `joinP`, `takeMaskP`, `addRowP`,
    Johnson/Desc/First/Base/Ground.lean) at two given answers and a given target; a message's first
    sample row in that state; the state on entry, at the answers and the target that the tables
    give, with da added to the first answer; that state at da = 0, which no test in this file uses
  `openRow`, `pt`: the one open row; the point of its vector of product form
  `rowsAt w`: the first stage's tables and tails (`PS`, Johnson/Prover/Link/BodyState.lean) at the
    input w: member 0's rows are rows 0 to 4 of a main table of eight rows; rows 5 to 7 are 0
  `lay`: how the members' rows are read from the first stage's state (`At.lay`, ToyAt.lean)
  `gen n`: a list of challenges for the place's declared rounds, by a written formula; another list
    for another n
  `coins`: the values put for the coins that `testAll` reads (`TestCoins`, Test.lean), by written
    formulas; 0 for the members' coins, which `J` does not read
  `sender`: the address (`Addr`, Johnson/Desc/ProofFile/Honest/Frame.lean) of the part that sent
    both members
  `codes`, `s0`, `s1`, `s2`: the lists of codes; the three stages
  `ft`: the number of the first tree that the chain sends
  `nMain`, `nMask`: the two members as they are announced (`OracleNotice`, OnBytes/Iop/Ground.lean)
  `send`, `r1`: the parameters of the one sending that sends both (`K1.Par`,
    Johnson/Desc/K1/Send.lean); its first round, with six sampled elements
  `d0`: the state from which `madeAt` starts
  `nums`, `p`, `declared`: the place's numbers (`H2U.TestNums`, Johnson/Desc/K12/TestEntries.lean);
    the place (`H2U.proximityTestParametersAt`, Johnson/Desc/K12/AtPlan.lean); its declared rounds (`H2U.roundsOfNums`)
  `tri`: an element of the extension field from three numbers

What is checked. `madeAt` returns no error at answers and target 0, and the block's test on the plan
(`planOk`) is true. The job's three trees have the depths that the book of trees states
(`At.depths`, ToyAt.lean). The claim is true at the written tables. `firstB`
(Johnson/Desc/K12/Honest/FirstTest.lean), `stateB` (FirstStateTest.lean) and `valuesB`
(FirstValuesTest.lean) are true. The conclusion of `first_V`, evaluated by itself (`endB`,
FirstValuesTest.lean), is true. The test's block accepts all that the term shows, and the rounds
pass the format's test. That last check is `At.accepts` (ToyAt.lean). The claim, `firstB`,
`valuesB`, `endB` and `At.accepts` are evaluated at two lists of challenges (`three 0`, `three 1`);
the trees' depths, `stateB` and every negative test at the first list only.

Negative tests, each with one thing changed:
- a word of each of the three trees' columns (word 0 of every column of one tree is made one
  larger): `firstB` is false.
- an entry of member 0's row, or of the fresh table, in the plain rows. `firstB` is false at each.
- the mask row's entry in the plain rows. `firstB` and `stateB` are false.
- the prover's tables at another input than the claim's (w = 1): `firstB` and `stateB` stay true;
  the claim, `valuesB` and `endB` are false; and `At.accepts` is false.
- an entry of a row that no member has (entry 0 of row 5, and of row 7, of the state's main table is
  made one larger): `stateB` is false.
- a false answer to a sample in the state on entry (da = `oneE`): the claim and `valuesB` are false.
  Both are false also where no claim is passed, and no guard shows that at da = `oneE` `madeAt`
  returns no error and a claim is passed.

Limits.
- An evaluation by Lean's evaluator, outside the kernel: it leaves no theorem.
- One place.
- Not met here: rows over the base field · a first stage with h > 0 (a fresh table of two rows or
  more; two mask rows) · two members with main rows in two trees: these are met in
  Johnson/Desc/ProofFile/Honest/K12/ToyWide.lean.
- The term is evaluated whole; it is not played part by part through a book of coins.
- It is not the key file's place.
- `valuesB` gives all the hypotheses of `first_V` but one (`first_V_test`,
  Johnson/Desc/K12/Honest/FirstValuesTest.lean): that the state's fresh table is the packing of the
  hiding polynomial is not evaluated; the state here is `TestJob.first` (Test.lean), whose
  definition sets that table to `packedN` of `hideAt`.
- `At.accepts` is the format's test and the block's decision (`Block.decide`). The third check of a
  block's step (`Block.step`, Johnson/Desc/Block.lean), on the columns' keys, positions and widths,
  is not evaluated. Where `At.accepts` is false, which of its two checks fails is not evaluated.
- All negative tests but one evaluate the functions to Bool (`firstB`, `stateB`, `valuesB`, `endB`,
  `At.claim`), not the block.
- That `madeAt` returns no error is evaluated at answers and target 0 only. `stateAt` calls it at
  the answers and the target that the tables give, and takes `d0` on an error; no guard evaluates
  that call by itself.
- No negative test is next to the guards on `madeAt`, on `planOk`, on the number of trees and on
  `At.depths`.
- That the block accepts is a test at one example, no statement of completeness.
- The job's state on entry is computed in this file and is compared with no verifier's state.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyAt
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K1.Own

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyTrees
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS wordsOf wr mainSym maskSym)
open H2K.Pub (sgOf)

/-! ## 1 The place -/

/-- The lists of codes: three for main rows, three for mask rows. -/
def codes : Codes :=
  ⟨#[⟨5, 4, 2⟩, ⟨6, 2, 2⟩, ⟨8, 2, 2⟩], #[⟨4, 8, 2⟩, ⟨5, 16, 2⟩, ⟨7, 64, 2⟩]⟩
/-- The first stage: main code, mask code, k = 3, h = 0, two positions. -/
def s0 : Fmt.M1.Stage := ⟨⟨5, 4, 2⟩, ⟨4, 8, 2⟩, 3, 0, 2⟩
/-- The second stage: k = 1, h = 1. -/
def s1 : Fmt.M1.Stage := ⟨⟨6, 2, 2⟩, ⟨5, 16, 2⟩, 1, 1, 2⟩
/-- The last stage: k = 0, h = 0. -/
def s2 : Fmt.M1.Stage := ⟨⟨8, 2, 2⟩, ⟨7, 64, 2⟩, 0, 0, 2⟩
/-- The number of the first tree that the chain sends. -/
def ft : ℕ := 7
/-- Member 0 as it is announced: five main rows over the extension field, no mask row. -/
def nMain : OracleNotice := ⟨{ code := 0, mainRows := 5, mainDeg := 3, answers := 1 }, 0⟩
/-- Member 1 as it is announced: one mask row, no main row; another class of leaves. -/
def nMask : OracleNotice := ⟨{ maskRows := 1, maskCode := 0, answers := 1 }, 1⟩
/-- The parameters of the one sending that sends both members. -/
def send : K1.Par :=
  { place := ⟨2, none, 1, .K1⟩, codes := codes, gp := ⟨1, ft⟩, work := 0
    parts := [("main", #[nMain]), ("mask", #[nMask])] }
/-- The sending's first round: no item, six sampled elements. -/
def r1 : Fmt.RoundView :=
  ⟨[], ⟨[(5, 9, 2), (6, 5, 3), (5, 8, 9), (7, 9, 3), (2, 3, 8), (4, 6, 2)], [], [], none⟩⟩
/-- The state from which `madeAt` starts: the codes and nothing else. -/
def d0 : _root_.Desc.Plain.DState Unit := ⟨{ codes := codes }, {}, 0, [], ()⟩
/-- The point of the open row's vector of product form; its third coordinate is 0. -/
def pt : List E :=
  [E.ofTriple (8, 1, 1), E.ofTriple (2, 7, 1), zeroE, E.ofTriple (3, 1, 4), E.ofTriple (1, 5, 9)]
/-- The place's numbers. -/
def nums : H2U.TestNums :=
  { rows := 3, work := 0, stages := [s0, s1, s2], ownMask := true
    first := [(⟨5, 15, false, ft⟩, .own 0), (⟨4, 3, false, ft + 1⟩, .own 1)], free := 2
    firstTree := ft }
/-- The place. -/
def p : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ ⟨2, 0, nums, [(0, 0), (1, 1), (2, 2)], 1, 1, true⟩
/-- The place's declared rounds; the empty list where `H2U.roundsOfNums` gives none. -/
def declared : List Fmt.DeclaredRound := (H2U.roundsOfNums nums).getD []

/-! ## 2 The tables, and the state on entry at true values -/

/-- An element of the extension field from three numbers. -/
def tri (x y z : ℕ) : E := E.ofTriple (x.toUInt64, y.toUInt64, z.toUInt64)

/-- Member 0's main rows: row i, entry e. w: the prover's input, added to the first of the three
numbers of entry 0 of row 0. -/
def mainE (w i e : ℕ) : E :=
  tri (11 + 7 * i + e + (if i = 0 ∧ e = 0 then w else 0)) (3 + i) (5 + 2 * e)
/-- Member 0's rows' tails: row i, entry q. -/
def mainTlE (i q : ℕ) : E := tri (101 + 3 * i + q) 7 (1 + q)
/-- Member 1: its one mask row; its tail. -/
def maskE (e : ℕ) : E := tri (201 + e) (2 + e) 9
/-- The tail of member 1's mask row: entry q. -/
def maskTlE (q : ℕ) : E := tri (301 + q) 4 4

/-- The value of a row's left side at the two members' tables, at the input 0, by the row's own
coefficients. -/
def valOf (r : Row) : E :=
  addE
    (((List.range 32).map fun i =>
      mulE (r.coefficient 0 .main i) (if i % 8 < 5 then mainE 0 (i % 8) (i / 8) else zeroE)).foldl
      addE zeroE)
    (((List.range 8).map fun i => mulE (r.coefficient 1 .mask i) (maskE i)).foldl addE zeroE)

/-- The open row: on member 0's main table and entry kappa of member 1's mask table. tau: target. -/
def openRow (kappa : ℕ) (tau : E) : Row :=
  { ((({ } : Row).add 0 .main (Tensor.eq pt oneE)).addUnit 1 .mask kappa oneE) with target := tau }

/-- A state computed by the description's own functions, in this order: a new group; the sending's
decision on two rounds; two joinings; the next free entry of member 1's mask table; the open row.
a0, a1: the answers to the two samples. tau: gives the open row's target, from the open row at the
target 0. -/
def madeAt (a0 a1 : E) (tau : Row → E) : Except String (_root_.Desc.Plain.DState Unit) := do
  let g ← (Ground.newGroupP d0 0 0).elim (.error "the group") .ok
  let x ← K1.decideSend send none g.2
    [r1, ⟨[.answer a0.triple, .answer a1.triple], ⟨[], [], [], none⟩⟩]
  let a ← (Ground.joinP x.2 0 0 false).elim (.error "the first joining") .ok
  let b ← (Ground.joinP a 0 1 false).elim (.error "the second joining") .ok
  let k ← (Ground.takeMaskP b 1).elim (.error "the mask's entry") .ok
  (Ground.addRowP k.2 0 (openRow k.1 (tau (openRow k.1 zeroE)))).elim (.error "the open row") .ok

/-- The first sample row of oracle message o, read from `madeAt` at answers and target 0; the empty
row where `madeAt` returns an error. -/
def sampleOf (o : ℕ) : Row :=
  match madeAt zeroE zeroE fun _ => zeroE with
  | .ok d => ((d.st.oracles.getD o default).sampleRows.getD 0 {})
  | .error _ => {}

/-- The state on entry to the test: `madeAt` at the answers and the target that the tables give
(`valOf`); `d0` where `madeAt` returns an error. da: added to the first answer. -/
def stateAt (da : E) : T12 :=
  let d := (madeAt (addE (valOf (sampleOf 0)) da) (valOf (sampleOf 1)) valOf).toOption.getD d0
  ⟨d.st, d.book, d.roots, 0, .nothing, none⟩

/-- The state on entry at da = 0. No test in this file uses it. -/
def tTrue : T12 := stateAt zeroE

/-! ## 3 The job -/

/-- The first stage's tables and tails at the input w; the other fields are 0. -/
def rowsAt (w : ℕ) : PS where
  tabM := fun n => if n % 8 < 5 ∧ n / 8 < 4 then readE (mainE w (n % 8) (n / 8)) else 0
  tabZ := fun n => if n < 8 then readE (maskE n) else 0
  tM := fun b q => if b < 5 then readE (mainTlE b q) else 0
  tZ := fun b q => if b = 0 then readE (maskTlE q) else 0
  fM := fun _ _ => 0
  fT := fun _ _ => 0
  sM := fun _ => 0
  sT := fun _ => 0

/-- The address of the part that sent both members: part 0 at the sending's place. -/
def sender : Addr := ⟨⟨2, none, 1, .K1⟩, 0⟩

/-- The job. It reads neither the front nor the members' coins. da: see `stateAt`. -/
def J (da : E) : TestJob ℕ Unit where
  p := p
  members := [(sender, 0, ⟨0, 11⟩), (sender, 1, ⟨0, 3⟩)]
  fresh := none
  rec₀ := fun _ _ => stateAt da
  rows₀ := fun w _ _ => rowsAt w
  trees₀ := fun _ _ _ P =>
    [(5, fun x => wordsOf (wr 5 (mainSym (sgOf s0) P.tabM P.tM x))),
     (4, fun x => wordsOf (wr 1 (maskSym (sgOf s0) P.tabZ P.tZ x))),
     (4, freshCol (sgOf s0) P)]

/-- Written values put for the coins that `testAll` reads; 0 for the members' coins. -/
def coins : TestCoins :=
  ⟨fun i => readE (tri (401 + i) 1 2), fun _ q => readE (tri (501 + q) 3 1),
    fun _ => ⟨fun _ => 0, fun _ => 0⟩, fun i => readE (tri (601 + i) (1 + i) 7)⟩

/-- Challenges for the declared rounds, by a written formula; another list for another n. -/
def gen (n : ℕ) : List Fmt.Drawn :=
  declared.zipIdx.map fun d =>
    ⟨(List.range d.1.entry.drawE).map fun i =>
        ((3 + 5 * d.2 + i + n).toUInt64, (1 + d.2 + 2 * i).toUInt64, (2 + i + 3 * n).toUInt64),
      (List.range d.1.entry.poss).map fun i => (7 * i + 3 * d.2 + 1 + 5 * n) % 2 ^ d.1.entry.logN,
      [], none⟩

/-- How the members' rows are read from the first stage's state. Member 0 has the rows 0 to 4 of the
main table of eight; member 1 the mask table's one row. upZ: one more on the mask row's entry 0. -/
def lay (upZ : Bool) (P : PS) : PlainRows where
  M := fun j i e => if j = 0 then P.tabM (i + 8 * e) else 0
  T := fun j i q => if j = 0 then P.tM i q else 0
  Z := fun j i e =>
    (if j = 1 then P.tabZ (i + e) else 0) + (if upZ ∧ j = 1 ∧ i = 0 ∧ e = 0 then 1 else 0)
  ZT := fun j i q => if j = 1 then P.tZ i q else 0
  F := P.fM
  FT := P.fT

/-- The example's values. n: see `gen`. w: the prover's input. upZ: see `lay`. da: see `stateAt`.
Nothing precedes the test, and the example stands where no column is handed: `Seen.bare []`. -/
def three (n : ℕ) (w : ℕ := 0) (upZ : Bool := false) (da : E := zeroE) : At :=
  ⟨J da, ⟨[], (), Seen.bare []⟩, coins, gen n, lay upZ, w⟩

/-! ## 4 What is checked -/

-- `madeAt` returns no error at answers and target 0; the block's `planOk` is true
#guard Except.isOk (madeAt zeroE zeroE fun _ => zeroE) && (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk
-- three trees, of the depths that the book of trees states (`At.depths`)
#guard (three 0).places.length == 3 && (three 0).depths
-- the claim in the state after the batching is true at the written tables
#guard (three 0).claim && (three 1).claim
-- `firstB`, `stateB`, `valuesB`, and the conclusion of `first_V` (`endB`)
#guard (three 0).test none false false && (three 1).test none false false
#guard (three 0).state false false
#guard (three 0).values none false false && (three 1).values none false false
#guard (three 0).ends && (three 1).ends
-- the test's block accepts the term
#guard (three 0).accepts && (three 1).accepts
-- negative tests: word 0 of every column of one tree made one larger, for each of the three trees
#guard !(three 0).test (some 0) false false && !(three 0).test (some 1) false false &&
  !(three 0).test (some 2) false false
-- an entry of member 0's row; of the fresh table; of the mask row, in the plain rows
#guard !(three 0).test none true false && !(three 0).test none false true
#guard !(three 0 0 true).test none false false && !(three 0 0 true).state false false
-- the prover's tables at another input than the claim's
#guard (three 0 1).test none false false && (three 0 1).state false false
#guard !(three 0 1).claim && !(three 0 1).values none false false && !(three 0 1).ends
#guard !(three 0 1).accepts
-- an entry of a main row that no member has (rows 5 to 7) made one larger in the state: rows 5, 7
#guard !(three 0).stateUp 5 && !(three 0).stateUp 7
-- a false answer to a sample in the state on entry
#guard !(three 0 0 false oneE).claim && !(three 0 0 false oneE).values none false false

end ProofFile.Honest.K12.ToyTrees

#print axioms ProofFile.Honest.K12.ToyTrees.codes
#print axioms ProofFile.Honest.K12.ToyTrees.s0
#print axioms ProofFile.Honest.K12.ToyTrees.s1
#print axioms ProofFile.Honest.K12.ToyTrees.s2
#print axioms ProofFile.Honest.K12.ToyTrees.ft
#print axioms ProofFile.Honest.K12.ToyTrees.nMain
#print axioms ProofFile.Honest.K12.ToyTrees.nMask
#print axioms ProofFile.Honest.K12.ToyTrees.send
#print axioms ProofFile.Honest.K12.ToyTrees.r1
#print axioms ProofFile.Honest.K12.ToyTrees.d0
#print axioms ProofFile.Honest.K12.ToyTrees.pt
#print axioms ProofFile.Honest.K12.ToyTrees.nums
#print axioms ProofFile.Honest.K12.ToyTrees.p
#print axioms ProofFile.Honest.K12.ToyTrees.declared
#print axioms ProofFile.Honest.K12.ToyTrees.tri
#print axioms ProofFile.Honest.K12.ToyTrees.mainE
#print axioms ProofFile.Honest.K12.ToyTrees.mainTlE
#print axioms ProofFile.Honest.K12.ToyTrees.maskE
#print axioms ProofFile.Honest.K12.ToyTrees.maskTlE
#print axioms ProofFile.Honest.K12.ToyTrees.valOf
#print axioms ProofFile.Honest.K12.ToyTrees.openRow
#print axioms ProofFile.Honest.K12.ToyTrees.madeAt
#print axioms ProofFile.Honest.K12.ToyTrees.sampleOf
#print axioms ProofFile.Honest.K12.ToyTrees.stateAt
#print axioms ProofFile.Honest.K12.ToyTrees.tTrue
#print axioms ProofFile.Honest.K12.ToyTrees.rowsAt
#print axioms ProofFile.Honest.K12.ToyTrees.sender
#print axioms ProofFile.Honest.K12.ToyTrees.J
#print axioms ProofFile.Honest.K12.ToyTrees.coins
#print axioms ProofFile.Honest.K12.ToyTrees.gen
#print axioms ProofFile.Honest.K12.ToyTrees.lay
#print axioms ProofFile.Honest.K12.ToyTrees.three
