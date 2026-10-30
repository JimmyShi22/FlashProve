-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyLate.lean: a test at a third small made-up example. All
hypotheses of `test_accepts_all` (WholeAll.lean in this folder) hold together at a place whose first
stage has k = h and whose second has k > h. That is the form of the key file's test on the ranges,
(k, h) = (4, 4), (4, 3), (3, 3), (0, 0) at the written place `piKRFull`
(Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean), which neither ToyAll.lean's nor ToyCame.lean's place
has. The hypotheses are evaluated as the function to Bool `allB` (AllB.lean); the proof of its
theorem `accepts_of_allB` derives the hypotheses from the clauses of `allB`. The definitions are
ToyCame.lean's, written again at other numbers. Definitions, none marked `noncomputable`, two
theorems, and evaluations (`#guard`). Made-up numbers only.

Terms. A place (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a proximity test, among
them its stages (`Fmt.M1.Stage`: main code, mask code, k, h, number of positions). A job
(`TestJob`, Test.lean) is what a caller supplies for its test: the place, who sent the group's
oracle messages (the group's members, numbered from 0) and the first fold's fresh table, and
functions that give the state on entry to the test (`rec₀`; in the limits also: the state in front),
the first stage's rows and the trees. The block is `proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/Frame.lean,
JoinGuarded.lean). The clauses are the entries of `allL` (AllB.lean), each a name with a Bool. The front
(`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is what precedes the test. A stretch (`Stretch`,
Coins.lean) is a run of coins by number; the members' stretches are the field `mem` of `TestCoins`
(Test.lean). A book is a book of coins (`ProverCoinCounts`, Johnson/Desc/ProofFile/Honest/Frame.lean). In the
limits, "the title" is this head's first paragraph, and a layout "has no member" where no values are
written at which the hypotheses hold together in that layout.

The place. Four stages: (k 1, h 1), (k 2, h 1), (k 1, h 1), (k 0, h 0). Member 0: one main row over
the base field, in a tree of depth 5. Member 1: one main row over the extension field and one mask
row, in a tree of depth 5. Member 2: one mask row, in a tree of depth 4. The fresh table: two mask
rows, not sampled, in a tree of depth 4; it has come earlier. Main rows of sixteen entries.

  `allB_late`: all seventeen clauses are true at `late 0`: `allB ... = true`, a theorem, proved by
    evaluation in Lean's kernel (`decide +kernel`)
  `accepts_late`: so the block's decision accepts there what `testAll` (Test.lean) shows, and
    nothing is left untested in the state that it returns (`ChainEnd.NothingLeft`,
    Johnson/Desc/ChainEndLaw.lean)
  `late n w upZ da`: the example's values (`At`, ToyAt.lean): the job and its values. n: another
    list of challenges for another n. w: the prover's input; the job's state on entry does not read
    it: its answers and target are those of the written rows at the input 0 (`valOf`). upZ: see
    `lay`. da: see `stateAt`
  `onRec`, `onP`: the same values with the job's state on entry, or its place, changed by a
    function; no test in this file uses them
  `codes`, `s0`, `s1`, `s2`, `s3`: the lists of codes; the four stages
  `ft`: the number of the first tree that the chain sends
  `n0`, `n1`, `n2`, `n3`: the three members and the fresh table as they are announced
    (`OracleNotice`, OnBytes/Iop/Ground.lean)
  `send`: the parameters of the one sending that sends all four (`K1.Par`,
    Johnson/Desc/K1/Send.lean)
  `d0`: the state from which `madeAt` starts
  `nums`, `p`, `declared`: the place's numbers (`H2U.TestNums`, Johnson/Desc/K12/TestEntries.lean);
    the place; its declared rounds
  `genOf`, `r1`: challenges for a list of declared rounds, by a written formula; what the sending's
    first round sampled
  `tri`: an element of the extension field from three numbers
  `m0E`, `m0Tl`, `m1E`, `m1Tl`, `m1Z`, `m1ZTl`, `m2Z`, `m2ZTl`: the members' rows and the rows'
    tails, each by a written formula
  `sumOf`, `valOf`: a sum over a range; the value of a row's left side at these rows
  `openRow`: the one open row
  `madeAt`, `word`, `sampleOf`, `stateAt`: a state computed by the description's own functions
    (`K1.decideSend`, Johnson/Desc/K1/Own.lean; `Ground.newGroupP`, `joinP`, `takeMaskP`, `addRowP`,
    Johnson/Desc/First/Base/Ground.lean) at given answers and a given target; "ok" or an error's
    text; a message's first sample row in that state; the state on entry, at the answers and the
    target that the written rows give
  `rowsAt`, `sender`, `word1`, `J`, `coins`, `lay`: the first stage's tables; the address of the
    part that sent all four messages; a word of a field element; the job; the values put for the
    coins that `testAll` reads; how the members' rows are read from the first stage's state

By what. `allB_late` is proved by `decide +kernel`. `accepts_late` is `accepts_of_allB` (AllB.lean)
at `allB_late`.

What the `#guard` lines evaluate. At two lists of challenges (`late 0`, `late 1`): no clause fails
(`At.no`, ToyAll.lean); the block's decision, run on what `testAll` shows, accepts, with nothing
left untested (`At.yes`, ToyAll.lean); and the rounds pass the check of their form (`roundsFit`,
inside `At.accepts`, ToyAt.lean). Negative tests: each but the last is an equation on the list of
the names of the clauses that fail; the last evaluates `At.acc` and `At.yes` at `more`
(ToyAll.lean); see the comments at the tests.

Limits.
- The theorems are on one small made-up place at one list of challenges.
- Poorer than the place of the key file's test on the ranges, whose form the title names:
  four trees, where the ranges' place has one tree that holds the member, the masks and the fresh
  table: that layout at k = h has no member ·
  no sampled oracle message stands outside the group ·
  the front is empty, the state in front is a constant, the members' stretches are 0 and unread,
  and nothing is played through a book.
- Only two of the seventeen clauses are false in a test here (counted by reading the tests):
  "RestAsks" and "nothing is left untested behind the batching".
- Three things are not checked at this place here: `OpensFit` (ColsTerm.lean); the count of rounds
  (the field `count` of `K12At`, SaysYesK12.lean); the invariant after the first stage (`BodyInv`,
  Johnson/Prover/Link/BodyInv.lean, as `Wanted` of BodyInvFirst.lean states it).
- The negative tests are evaluations by Lean's evaluator, outside the kernel: they leave no theorem.
- That `madeAt` returns no error is evaluated at answers and target 0 only. `stateAt` calls it at
  the answers and the target that the written rows give, and takes `d0` on an error; no guard
  evaluates that call by itself.
- No negative test is next to the guards on `madeAt`, on the two `planOk`, on the numbers of stages
  and of trees and on `At.depths`.
- "Accepts" is `Block.decide ... = .ok`. `Block.step` (Johnson/Desc/Block.lean) is not run.
- The job's state on entry is computed in this file and is compared with no verifier's state.
- It is no place of a file: the numbers are made up, and no description of a file (`FileDescription`,
  Johnson/Desc/Block.lean) is named here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyAll
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K1.Own

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyLate
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS wordsOf wr mainSym maskSym)
open H2K.Pub (sgOf)

/-! ## 1 The place -/

/-- The codes: four of main rows, four of mask rows (log-length, message length, tail length). -/
def codes : Codes :=
  ⟨#[⟨5, 16, 2⟩, ⟨6, 4, 2⟩, ⟨7, 2, 2⟩, ⟨8, 2, 2⟩], #[⟨4, 4, 2⟩, ⟨5, 8, 2⟩, ⟨6, 16, 2⟩, ⟨7, 64, 2⟩]⟩
/-- The first stage: main code, mask code, k = 1, h = 1, two positions. -/
def s0 : Fmt.M1.Stage := ⟨⟨5, 16, 2⟩, ⟨4, 4, 2⟩, 1, 1, 2⟩
/-- The second stage: k = 2, h = 1. -/
def s1 : Fmt.M1.Stage := ⟨⟨6, 4, 2⟩, ⟨5, 8, 2⟩, 2, 1, 2⟩
/-- The third stage: k = 1, h = 1. -/
def s2 : Fmt.M1.Stage := ⟨⟨7, 2, 2⟩, ⟨6, 16, 2⟩, 1, 1, 2⟩
/-- The last stage: k = 0, h = 0. -/
def s3 : Fmt.M1.Stage := ⟨⟨8, 2, 2⟩, ⟨7, 64, 2⟩, 0, 0, 2⟩
/-- The number of the first tree that the chain sends. -/
def ft : ℕ := 7
/-- Member 0 as it is announced: one main row over the base field; leaf class 0. -/
def n0 : OracleNotice := ⟨{ code := 0, mainRows := 1, mainDeg := 1, answers := 1 }, 0⟩
/-- Member 1 as it is announced: one main row over the extension field, one mask row. -/
def n1 : OracleNotice :=
  ⟨{ code := 0, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 0, answers := 1 }, 1⟩
/-- Member 2 as it is announced: one mask row. -/
def n2 : OracleNotice := ⟨{ maskRows := 1, maskCode := 0, answers := 1 }, 2⟩
/-- The first fold's fresh table: two mask rows, not sampled. -/
def n3 : OracleNotice := ⟨{ maskRows := 2, maskCode := 0, answers := 0 }, 3⟩
/-- The parameters of the one sending that sends the three members and the fresh table. -/
def send : K1.Par :=
  { place := ⟨2, none, 1, .K1⟩, codes := codes, gp := ⟨1, ft⟩, work := 0
    parts := [("base", #[n0]), ("main", #[n1]), ("mask", #[n2]), ("fresh", #[n3])] }
/-- The state from which `madeAt` starts: the codes; no message, no group, no tree, no root. -/
def d0 : _root_.Desc.Plain.DState Unit := ⟨{ codes := codes }, {}, 0, [], ()⟩
/-- The place's numbers: four batched rows, the stages, the group's trees and the fresh table's. -/
def nums : H2U.TestNums :=
  { rows := 4, work := 0, stages := [s0, s1, s2, s3], ownMask := false
    first := [(⟨5, 1, false, ft⟩, .own 0), (⟨5, 6, false, ft + 1⟩, .own 1),
      (⟨4, 3, false, ft + 2⟩, .own 2), (⟨4, 6, false, ft + 3⟩, .own 3)], free := 4
    firstTree := ft }
/-- The place: `nums` on chain 2, with each stage's two code numbers. -/
def p : P12 :=
  H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ ⟨2, 0, nums, [(0, 0), (1, 1), (2, 2), (3, 3)], 1, 1, true⟩
/-- The place's declared rounds; the empty list where `roundsOfNums` gives none. -/
def declared : List Fmt.DeclaredRound := (H2U.roundsOfNums nums).getD []

/-- Challenges for a list of declared rounds, by a written formula; n selects the list. -/
def genOf (ds : List Fmt.DeclaredRound) (n : ℕ) : List Fmt.Drawn :=
  ds.zipIdx.map fun d =>
    ⟨(List.range d.1.entry.drawE).map fun i =>
        ((3 + 5 * d.2 + i + n).toUInt64, (1 + d.2 + 2 * i).toUInt64, (2 + i + 3 * n).toUInt64),
      (List.range d.1.entry.poss).map fun i => (7 * i + 3 * d.2 + 1 + 5 * n) % 2 ^ d.1.entry.logN,
      [], none⟩

/-- What the sending's first round sampled: the first element of `genOf` at n = 2. -/
def r1 : Fmt.RoundView := ⟨[], (genOf (K1.sendOwn (Cl := Unit) send).rounds 2).headD ⟨[], [], [], none⟩⟩

/-! ## 2 The tables, and the state on entry at true values -/

/-- An element of the extension field from three numbers. -/
def tri (x y z : ℕ) : E := E.ofTriple (x.toUInt64, y.toUInt64, z.toUInt64)

/-- Member 0, over the base field: row i, entry e; only row 0 is read. w: the input, added to entry
(0, 0). -/
def m0E (w i e : ℕ) : E := tri (11 + 7 * i + e + (if i = 0 ∧ e = 0 then w else 0)) 0 0
/-- The tails of member 0's rows: row i, entry q; only row 0 is read. -/
def m0Tl (i q : ℕ) : E := tri (101 + 3 * i + q) 0 0
/-- Member 1: one main row (number 0 of this text); one mask row; their tails. -/
def m1E (i e : ℕ) : E := tri (31 + 5 * i + e) (3 + i) (5 + 2 * e)
/-- The tails of member 1's main rows: row i, entry q; only row 0 is read. -/
def m1Tl (i q : ℕ) : E := tri (131 + 3 * i + q) 7 (1 + q)
/-- Member 1's mask row. -/
def m1Z (e : ℕ) : E := tri (201 + e) (2 + e) 9
/-- The tail of member 1's mask row. -/
def m1ZTl (q : ℕ) : E := tri (301 + q) 4 4
/-- Member 2: one mask row; its tail. -/
def m2Z (e : ℕ) : E := tri (221 + e) (6 + e) 3
/-- The tail of member 2's mask row. -/
def m2ZTl (q : ℕ) : E := tri (321 + q) 5 8

/-- The sum of f 0 to f (n - 1). -/
def sumOf (n : ℕ) (f : ℕ → E) : E := ((List.range n).map f).foldl addE zeroE

/-- The value of a row's left side at the written rows (input 0). In a member's own table the number
of rows is rounded up to a power of two; here each table has one row, so an index into it is the
entry's number. -/
def valOf (r : Row) : E :=
  addE (addE
    (sumOf 16 fun i => mulE (r.coefficient 0 .main i) (m0E 0 0 i))
    (sumOf 16 fun i => mulE (r.coefficient 1 .main i) (m1E 0 i)))
    (addE (sumOf 4 fun i => mulE (r.coefficient 1 .mask i) (m1Z i))
      (sumOf 4 fun i => mulE (r.coefficient 2 .mask i) (m2Z i)))

/-- The open row: single entries of the three members' tables. kappa: the next free entry of member
2's mask table. -/
def openRow (kappa : ℕ) (tau : E) : Row :=
  { (((({ } : Row).addUnit 0 .main 1 (tri 2 1 1)).addUnit 1 .main 2 (tri 3 5 1)).addUnit 2 .mask
      kappa oneE) with target := tau }

/-- The state after group, sending, joinings and open row. a: the answers; tau: the target. -/
def madeAt (a : ℕ → E) (tau : Row → E) : Except String (_root_.Desc.Plain.DState Unit) := do
  let g ← (Ground.newGroupP d0 0 0).elim (.error "the group") .ok
  let x ← K1.decideSend send none g.2
    [r1, ⟨[.answer (a 0).triple, .answer (a 1).triple, .answer (a 2).triple], ⟨[], [], [], none⟩⟩]
  let j0 ← (Ground.joinP x.2 0 0 false).elim (.error "the first joining") .ok
  let j1 ← (Ground.joinP j0 0 1 false).elim (.error "the second joining") .ok
  let j2 ← (Ground.joinP j1 0 2 false).elim (.error "the third joining") .ok
  let k ← (Ground.takeMaskP j2 2).elim (.error "the mask's entry") .ok
  (Ground.addRowP k.2 0 (openRow k.1 (tau (openRow k.1 zeroE)))).elim (.error "the open row") .ok

/-- "ok", or the error's text. -/
def word {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => e

/-- The first sample row of oracle message o in `madeAt` at answers and target 0. -/
def sampleOf (o : ℕ) : Row :=
  match madeAt (fun _ => zeroE) fun _ => zeroE with
  | .ok d => ((d.st.oracles.getD o default).sampleRows.getD 0 {})
  | .error _ => {}

/-- The state on entry, at the answers and the target that the written rows give (`valOf`). Its
field `mask` names message 3, the fresh table. da: added to the first answer. Where `madeAt` returns
an error, the state is taken from `d0`. -/
def stateAt (da : E) : T12 :=
  let d := (madeAt (fun o => addE (valOf (sampleOf o)) (if o = 0 then da else zeroE))
    valOf).toOption.getD d0
  ⟨d.st, d.book, d.roots, 0, .nothing, some 3⟩

/-! ## 3 The job -/

/-- The stage's tables: main row 0: member 0; 1: member 1. Mask row 0: member 1; 1: member 2. -/
def rowsAt (w : ℕ) : PS where
  tabM := fun n =>
    let b := n % 2
    let e := n / 2
    if e < 16 then (if b = 0 then readE (m0E w 0 e) else readE (m1E 0 e)) else 0
  tabZ := fun n =>
    if n / 2 < 4 then (if n % 2 = 0 then readE (m1Z (n / 2)) else readE (m2Z (n / 2))) else 0
  tM := fun b q =>
    if b = 0 then readE (m0Tl 0 q) else if b = 1 then readE (m1Tl 0 q) else 0
  tZ := fun b q => if b = 0 then readE (m1ZTl q) else if b = 1 then readE (m2ZTl q) else 0
  fM := fun _ _ => 0
  fT := fun _ _ => 0
  sM := fun _ => 0
  sT := fun _ => 0

/-- The address of the part that sent all four oracle messages: part 0 at the sending's place. -/
def sender : Addr := ⟨⟨2, none, 1, .K1⟩, 0⟩

/-- One word of an element of the base field. -/
def word1 (x : GE) : UInt64 := (ofE x).1

/-- The job. da: see `stateAt`. -/
def J (da : E) : TestJob ℕ Unit where
  p := p
  members := [(sender, 0, ⟨0, 7⟩), (sender, 1, ⟨0, 7⟩), (sender, 2, ⟨0, 3⟩)]
  fresh := some (sender, 3)
  rec₀ := fun _ _ => stateAt da
  rows₀ := fun w _ _ => rowsAt w
  trees₀ := fun _ _ _ P =>
    [(5, fun x => [word1 (mainSym (sgOf s0) P.tabM P.tM x 0)]),
     (5, fun x => wordsOf [ofE (mainSym (sgOf s0) P.tabM P.tM x 1),
        ofE (maskSym (sgOf s0) P.tabZ P.tZ x 0)]),
     (4, fun x => wordsOf [ofE (maskSym (sgOf s0) P.tabZ P.tZ x 1)]),
     (4, freshCol (sgOf s0) P)]

/-- The values put for the coins that `testAll` reads: written numbers; 0 for the members' coins. -/
def coins : TestCoins :=
  ⟨fun i => readE (tri (401 + i) 1 2), fun b q => readE (tri (501 + 2 * b + q) 3 1),
    fun _ => ⟨fun _ => 0, fun _ => 0⟩, fun i => readE (tri (601 + i) (1 + i) 7)⟩

/-- How the members' rows are read from the first stage's state. upZ: one more on entry 0 of member
2's mask row. -/
def lay (upZ : Bool) (P : PS) : PlainRows where
  M := fun j i e =>
    if j = 0 then P.tabM (i + 2 * e) else if j = 1 then P.tabM (1 + i + 2 * e) else 0
  T := fun j i q => if j = 0 then P.tM i q else if j = 1 then P.tM (1 + i) q else 0
  Z := fun j i e =>
    (if j = 1 then P.tabZ (i + 2 * e) else if j = 2 then P.tabZ (1 + i + 2 * e) else 0) +
      (if upZ ∧ j = 2 ∧ i = 0 ∧ e = 0 then 1 else 0)
  ZT := fun j i q => if j = 1 then P.tZ i q else if j = 2 then P.tZ (1 + i) q else 0
  F := P.fM
  FT := P.fT

/-- The example's values. n: which challenges; w: the input; upZ: see `lay`; da: see `stateAt`.
Nothing precedes the test, and the example stands where no column is handed: `Seen.bare []`. -/
def late (n : ℕ) (w : ℕ := 0) (upZ : Bool := false) (da : E := zeroE) : At :=
  ⟨J da, ⟨[], (), Seen.bare []⟩, coins, genOf declared n, lay upZ, w⟩

/-! ## 4 What is proved and what is evaluated -/

/-- The job's state on entry changed by f. -/
def onRec (A : At) (f : T12 → T12) : At :=
  { A with J := { A.J with rec₀ := fun w fr => f (A.J.rec₀ w fr) } }

/-- The job's place changed by f. -/
def onP (A : At) (f : P12 → P12) : At := { A with J := { A.J with p := f A.J.p } }

set_option maxRecDepth 100000 in
/-- **All seventeen clauses are true at `late 0`**, by evaluation in Lean's kernel. -/
theorem allB_late : allB (late 0).J (late 0).w (late 0).fr (late 0).C (late 0).D
    ((late 0).lay (late 0).P) = true := by decide +kernel

/-- **So the conclusion of `accepts_of_allB` holds there**: the block's decision accepts what
`testAll` shows, and nothing is left untested. -/
theorem accepts_late : ∃ t', (proximityTestKind guardedProximityTestParts (late 0).J.p : Block T12 Unit).decide
    ((late 0).J.rec₀ (late 0).w (late 0).fr)
    ((testAll (late 0).J (late 0).w (late 0).fr (late 0).C (late 0).D).rs.map noDigest)
    (testAll (late 0).J (late 0).w (late 0).fr (late 0).C (late 0).D).gs = .ok t' ∧
    ChainEnd.NothingLeft t'.st :=
  accepts_of_allB _ _ _ _ _ _ allB_late

-- `madeAt` returns no error at answers and target 0; the sending's and the test's `planOk` are true
#guard word (madeAt (fun _ => zeroE) fun _ => zeroE) == "ok"
#guard (K1.sendOwn (Cl := Unit) send).planOk && (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk
-- four stages; four trees, of the depths that the group's plain data states (`At.depths`)
#guard p.nums.stages.length == 4 && (late 0).places.length == 4 && (late 0).depths
-- the example once more, by the evaluator, at two lists of challenges: no clause fails; the block's
-- decision, run, accepts
#guard (late 0).no == [] && (late 1).no == []
#guard (late 0).accepts && (late 1).accepts && (late 0).yes && (late 1).yes
-- negative: another input; an entry of a mask row in the plain rows; a false answer to a sample
#guard (late 0 1).no == ["RestAsks"] && (late 0 0 true).no == ["RestAsks"] &&
  (late 0 0 false oneE).no == ["RestAsks"]
-- one group more, on which no test has begun: only that clause fails; the block's decision, run,
-- accepts, and something is left untested
#guard (more (late 0)).no == ["nothing is left untested behind the batching"]
#guard (more (late 0)).acc && !(more (late 0)).yes

end ProofFile.Honest.K12.ToyLate

#print axioms ProofFile.Honest.K12.ToyLate.allB_late
#print axioms ProofFile.Honest.K12.ToyLate.accepts_late
#print axioms ProofFile.Honest.K12.ToyLate.codes
#print axioms ProofFile.Honest.K12.ToyLate.s0
#print axioms ProofFile.Honest.K12.ToyLate.s1
#print axioms ProofFile.Honest.K12.ToyLate.s2
#print axioms ProofFile.Honest.K12.ToyLate.s3
#print axioms ProofFile.Honest.K12.ToyLate.ft
#print axioms ProofFile.Honest.K12.ToyLate.n0
#print axioms ProofFile.Honest.K12.ToyLate.n1
#print axioms ProofFile.Honest.K12.ToyLate.n2
#print axioms ProofFile.Honest.K12.ToyLate.n3
#print axioms ProofFile.Honest.K12.ToyLate.send
#print axioms ProofFile.Honest.K12.ToyLate.d0
#print axioms ProofFile.Honest.K12.ToyLate.nums
#print axioms ProofFile.Honest.K12.ToyLate.p
#print axioms ProofFile.Honest.K12.ToyLate.declared
#print axioms ProofFile.Honest.K12.ToyLate.genOf
#print axioms ProofFile.Honest.K12.ToyLate.r1
#print axioms ProofFile.Honest.K12.ToyLate.tri
#print axioms ProofFile.Honest.K12.ToyLate.m0E
#print axioms ProofFile.Honest.K12.ToyLate.m0Tl
#print axioms ProofFile.Honest.K12.ToyLate.m1E
#print axioms ProofFile.Honest.K12.ToyLate.m1Tl
#print axioms ProofFile.Honest.K12.ToyLate.m1Z
#print axioms ProofFile.Honest.K12.ToyLate.m1ZTl
#print axioms ProofFile.Honest.K12.ToyLate.m2Z
#print axioms ProofFile.Honest.K12.ToyLate.m2ZTl
#print axioms ProofFile.Honest.K12.ToyLate.sumOf
#print axioms ProofFile.Honest.K12.ToyLate.valOf
#print axioms ProofFile.Honest.K12.ToyLate.openRow
#print axioms ProofFile.Honest.K12.ToyLate.madeAt
#print axioms ProofFile.Honest.K12.ToyLate.word
#print axioms ProofFile.Honest.K12.ToyLate.sampleOf
#print axioms ProofFile.Honest.K12.ToyLate.stateAt
#print axioms ProofFile.Honest.K12.ToyLate.rowsAt
#print axioms ProofFile.Honest.K12.ToyLate.sender
#print axioms ProofFile.Honest.K12.ToyLate.word1
#print axioms ProofFile.Honest.K12.ToyLate.J
#print axioms ProofFile.Honest.K12.ToyLate.coins
#print axioms ProofFile.Honest.K12.ToyLate.lay
#print axioms ProofFile.Honest.K12.ToyLate.late
#print axioms ProofFile.Honest.K12.ToyLate.onRec
#print axioms ProofFile.Honest.K12.ToyLate.onP
