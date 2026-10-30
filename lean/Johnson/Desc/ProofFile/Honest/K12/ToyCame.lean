-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyCame.lean: a test at a second small made-up example. All
hypotheses of `test_accepts_all` (WholeAll.lean in this folder) hold together at a place of four
stages whose group is in three trees, with the first fold's fresh table, which has come earlier, in
a fourth. The hypotheses are evaluated as the function to Bool `allB` (AllB.lean); the proof of its
theorem `accepts_of_allB` derives the hypotheses from the clauses of `allB`. The first such example
is in ToyAll.lean. Definitions, none marked `noncomputable`, three theorems, and evaluations
(`#guard`). Made-up numbers only.

Terms. A place (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a proximity test, among
them its stages (`Fmt.M1.Stage`: main code, mask code, k, h, number of positions). A job
(`TestJob`, Test.lean) is what a caller supplies for its test: the place, who sent the group's
oracle messages (the group's members, numbered from 0) and the fresh table, and functions that give
the state on entry to the test, the first stage's rows and the trees. The term is `testAll`
(Test.lean): all that is shown in the test. The block is `proximityTestKind guardedProximityTestParts p`
(Johnson/Desc/K12/Frame.lean, JoinGuarded.lean). The clauses are the entries of `allL` (AllB.lean), each
a name with a Bool. "This member", said of the example and not of the group: a choice of values at
which the hypotheses hold together. A book of coins is `ProverCoinCounts`
(Johnson/Desc/ProofFile/Honest/Frame.lean).

The place. Four stages: (k 3, h 1), (k 1, h 1), (k 1, h 1), (k 0, h 0). Member 0: three main rows
over the base field, in a tree of depth 5. Member 1: two main rows over the extension field and one
mask row, in a tree of depth 5. Member 2: one mask row and no main row, in a tree of depth 4. The
fresh table: two mask rows, not sampled, in a tree of depth 4. One open row and three sample rows
are batched.

  `allB_came`: all seventeen clauses are true at `came 0`: `allB ... = true`, a theorem, proved by
    evaluation in Lean's kernel (`decide +kernel`)
  `coreB_came`: in the same way, so are the sixteen clauses of `coreB` (AllB.lean)
  `accepts_came`: so the block's decision accepts there what the term shows, and nothing is left
    untested in the state that it returns (`ChainEnd.NothingLeft`, Johnson/Desc/ChainEndLaw.lean)
  `came n w upZ da`: the example's values (`At`, ToyAt.lean): the job and its values. n: another
    list of challenges for another n. w: the prover's input; the job's state on entry does not read
    it: its answers and target are those of the written rows at the input 0 (`valOf`). upZ: see
    `lay`. da: see `stateAt`
  `onRec`, `onP`: the same values with the job's state on entry, or its place, changed by a function
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
  `madeAt`, `word`, `sampleOf`, `stateAt`: a state computed by the description's own functions at
    given answers and a given target; "ok" or an error's text; a message's first sample row in that
    state; the state on entry, at the answers and the target that the written rows give
  `rowsAt`, `sender`, `word1`, `J`, `coins`, `lay`: the first stage's tables; the address of the
    part that sent all four messages; a word of a field element; the job; the values put for the
    coins that the term reads; how the members' rows are read from the first stage's state

By what. `allB_came` and `coreB_came` are proved by `decide +kernel`. `accepts_came` is
`accepts_of_allB` (AllB.lean) at `allB_came`.

What the `#guard` lines evaluate. At two lists of challenges (`came 0`, `came 1`): no clause fails
(`At.no`, ToyAll.lean); the block's decision, run on what the term shows, accepts, with nothing left
untested (`At.yes`, ToyAll.lean); and the rounds pass the check of their form (`roundsFit`, inside
`At.accepts`, ToyAt.lean). Negative tests: each but the last is an equation on the list of the names
of the clauses that fail; the last evaluates `At.acc` and `At.yes` at `more` (ToyAll.lean); see the
comments at the tests.

How it is built. The group, and the way in which a state on entry to the test is computed by the
description's own functions, are those of ToyWideJob.lean in this folder, written again with main
rows of eight entries, one stage more, and the fresh table sent in the same sending as the members.
`lay` is that of ToyWide.lean.

What this member has that ToyAll.lean's has not: a step from a later stage to a later one that is
not the last · a first stage with h > 0: members' mask rows, a fresh table of two rows · rows over
the base field · several trees at the first switch, two of them shorter than the main code's · a
second list of challenges (by the evaluator).

Limits.
- The theorems are on one small made-up place at one list of challenges.
- Here and in ToyAll.lean the first stage has k > h and every later stage k = h. A first stage with
  k = h and a later one with k > h: ToyLate.lean.
- The negative tests are evaluations by Lean's evaluator, outside the kernel: they leave no theorem.
- That `madeAt` returns no error is evaluated at answers and target 0 only. `stateAt` calls it at
  the answers and the target that the written rows give, and takes `d0` on an error; no guard
  evaluates that call by itself.
- No negative test is next to the guards on `madeAt`, on the two `planOk`, on the numbers of stages
  and of trees and on `At.depths`.
- Eight of the seventeen clauses are false in no test here or in ToyAll.lean (counted by reading
  the tests): "the place has rounds" · "the place has oracle messages" · "the mark tidy" · "no row
  has a written-out factor" · "the front's test on the open rows" (`claimsB`) · "BAT's challenges
  have the declared form" · "the batching has one round" · "the batching opens nothing".
- The term is evaluated whole; it is not played part by part through a book of coins.
- "Accepts" is `Block.decide ... = .ok`. `Block.step` (Johnson/Desc/Block.lean) is not run.
- What precedes the test (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is empty. The job's state
  on entry is the same at every input and is compared with no verifier's state. The values put for
  the members' coins are 0, and the job does not read them.
- It is no place of a file: the numbers are made up, and no description of a proof file
  (`FileDescription`, Johnson/Desc/Block.lean) is named here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyAll
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K1.Own

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyCame
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS wordsOf wr mainSym maskSym)
open H2K.Pub (sgOf)

/-! ## 1 The place -/

/-- The codes: four of main rows, four of mask rows (log-length, message length, tail length). -/
def codes : Codes :=
  ⟨#[⟨5, 8, 2⟩, ⟨6, 4, 2⟩, ⟨7, 2, 2⟩, ⟨9, 2, 2⟩], #[⟨4, 8, 2⟩, ⟨5, 16, 2⟩, ⟨6, 32, 2⟩, ⟨8, 128, 2⟩]⟩
/-- The first stage: main code, mask code, k = 3, h = 1, two positions. -/
def s0 : Fmt.M1.Stage := ⟨⟨5, 8, 2⟩, ⟨4, 8, 2⟩, 3, 1, 2⟩
/-- The second stage: k = 1, h = 1. -/
def s1 : Fmt.M1.Stage := ⟨⟨6, 4, 2⟩, ⟨5, 16, 2⟩, 1, 1, 2⟩
/-- The third stage: k = 1, h = 1. -/
def s2 : Fmt.M1.Stage := ⟨⟨7, 2, 2⟩, ⟨6, 32, 2⟩, 1, 1, 2⟩
/-- The last stage: k = 0, h = 0. -/
def s3 : Fmt.M1.Stage := ⟨⟨9, 2, 2⟩, ⟨8, 128, 2⟩, 0, 0, 2⟩
/-- The number of the first tree that the chain sends. -/
def ft : ℕ := 7
/-- Member 0 as it is announced: three main rows over the base field; leaf class 0. -/
def n0 : OracleNotice := ⟨{ code := 0, mainRows := 3, mainDeg := 1, answers := 1 }, 0⟩
/-- Member 1 as it is announced: two main rows over the extension field, one mask row. -/
def n1 : OracleNotice :=
  ⟨{ code := 0, mainRows := 2, mainDeg := 3, maskRows := 1, maskCode := 0, answers := 1 }, 1⟩
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
    first := [(⟨5, 3, false, ft⟩, .own 0), (⟨5, 9, false, ft + 1⟩, .own 1),
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

/-- Member 0, over the base field: row i, entry e. w: the input, added to entry (0, 0). -/
def m0E (w i e : ℕ) : E := tri (11 + 7 * i + e + (if i = 0 ∧ e = 0 then w else 0)) 0 0
/-- The tails of member 0's rows: row i, entry q. -/
def m0Tl (i q : ℕ) : E := tri (101 + 3 * i + q) 0 0
/-- Member 1: two main rows; one mask row; their tails. -/
def m1E (i e : ℕ) : E := tri (31 + 5 * i + e) (3 + i) (5 + 2 * e)
/-- The tails of member 1's main rows. -/
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
of rows is rounded up to a power of two. -/
def valOf (r : Row) : E :=
  addE (addE
    (sumOf 32 fun i =>
      mulE (r.coefficient 0 .main i) (if i % 4 < 3 then m0E 0 (i % 4) (i / 4) else zeroE))
    (sumOf 16 fun i => mulE (r.coefficient 1 .main i) (m1E (i % 2) (i / 2))))
    (addE (sumOf 8 fun i => mulE (r.coefficient 1 .mask i) (m1Z i))
      (sumOf 8 fun i => mulE (r.coefficient 2 .mask i) (m2Z i)))

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

/-- The state on entry, at the answers and the target that the written rows give; its field `mask`
names message 3. da: added to the first answer. Where `madeAt` returns an error, the state is built
from `d0`. -/
def stateAt (da : E) : T12 :=
  let d := (madeAt (fun o => addE (valOf (sampleOf o)) (if o = 0 then da else zeroE))
    valOf).toOption.getD d0
  ⟨d.st, d.book, d.roots, 0, .nothing, some 3⟩

/-! ## 3 The job -/

/-- The stage's tables: main rows 0 to 2: member 0; 4, 5: member 1. Mask rows 0: member 1; 1: member
2. -/
def rowsAt (w : ℕ) : PS where
  tabM := fun n =>
    let b := n % 8
    let e := n / 8
    if e < 8 then
      (if b < 3 then readE (m0E w b e) else if 4 ≤ b ∧ b < 6 then readE (m1E (b - 4) e) else 0)
    else 0
  tabZ := fun n =>
    if n / 2 < 8 then (if n % 2 = 0 then readE (m1Z (n / 2)) else readE (m2Z (n / 2))) else 0
  tM := fun b q =>
    if b < 3 then readE (m0Tl b q) else if 4 ≤ b ∧ b < 6 then readE (m1Tl (b - 4) q) else 0
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
    [(5, fun x => (List.range 3).map fun b => word1 (mainSym (sgOf s0) P.tabM P.tM x b)),
     (5, fun x => wordsOf ([4, 5].map (fun b => ofE (mainSym (sgOf s0) P.tabM P.tM x b)) ++
        [ofE (maskSym (sgOf s0) P.tabZ P.tZ x 0)])),
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
    if j = 0 then P.tabM (i + 8 * e) else if j = 1 then P.tabM (4 + i + 8 * e) else 0
  T := fun j i q => if j = 0 then P.tM i q else if j = 1 then P.tM (4 + i) q else 0
  Z := fun j i e =>
    (if j = 1 then P.tabZ (i + 2 * e) else if j = 2 then P.tabZ (1 + i + 2 * e) else 0) +
      (if upZ ∧ j = 2 ∧ i = 0 ∧ e = 0 then 1 else 0)
  ZT := fun j i q => if j = 1 then P.tZ i q else if j = 2 then P.tZ (1 + i) q else 0
  F := P.fM
  FT := P.fT

/-- The example's values. n: which challenges; w: the input; upZ: see `lay`; da: see `stateAt`.
Nothing precedes the test, and the example stands where no column is handed: `Seen.bare []`. -/
def came (n : ℕ) (w : ℕ := 0) (upZ : Bool := false) (da : E := zeroE) : At :=
  ⟨J da, ⟨[], (), Seen.bare []⟩, coins, genOf declared n, lay upZ, w⟩

/-! ## 4 What is proved and what is evaluated -/

/-- The job's state on entry changed by f. -/
def onRec (A : At) (f : T12 → T12) : At :=
  { A with J := { A.J with rec₀ := fun w fr => f (A.J.rec₀ w fr) } }

/-- The job's place changed by f. -/
def onP (A : At) (f : P12 → P12) : At := { A with J := { A.J with p := f A.J.p } }

set_option maxRecDepth 100000 in
/-- **All seventeen clauses are true at `came 0`**, by evaluation in Lean's kernel. -/
theorem allB_came : allB (came 0).J (came 0).w (came 0).fr (came 0).C (came 0).D
    ((came 0).lay (came 0).P) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The sixteen clauses of `coreB` are true there too. -/
theorem coreB_came : coreB (came 0).J (came 0).w (came 0).fr (came 0).C (came 0).D
    ((came 0).lay (came 0).P) = true := by decide +kernel

/-- **So the conclusion of `accepts_of_allB` holds there**: the block's decision accepts what
`testAll` shows, and nothing is left untested. -/
theorem accepts_came : ∃ t', (proximityTestKind guardedProximityTestParts (came 0).J.p : Block T12 Unit).decide
    ((came 0).J.rec₀ (came 0).w (came 0).fr)
    ((testAll (came 0).J (came 0).w (came 0).fr (came 0).C (came 0).D).rs.map noDigest)
    (testAll (came 0).J (came 0).w (came 0).fr (came 0).C (came 0).D).gs = .ok t' ∧
    ChainEnd.NothingLeft t'.st :=
  accepts_of_allB _ _ _ _ _ _ allB_came

-- `madeAt` returns no error at answers and target 0; the sending's and the test's `planOk` are true
#guard word (madeAt (fun _ => zeroE) fun _ => zeroE) == "ok"
#guard (K1.sendOwn (Cl := Unit) send).planOk && (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk
-- four stages; four trees, of the depths that the group's plain data states (`At.depths`)
#guard p.nums.stages.length == 4 && (came 0).places.length == 4 && (came 0).depths
-- the example once more, by the evaluator, at two lists of challenges: no clause fails; the block's
-- decision, run, accepts
#guard (came 0).no == [] && (came 1).no == []
#guard (came 0).accepts && (came 1).accepts && (came 0).yes && (came 1).yes
-- negative: another input; an entry of a mask row in the plain rows; a false answer to a sample
#guard (came 0 1).no == ["RestAsks"] && (came 0 0 true).no == ["RestAsks"] &&
  (came 0 0 false oneE).no == ["RestAsks"]
-- a member named as the fresh table; another code's number for the second stage: the batching
-- passes no claim
#guard (onRec (came 0) fun t => { t with mask := some 2 }).no ==
  ["three stages or more, and a claim behind the batching"]
#guard (onP (came 0) fun q => { q with idx := q.idx.set 1 (2, 1) }).no ==
  ["three stages or more, and a claim behind the batching"]
-- one root more in the state on entry
#guard (onRec (came 0) fun t => { t with roots := t.roots + 1 }).no ==
  ["all that is public in front of the first stage (Sh.firstB)"]
-- an oracle message that names no group
#guard (onRec (came 0) fun t => { t with st := { t.st with
    oracles := t.st.oracles.modify 0 fun x => { x with groups := [] } } }).no ==
  ["all that is public in front of the first stage (Sh.firstB)",
    "nothing is left untested behind the batching"]
-- two answers to a sample; the last round's oracle messages cut off
#guard (onP (came 0) fun q => { q with answers := 2 }).no ==
  ["all that is public in front of the first stage (Sh.firstB)", "SwitchPlan at the first switch",
    "the plan from the second stage on (planFromOk)"]
#guard (onP (came 0) fun q => { q with oracles := q.oracles.dropLast }).no ==
  ["the plan from the second stage on (planFromOk)",
    "the sorts of the items from the second stage on"]
-- one group more, on which no test has begun: only that clause fails; the block's decision, run,
-- accepts, and something is left untested
#guard (more (came 0)).no == ["nothing is left untested behind the batching"]
#guard (more (came 0)).acc && !(more (came 0)).yes

end ProofFile.Honest.K12.ToyCame

#print axioms ProofFile.Honest.K12.ToyCame.allB_came
#print axioms ProofFile.Honest.K12.ToyCame.coreB_came
#print axioms ProofFile.Honest.K12.ToyCame.accepts_came
#print axioms ProofFile.Honest.K12.ToyCame.codes
#print axioms ProofFile.Honest.K12.ToyCame.s0
#print axioms ProofFile.Honest.K12.ToyCame.s1
#print axioms ProofFile.Honest.K12.ToyCame.s2
#print axioms ProofFile.Honest.K12.ToyCame.s3
#print axioms ProofFile.Honest.K12.ToyCame.ft
#print axioms ProofFile.Honest.K12.ToyCame.n0
#print axioms ProofFile.Honest.K12.ToyCame.n1
#print axioms ProofFile.Honest.K12.ToyCame.n2
#print axioms ProofFile.Honest.K12.ToyCame.n3
#print axioms ProofFile.Honest.K12.ToyCame.send
#print axioms ProofFile.Honest.K12.ToyCame.d0
#print axioms ProofFile.Honest.K12.ToyCame.nums
#print axioms ProofFile.Honest.K12.ToyCame.p
#print axioms ProofFile.Honest.K12.ToyCame.declared
#print axioms ProofFile.Honest.K12.ToyCame.genOf
#print axioms ProofFile.Honest.K12.ToyCame.r1
#print axioms ProofFile.Honest.K12.ToyCame.tri
#print axioms ProofFile.Honest.K12.ToyCame.m0E
#print axioms ProofFile.Honest.K12.ToyCame.m0Tl
#print axioms ProofFile.Honest.K12.ToyCame.m1E
#print axioms ProofFile.Honest.K12.ToyCame.m1Tl
#print axioms ProofFile.Honest.K12.ToyCame.m1Z
#print axioms ProofFile.Honest.K12.ToyCame.m1ZTl
#print axioms ProofFile.Honest.K12.ToyCame.m2Z
#print axioms ProofFile.Honest.K12.ToyCame.m2ZTl
#print axioms ProofFile.Honest.K12.ToyCame.sumOf
#print axioms ProofFile.Honest.K12.ToyCame.valOf
#print axioms ProofFile.Honest.K12.ToyCame.openRow
#print axioms ProofFile.Honest.K12.ToyCame.madeAt
#print axioms ProofFile.Honest.K12.ToyCame.word
#print axioms ProofFile.Honest.K12.ToyCame.sampleOf
#print axioms ProofFile.Honest.K12.ToyCame.stateAt
#print axioms ProofFile.Honest.K12.ToyCame.rowsAt
#print axioms ProofFile.Honest.K12.ToyCame.sender
#print axioms ProofFile.Honest.K12.ToyCame.word1
#print axioms ProofFile.Honest.K12.ToyCame.J
#print axioms ProofFile.Honest.K12.ToyCame.coins
#print axioms ProofFile.Honest.K12.ToyCame.lay
#print axioms ProofFile.Honest.K12.ToyCame.came
#print axioms ProofFile.Honest.K12.ToyCame.onRec
#print axioms ProofFile.Honest.K12.ToyCame.onP
