-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanOkNat.lean: A TEST ON A PLAN THAT A VERIFIER CAN RUN: `planOk M`: comparisons of
natural numbers, over the planner's records and the plans' own entries. It imports the planner and
the format (and, through them, the hash): no Mathlib, and no file on codes.
Johnson/Bridge/PlanOkNatEq.lean proves `planOk M = planOkB M` (Johnson/Bridge/PlanWhole.lean), whose
yes the theorems of this folder spend. [Neither of these two files is in this library, nor is any
theorem that spends that yes.]

What it asks, in short. Of the rounds of a proof file's, a key file's and an entry file's plans it
reads those of nine names: «BAT», «FOLD epsilon», «FOLD round», «SEND seed», «CS», «BASE lambda»,
«BASE», «LOC», «LIN point»: by a look at stored plans, the rounds in whose error a code's distance,
a bound on a list or a count of bad points of a line stands, but for «RECORD», «LINK point» and
«LINK», which it does not read. Each such entry must have its round's form; what it draws is held
against the records' stage, but for the positions of a stored table's «LOC», the coordinates of a
«SEND seed» outside the code switches and the rows of a «BAT», which are the entry's own; and a
count, made of the records' numbers and the entry's, must be at most 2^-128 of all its challenges,
the entry's bits of proof of work counted in. That the count bounds the round's bad challenges is
proved for the folds, the code switches and the base cases, and, under hypotheses on the block, for
«LIN point» (elsewhere, and of rounds of the format's form); for «LOC», «BAT» and the other «SEND
seed» it is by reading. Of every other entry it asks only that it has at most 62 bits of work and
stands for one round.

This file holds numbers of coding theory as bare arithmetic; it uses no statement on codes and
proves nothing. What its numbers are called (a bound on a list; a count of bad points of a line)
leans on theorems of other files, and the count of bad points on the files under ThirdParty/: files
adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

How to read it. A STAGE is a group of the planner (two codes: for main rows and for mask rows; k row
variables, of which the mask rows have h) with its number t of drawn positions; it is carried as the
pair (g, t), with its RADIUS e beside it: ((g, t), e). q is the size of the field of the challenges.
Section 1: numbers of a code and a stage. Section 2: the bracket of the count of bad points of a
line. Section 3: the three kinds of places: a fold, a base case, a code switch. Section 4: one
comparison for every round. Section 5: slots, against which a plan's entries are held. Section 6:
the records. Section 7: the tests. Section 8: `planOk`.

What it calls and does not spell. THE RADII ARE THE PLANNER's OWN: `radius` and `tableRadOf` call
its analysis (`analysisOfM`, `tableAnalysis`: interval arithmetic on numbers m · 2^e) and round one
end down, without looking at that arithmetic's mark «bad». A reader need not trust or read that
analysis: whatever number comes out is priced anew here, from both sides: too large a radius fails
at a list, a bracket or a count of bad points, too small a one at the rounds that draw positions.
Also called: `linSizeOf`, `reqGroups`, `keptOf`, `wordOf`, `clog2`, `sumT` (the planner's),
`Fmt.dsOf` (the draws of an entry), `Fmt.M2.rBatN` (the format's round «BAT»).

How to add a form of round: a `Slot` (its name, its draws, its work; its rows and its count, made of
the records' numbers, as functions of the entry) and its place in a list of slots; `rowsOk` holds a
list of entries against a list of slots, and Johnson/Bridge/PlanOkNatEq.lean has what a yes gives
(`rowsOk_below`, `rowsOk_shape`) [not in this library]. A NEW FORM IS A TEST BESIDE `planOk`, which
takes no new slot. THE
COMPARISON TAKES ANY COUNT: whoever writes a slot vouches that its count is the round's: a slot with
the count 0 passes at every entry of its form. What a slot takes off the entry it does not test. Two
empty lists pass; a name that the list of entries leaves out is not seen.

Limits. A YES IS FOR THE COUNTS, NOT FOR THE BLOCKS: that a block of a protocol is taken off at a
plan's own round is said by no theorem on this test. THE TEST IS SAFE TO ASK ONLY OF RECORDS AND
PLANS THAT THE ASKER HAS ITSELF MADE BY THE PLANNER FROM A FILE's PUBLIC FILES: that the records and
the plans come of one call of the planner is asked by no clause; nor how many plans a file has, nor
the parameter bytes (that the plans tested are the plans hashed). No theorem says that the test says
yes at any plan: it has been EVALUATED by a sheet that is not in this repository. That the radii and
lists off the records are those of a protocol's blocks is not said. BY READING, OR OPEN: that a
plan's own entry is the format's round, bytes and roots too (at stored plans it is not so where a
root rides in the message of a «FOLD epsilon»: there the theorems on the blocks taken off are idle;
the count is held all the same); which entry is which stage's, table's or record's (by order, over
all plans of the three files one after the other: in which plan an entry stands, and where among the
entries of other names, is not asked; name, draws, work and rows must fit); that the counts of
«LOC», «BAT» and «SEND seed» outside the code switches are a block's; which kind a description gives
a round (the theorems ask: seeds where a seed is drawn, else neither seeds nor sealed); the rows of
«BAT» (the entry's own, held against no record; below two the count is 0); how many «SEND seed»
stand outside the code switches, and any entry under another name; that the messages under a seed
are as many as the neighbour's answers, and which stage's list a message has; that no more requests
share a point than the records say; a group's slots (no test reads them; through the rows of «CS»
more than one is refused at a folded stage). THE BITS OF WORK COUNT AMONG THE 128 at «CS», «BASE»
and «LOC»; they are capped at 62 at every entry; `planOk` takes a test's bits off its own entry
«BASE»: THAT THEY ARE THE SETTING's IS A TEST BESIDE IT, `setWorkOk` (the nine tests; the first
chain's «LOC»; not the stored tables' «LOC»); what they are worth is proved nowhere here. THE COST:
the cap on the work stands first, and `slotOk` holds an entry's numbers before a power of them is
taken; but a stored table's «LOC» (its positions), a «SEND seed» outside the code switches (its
coordinates) and the records' own sizes reach a power before anything holds them: a number like 2^40
there is refused dearly or not in our time; how large the planner lets a file's public files make
these numbers nobody here has looked at. The text follows `planOkB`'s clause by clause, so some
things are asked twice. No sum over rounds.

-/
import OnBytes.Params.Configure
import Fmt.Rules6Draws
import Fmt.M2Plan

set_option autoImplicit false

namespace Johnson.Bridge.OkNat
open OnBytes OnBytes.Params

/-! ## 1. Numbers of a code and a stage -/

/-- The field of the challenges has q = p^3 elements, p = 2^64 - 2^32 + 1. -/
def q : Nat := (2 ^ 64 - 2 ^ 32 + 1) ^ 3

/-- The Johnson bound on a list: length n, distance d, radius e. It means something only below the
Johnson radius (`belowJohnson`); beyond it the divisor is 0 and so is the value. -/
def listMax (n d e : Nat) : Nat := n * (d - e) / ((n - e) ^ 2 - n * (n - d))

/-- The seeds at which one pair of a list can clash: a point of lg coordinates and a factor. -/
def clashSeeds (lg : Nat) : Nat := max (lg * q ^ (lg - 1) * (q - 1)) (q ^ lg)

/-- The length of a stage's rows. -/
def len (g : GroupSize) : Nat := 2 ^ g.main.logN

/-- The dimensions of the two codes: a message's entries and the random tail. -/
def dimMain (g : GroupSize) : Nat := g.main.r + g.main.ell
def dimMask (g : GroupSize) : Nat := g.mask.r + g.mask.ell

/-- How often the mask code is repeated to reach the main rows' length. -/
def copies (g : GroupSize) : Nat := 2 ^ (g.main.logN - g.mask.logN)

/-- The distances of a main row, of a repeated mask row, and of the stage: the smaller. -/
def distMain (g : GroupSize) : Nat := len g - dimMain g + 1
def distMask (g : GroupSize) : Nat := copies g * (2 ^ g.mask.logN - dimMask g + 1)
def dist (g : GroupSize) : Nat := min (distMain g) (distMask g)

/-- The bound on a list at the stage's distance. -/
def listAt (g : GroupSize) (e : Nat) : Nat := listMax (len g) (dist g) e

/-- The sizes are in order. -/
def sizesOk (g : GroupSize) : Bool :=
  decide (g.main.logN ≤ 32) && decide (g.mask.logN ≤ g.main.logN) && decide (dimMain g ≤ len g) &&
    decide (dimMask g ≤ 2 ^ g.mask.logN)

/-- The radius is below the distance and below the Johnson radius. -/
def belowJohnson (g : GroupSize) (e : Nat) : Bool :=
  decide (e < dist g) && decide (len g * (len g - dist g) < (len g - e) ^ 2)

/-- A stage and its radius: the sizes; the Johnson radius; each code's dimension at least two; the
radius above 0. -/
def stageGood (g : GroupSize) (e : Nat) : Bool :=
  sizesOk g && belowJohnson g e && decide (0 < dimMain g - 1) && decide (0 < dimMask g - 1) &&
    decide (0 < e)

/-! ## 2. The bracket of the count of bad points of a line

The count is a real number with a square root of the rate in it. A bracket holds m, two ends
a / 2^64 and b / 2^64 around that root, and a whole number N; ten comparisons show that the count is
at most N. -/

structure Bracket where
  m : Nat
  a : Nat
  b : Nat
  N : Nat

/-- The ten comparisons, at length n, dimension less one k, radius e. -/
def Bracket.ok (w : Bracket) (n k e : Nat) : Bool :=
  decide (0 < n) && (decide (0 < k) && (decide (0 < w.a) && (decide (0 < 2 ^ 64) &&
    (decide (w.a ^ 2 * n ≤ k * (2 ^ 64) ^ 2) && (decide (k * (2 ^ 64) ^ 2 ≤ w.b ^ 2 * n) &&
    (decide (w.b * n + e * 2 ^ 64 < 2 ^ 64 * n) &&
    (decide (w.b * n + w.m * (w.b * n + e * 2 ^ 64) ≤ w.m * (2 ^ 64 * n)) && (decide (3 ≤ w.m) &&
    decide (2 ^ 64 * ((2 * w.m + 1) ^ 5 * n ^ 2 + 24 * (2 * w.m + 1) * k * (e + 1)) ≤
      48 * k * w.a * w.N)))))))))

/-- The largest r, bit by bit from bit i - 1 down, with r^2 n ≤ K. -/
def rootDown (n K : Nat) : Nat → Nat → Nat
  | 0, r => r
  | i + 1, r =>
    bif Nat.ble ((r + 2 ^ i) * (r + 2 ^ i) * n) K then rootDown n K i (r + 2 ^ i)
    else rootDown n K i r

/-- The bracket with the ends a and b. -/
def bracketEnds (n k e a b : Nat) : Bracket :=
  let den := 2 ^ 64 * n - b * n - e * 2 ^ 64
  let m := max 3 ((b * n + den - 1) / den)
  ⟨m, a, b,
    (2 ^ 64 * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1)) + 48 * k * a - 1) /
      (48 * k * a)⟩

/-- The bracket whose lower end is a; the upper end is a, or a + 1 where the root is not whole. -/
def bracketUp (n k e a : Nat) : Bracket :=
  bracketEnds n k e a (bif Nat.ble (k * 2 ^ 128) (a * a * n) then a else a + 1)

/-- The bracket that is proposed; `Bracket.ok` tests it. -/
def bracketOf (n k e : Nat) : Bracket := bracketUp n k e (rootDown n (k * 2 ^ 128) 128 0)

/-- The brackets of a stage's two codes. -/
def mainBracket (g : GroupSize) (e : Nat) : Bracket := bracketOf (len g) (dimMain g - 1) e
def maskBracket (g : GroupSize) (e : Nat) : Bracket :=
  bracketOf (len g) (copies g * (dimMask g - 1)) e

/-! ## 3. The places -/

/-- A count c in a round that draws one element, without work: c / q ≤ 2^-128, with the sampler's
loss. -/
def oneElement (c : Nat) : Bool := decide (c * 2 ^ 193 + 3 * (1 + 0) * q ≤ q * 2 ^ (0 + 65))

/-- Bad points of a line: for a main row; for a table of mask rows. -/
def badMain (g : GroupSize) (e : Nat) : Nat := (mainBracket g e).N
def badMask (g : GroupSize) (e : Nat) : Nat :=
  (maskBracket g e).N + listMax (len g) (distMask g) e

/-- The count of a round of a fold: without mask rows; with them. -/
def foldPlain (g : GroupSize) (e : Nat) : Nat := badMain g e + listAt g e * 2
def foldMasked (g : GroupSize) (e : Nat) : Nat :=
  badMain g e + (badMask g e + badMask g e) + listAt g e * 2

/-- A stage that is folded: the stage and both brackets pass; the count of a round without mask rows
passes, and, where the stage has mask rows, the count of a round with them. -/
def foldOk (g : GroupSize) (e : Nat) : Bool :=
  (stageGood g e && (mainBracket g e).ok (len g) (dimMain g - 1) e &&
      (maskBracket g e).ok (len g) (copies g * (dimMask g - 1)) e) &&
    (oneElement (foldPlain g e) && (decide (g.h = 0) || oneElement (foldMasked g e)))

/-- The count of a base case's first round. -/
def baseFirst (g : GroupSize) (e : Nat) : Nat :=
  (mainBracket g e).N + ((maskBracket g e).N + listMax (len g) (distMask g) e) + listAt g e

/-- The lists of t positions at all of which a word at distance more than e agrees. -/
def missAll (g : GroupSize) (t e : Nat) : Nat := (len g - e - 1) ^ t

/-- A last stage: one row a table; its two rounds. -/
def lastOk (g : GroupSize) (t e work : Nat) : Bool :=
  (stageGood g e && decide (g.h = 0) && decide (g.k - g.h = 0) &&
      (mainBracket g e).ok (len g) (dimMain g - 1) e &&
      (maskBracket g e).ok (len g) (copies g * (dimMask g - 1)) e) &&
    (oneElement (baseFirst g e) &&
      decide (missAll g t e * 2 ^ 193 + 3 * (0 + 0) * len g ^ t ≤ len g ^ t * 2 ^ (work + 65)))

/-- The coordinates of the point of a stage's sample. -/
def sampleCoords (g : GroupSize) : Nat :=
  max (g.h + (g.k - g.h) + Nat.log2 g.main.ell) (g.h + Nat.log2 g.mask.ell) + 1

/-- The sizes of the stage that is left (g) and the stage that is entered (g') fit. -/
def switchFits (g g' : GroupSize) : Bool :=
  decide (2 ^ (g'.h + (g'.k - g'.h)) * g'.main.ell = g.main.ell ∧
    2 * g.mask.ell + g.main.r + 2 * g.mask.r + 1 ≤ 2 ^ g'.h * g'.mask.ell ∧
    g'.main.ell = 2 ^ Nat.log2 g'.main.ell ∧ g'.mask.ell = 2 ^ Nat.log2 g'.mask.ell ∧
    g.mask.logN ≤ g.main.logN)

/-- The counts of a code switch's two rounds: the seed; the positions with one element. -/
def switchSeed (g' : GroupSize) (e' : Nat) : Nat :=
  listAt g' e' * (listAt g' e' - 1) / 2 * clashSeeds (sampleCoords g')
def switchDraw (g : GroupSize) (t e : Nat) (g' : GroupSize) (e' : Nat) : Nat :=
  missAll g t e * q + len g ^ t * (listAt g' e' * (1 + 3 * t))

/-- A code switch: the sizes fit and are in order; the entered stage's radius is below the Johnson
radius; the counts of both rounds pass, the second with the bits of work; these are at most 62. -/
def switchOk (g : GroupSize) (t e : Nat) (g' : GroupSize) (e' work : Nat) : Bool :=
  (switchFits g g' && sizesOk g && sizesOk g' && belowJohnson g' e') &&
    (decide (switchSeed g' e' * 2 ^ 193 +
        3 * (sampleCoords g' + 1 + 1) * (q ^ sampleCoords g' * (q - 1)) ≤
        q ^ sampleCoords g' * (q - 1) * 2 ^ (0 + 65)) &&
      decide (switchDraw g t e g' e' * 2 ^ 193 + 3 * (1 + 0) * (len g ^ t * q) ≤
        len g ^ t * q * 2 ^ (work + 65)) &&
      decide (work + 66 ≤ 128))

/-! ## 4. One comparison for every round -/

/-- The number of values of a list of draws. -/
def countVals : List Fmt.Draw → Nat
  | [] => 1
  | .elem :: ds => q * countVals ds
  | .elemNZ :: ds => (q - 1) * countVals ds
  | .pos k :: ds => 2 ^ k * countVals ds
  | .trits n :: ds => 4 ^ n * countVals ds
  | .sealed :: ds => (2 ^ 64) ^ 4 * countVals ds

/-- All typed values of the challenge of a round with the entry e: of a round that draws seeds, or
of any other but a sealing. -/
def rowVals (e : Fmt.Entry) : Bool → Nat
  | true => countVals (Fmt.dsOf e .seeds)
  | false => countVals (Fmt.dsOf e .elems)

/-- THE COMPARISON: c bad challenges among all, at the entry's own draws and bits of work:
c / all ≤ 2^-128 · 2^work, with the sampler's loss. Beside it: positions of at most 64 bits; no more
elements other than 0 than elements; where an element is drawn, at most 62 bits of work; a challenge
has a value. -/
def rowOk (e : Fmt.Entry) (seed : Bool) (c : Nat) : Bool :=
  decide (e.logN ≤ 64) && decide (e.drawNZ ≤ e.drawE) &&
    (Nat.beq e.drawE 0 || decide (e.work + 66 ≤ 128)) && decide (0 < rowVals e seed) &&
    decide (c * 2 ^ 193 + 3 * (e.drawE + e.drawNZ) * rowVals e seed ≤
      rowVals e seed * 2 ^ (e.work + 65))

/-! ## 5. Slots: what a plan's own entry is held against -/

/-- A name, whether a seed is drawn, what is drawn (elements, of them other than 0, positions, the
length's logarithm, matrix entries), the bits of work, the rows that are batched, and the count that
is held against all challenges (at «BAT» the rows are the entry's own, and the count depends on
them). -/
structure Slot where
  name : String
  seed : Bool
  drawE : Nat
  drawNZ : Nat
  poss : Nat
  logN : Nat
  trits : Nat
  work : Nat
  rows : Fmt.Entry → Nat
  cnt : Fmt.Entry → Nat

/-- The entry has the slot's name, draws (matrix entries among them), work and rows, stands for one
round, and passes the comparison. The equalities stand in front: where one fails the comparison is
not evaluated. -/
def slotOk (e : Fmt.Entry) (x : Slot) : Bool :=
  (e.name == x.name) && Nat.beq e.drawE x.drawE && Nat.beq e.drawNZ x.drawNZ &&
    Nat.beq e.poss x.poss && Nat.beq e.logN x.logN && Nat.beq e.work x.work &&
    Nat.beq e.trits x.trits && Nat.beq e.count 1 && Nat.beq e.rows (x.rows e) &&
    rowOk e x.seed (x.cnt e)

/-- A list of entries against a list of slots: as many of the one as of the other, and each entry
passes at its slot. -/
def rowsOk (es : List Fmt.Entry) (xs : List Slot) : Bool :=
  Nat.beq es.length xs.length && ((es.zip xs).all fun p => slotOk p.1 p.2)

/-- A stage with its radius: ((group, positions), radius). -/
abbrev StageAt : Type := (GroupSize × Nat) × Nat

/-- A round that draws one element and nothing else. -/
def oneSlot (name : String) (c : Nat) : Slot :=
  ⟨name, false, 1, 0, 0, 0, 0, 0, fun _ => 0, fun _ => c⟩

/-- The batching in front of a stage's fold: one element; the count: the stage's list times the
entry's rows less one. -/
def batSlot (x : StageAt) : Slot :=
  ⟨"BAT", false, 1, 0, 0, 0, 0, 0, fun y => y.rows, fun y => listAt x.1.1 x.2 * (y.rows - 1)⟩

/-- A fold: its first round, then one round for each row variable; mask rows in the first h. -/
def foldSlots (x : StageAt) : List Slot :=
  oneSlot "FOLD epsilon" (listAt x.1.1 x.2) ::
    (List.range (x.1.1.h + (x.1.1.k - x.1.1.h))).map fun i =>
      oneSlot "FOLD round"
        (if i + 1 ≤ x.1.1.h then foldMasked x.1.1 x.2 else foldPlain x.1.1 x.2)

/-- A code switch from x to y: the seed of y's sample; x's positions and one element. -/
def switchSlots (x y : StageAt) (work : Nat) : List Slot :=
  [⟨"SEND seed", true, sampleCoords y.1.1 + 1, 1, 0, 0, 0, 0, fun _ => 0,
      fun _ => switchSeed y.1.1 y.2⟩,
    ⟨"CS", false, 1, 0, x.1.2, x.1.1.main.logN, 0, work, fun _ => 3 * x.1.2 + 2,
      fun _ => switchDraw x.1.1 x.1.2 x.2 y.1.1 y.2⟩]

/-- A base case: one element; the positions. -/
def lastSlots (x : StageAt) (work : Nat) : List Slot :=
  [oneSlot "BASE lambda" (baseFirst x.1.1 x.2),
    ⟨"BASE", false, 0, 0, x.1.2, x.1.1.main.logN, 0, work, fun _ => 0,
      fun _ => missAll x.1.1 x.1.2 x.2⟩]

/-! ## 6. The records -/

/-- A proximity test: the stages that are folded, the last stage, the bits of work of its rounds of
positions. -/
structure Test where
  folds : List StageAt
  last : StageAt
  work : Nat

/-- All stages of a test. -/
def Test.stages (T : Test) : List StageAt := T.folds ++ [T.last]

/-- Each stage with the next. -/
def pairsOf : List StageAt → List (StageAt × StageAt)
  | x :: y :: r => (x, y) :: pairsOf (y :: r)
  | _ => []

/-- Every fold, every code switch and the base case of a test pass. -/
def Test.ok (T : Test) : Bool :=
  (T.folds.all fun x => foldOk x.1.1 x.2) &&
    ((pairsOf T.stages).all fun p =>
      switchOk p.1.1.1 p.1.1.2 p.1.2 p.2.1.1 p.2.2 T.work) &&
    lastOk T.last.1.1 T.last.1.2 T.last.2 T.work

/-- The slots of a test: the batching; fold and code switch, stage by stage; the base case. -/
def Test.slots (T : Test) : List Slot :=
  (T.stages.head?.toList.map batSlot) ++
    ((T.folds.zip (pairsOf T.stages)).flatMap fun p =>
      foldSlots p.1 ++ switchSlots p.2.1 p.2.2 T.work) ++
    lastSlots T.last T.work

/-- The planner's radius of a group: the upper end of the main code's distance, as `analysisOfM` has
it, times the length, rounded down. -/
def radius (s : Setting) (g : GroupSize) : Nat :=
  ((analysisOfM s g).mainAt.delta * Bound.ofNat (wordOf g.main).n).hi.floor

/-- A planner's stages, each with its radius. -/
def stagesAt (s : Setting) (st : List StageSize) : List StageAt :=
  st.map fun y => ((y.g, y.t), radius s y.g)

/-- The test of a planner's list of stages; none where the list is empty. -/
def testOf (s : Setting) (st : List StageSize) (work : Nat) : List Test :=
  (stagesAt s st).getLast?.toList.map fun l => ⟨(stagesAt s st).dropLast, l, work⟩

/-- The nine tests' lists of stages: four of a proof file, four of a key file, one of an entry
file. -/
def proofTests (Z : Params.Sized) : List (List StageSize) :=
  [Z.proof.last.stages, Z.proof.batch.folded.stages, Z.proof.batch.omega.stages,
    Z.proof.batch.own.stages]
def keyTests (Z : Params.Sized) : List (List StageSize) :=
  [Z.key.ranges.test.stages, Z.key.once.folded.stages, Z.key.once.omega.stages,
    Z.key.once.own.stages]
def nineTests (Z : Params.Sized) : List (Setting × List StageSize) :=
  (proofTests Z).map (fun st => (Z.proof.set, st)) ++
    (keyTests Z).map (fun st => (Z.key.set, st)) ++ [(Z.set, Z.link.linked.stages)]

/-- All plans: a proof file's, a key file's, an entry file's. -/
def plans (M : Configured) : List Planned := M.proof ++ M.key ++ [M.entry]

/-- The bits of work of the plans' entries «BASE», in the plans' order. -/
def baseWorks (M : Configured) : List Nat :=
  (plans M).flatMap fun P => (P.plan.entries.filter fun e => e.name == "BASE").map (·.work)

/-- The tests: one for each of the nine lists of stages that is not empty and has an entry «BASE»
(`testsOk` asks that they are nine). -/
def planTests (M : Configured) : List Test :=
  ((nineTests M.sized).zipWith (fun x w => testOf x.1 x.2 w) (baseWorks M)).flatten

/-- The group of a link as it is closed. -/
def closedGroup (z : ProofSized) (g : ReqGroup) (gs : List ReqGroup) : GroupSize :=
  { z.link.group with
    k := g.k, h := g.h,
    slots := 2 ^ clog2 (1 + sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))) }

/-- The closed groups of a request's links, one for each link that has a group. -/
def closedFrom (z : ProofSized) : List ReqGroup → List ReqLink → List GroupSize
  | [], _ => []
  | g :: gs, links =>
    match links.head? with
    | none => []
    | some _ => closedGroup z g gs :: closedFrom z gs (links.drop 1)

/-- The same of a proof file's request. -/
def closedGroups (z : ProofSized) : List GroupSize :=
  closedFrom z (reqGroups z.request).toList z.request.link

/-- The groups that are opened by a round «LOC» of the first chain: behind each closed group that
has a group behind it. -/
def openedFrom (z : ProofSized) : List ReqGroup → List ReqLink → List GroupSize
  | [], _ => []
  | g :: gs, links =>
    match links.head? with
    | none => []
    | some _ => (if gs.isEmpty then [] else [closedGroup z g gs]) ++ openedFrom z gs (links.drop 1)

/-- The same of a proof file's request. -/
def openedGroups (z : ProofSized) : List GroupSize :=
  openedFrom z (reqGroups z.request).toList z.request.link

/-- The closings of the links' groups, as stages with their radii. -/
def linkFolds (z : ProofSized) : List StageAt :=
  (closedGroups z).map fun g => ((g, z.link.t), radius z.set g)

/-- All stages of the records. -/
def allStages (M : Configured) : List StageAt :=
  (planTests M).flatMap Test.stages ++ linkFolds M.sized.proof

/-! ## 7. The tests -/

/-- The last stages of the nine tests. -/
def lastStages (Z : Params.Sized) : List StageSize :=
  (proofTests Z).flatMap (fun st => st.getLast?.toList) ++
    (keyTests Z).flatMap (fun st => st.getLast?.toList) ++ Z.link.linked.stages.getLast?.toList

/-- Every test has a stage; as many entries «BASE» as tests; as many closed groups as links. -/
def wholeOk (M : Configured) : Bool :=
  ((keyTests M.sized ++ proofTests M.sized ++ [M.sized.link.linked.stages]).all fun st =>
      !st.isEmpty) &&
    Nat.beq (baseWorks M).length (lastStages M.sized).length &&
    Nat.beq (closedGroups M.sized.proof).length M.sized.proof.request.link.length

/-- THE NINE TESTS AND THE LINKS' FOLDS, off the records. -/
def testsOk (M : Configured) : Bool :=
  wholeOk M && Nat.beq (planTests M).length (nineTests M.sized).length &&
    ((planTests M).all fun T => T.ok) && ((linkFolds M.sized.proof).all fun x => foldOk x.1.1 x.2)

/-- The entries «LOC» of a plan. -/
def locsOf (P : Planned) : List Fmt.Entry := P.plan.entries.filter fun e => e.name == "LOC"

/-- A round that draws positions alone, at the radius r: the lists of positions at all of which a
word at distance more than r agrees, against all lists, with the entry's bits of work. -/
def locOk (e : Fmt.Entry) (r : Nat) : Bool :=
  Nat.beq e.drawE 0 && Nat.beq e.drawNZ 0 && Nat.beq e.trits 0 &&
    (decide ((2 ^ e.logN - r - 1) ^ e.poss * 2 ^ 193 + 3 * (0 + 0) * (2 ^ e.logN) ^ e.poss ≤
        (2 ^ e.logN) ^ e.poss * 2 ^ (e.work + 65)) &&
      decide (e.logN ≤ 64))

/-- The first chain's entries «LOC», each with the group that it opens. -/
def linkLocs (M : Configured) : List (Fmt.Entry × GroupSize) :=
  ((M.proof.take 1).flatMap locsOf).zip (openedGroups M.sized.proof)

/-- The other plans' entries «LOC»: taken to be the stored tables' (`tablesOk` asks that they are
two, each of its table's length). -/
def tableLocs (M : Configured) : List Fmt.Entry :=
  (M.proof.drop 1 ++ M.key ++ [M.entry]).flatMap locsOf

/-- Every entry «LOC» with its radius; rT: the stored tables'. -/
def planLocs (rT : Nat) (M : Configured) : List (Fmt.Entry × Nat) :=
  (linkLocs M).map (fun p => (p.1, radius M.sized.proof.set p.2)) ++
    (tableLocs M).map fun e => (e, rT)

/-- THE ROUNDS «LOC»: as many in the first chain's plan as groups are opened, each of its group's
length and the links' number of positions; and every «LOC» passes at its radius. -/
def locsOk (rT : Nat) (M : Configured) : Bool :=
  Nat.beq ((M.proof.take 1).flatMap locsOf).length (openedGroups M.sized.proof).length &&
    ((linkLocs M).all fun p =>
      Nat.beq p.1.logN p.2.main.logN && Nat.beq p.1.poss M.sized.proof.link.t) &&
    ((planLocs rT M).all fun p => locOk p.1 p.2)

/-- A stored table's code and two radii: sizes in order; 0 < e ≤ eM below the distance; e below the
Johnson radius. -/
def tableOk (T : TableSize) (e eM : Nat) : Bool :=
  decide (T.code.logN ≤ 32) && decide (0 < T.code.r + T.code.ell - 1) &&
    decide (T.code.r + T.code.ell ≤ 2 ^ T.code.logN) && decide (0 < e) && decide (e ≤ eM) &&
    decide (eM < 2 ^ T.code.logN - (T.code.r + T.code.ell) + 1) &&
    decide (2 ^ T.code.logN * (2 ^ T.code.logN - (2 ^ T.code.logN - (T.code.r + T.code.ell) + 1)) <
      (2 ^ T.code.logN - e) ^ 2)

/-- The two stored tables: the proof file's, the key file's. -/
def planTables (Z : Params.Sized) : List TableSize := [Z.proof.batch.table, Z.key.once.table]

/-- THE STORED TABLES: two entries «LOC», each of its table's length; the radius. -/
def tablesOk (rT : Nat) (M : Configured) : Bool :=
  Nat.beq (tableLocs M).length (planTables M.sized).length &&
    (((tableLocs M).zip (planTables M.sized)).all fun p => Nat.beq p.1.logN p.2.code.logN) &&
    ((planTables M.sized).all fun T => tableOk T rT rT)

/-- The shared point of the test on a stored table: the table, the radius, the number of column
variables, the number of requests. -/
structure Point where
  T : TableSize
  e : Nat
  klo : Nat
  N : Nat

namespace Point
variable (x : Point)

/-- The code's length. -/
def n : Nat := 2 ^ x.T.code.logN

/-- The code's dimension less one. -/
def k : Nat := x.T.code.r + x.T.code.ell - 1

/-- The bracket that is proposed at the code and the radius. -/
def bracket : Bracket := bracketOf x.n x.k x.e

/-- A bound on the fold points that are bad for one table: the same for every table without a
collision at the record's seed. -/
def top : Nat :=
  x.T.v * x.bracket.N * q ^ (x.T.v - 1) + listMax x.n (x.n - x.k) x.e * (x.T.v * q ^ (x.T.v - 1))

/-- The count of the round: that bound at every choice of the column variables, and a field term for
each of N requests. -/
def cnt : Nat := x.top * q ^ x.klo + x.N * ((x.T.v + x.klo) * q ^ (x.T.v + x.klo - 1))

/-- All points. -/
def all : Nat := q ^ (x.T.v + x.klo)

/-- The table's code and the radius are in order, and the bracket passes. -/
def good : Bool := tableOk x.T x.e x.e && x.bracket.ok x.n x.k x.e

/-- The count against all points, without work. -/
def priced : Bool :=
  decide (x.cnt * 2 ^ 193 + 3 * (x.T.v + x.klo + 0) * x.all ≤ x.all * 2 ^ (0 + 65))

end Point

/-- The records of the two tests on a stored table. -/
def planLins (Z : Params.Sized) : List (TableSize × Option LinSize) :=
  [(Z.proof.batch.table, linSizeOf Z.proof.codes Z.proof.batch),
    (Z.key.once.table, linSizeOf Z.key.codes Z.key.once)]

/-- The plans' entries «LIN point». -/
def pointEntries (M : Configured) : List Fmt.Entry :=
  (plans M).flatMap fun P => P.plan.entries.filter fun e => e.name == "LIN point"

/-- Each entry «LIN point» with the point of its number: the proof file's first. -/
def planPoints (rT : Nat) (M : Configured) : List (Fmt.Entry × Point) :=
  (pointEntries M).zipWith
    (fun e p => (e, ⟨p.1, rT, (p.2.map (·.kLo)).getD 0, (p.2.map (·.instances)).getD 0⟩))
    (planLins M.sized)

/-- The entry draws one element for each coordinate of the point and nothing else, without work;
there is a request; the point's two tests pass. -/
def pointOk (e : Fmt.Entry) (x : Point) : Bool :=
  decide (e.logN ≤ 64) && Nat.beq e.poss 0 && Nat.beq e.drawE (x.T.v + x.klo) &&
    Nat.beq e.drawNZ 0 && Nat.beq e.trits 0 && Nat.beq e.work 0 && decide (1 ≤ x.N) && x.good &&
    x.priced

/-- THE ROUNDS «LIN point»: two entries; both records' sizes follow; each entry passes at its
point. -/
def pointsOk (rT : Nat) (M : Configured) : Bool :=
  Nat.beq (pointEntries M).length (planLins M.sized).length &&
    ((planLins M.sized).all fun p => p.2.isSome) &&
    ((planPoints rT M).all fun p => pointOk p.1 p.2)

/-- Each entry of a plan with the entry behind it; behind the last: an entry without a name. (This
and the three definitions that use it have no recursion of their own: a plan has tens of thousands
of entries.) -/
def withNext (es : List Fmt.Entry) : List (Fmt.Entry × Fmt.Entry) :=
  es.zip (es.drop 1 ++ [{ name := "" }])

/-- Each entry «SEND seed» that does not stand in front of «CS», with the entry behind it. -/
def seedsIn (es : List Fmt.Entry) : List (Fmt.Entry × Fmt.Entry) :=
  (withNext es).filter fun p => p.1.name == "SEND seed" && p.2.name != "CS"

/-- A seed for the samples of several messages, TAKEN TO BE as many as the entry behind has answers;
lists of at most L; the point's coordinates are the entry's own. A coarse count: each message, each
pair of its list. -/
def seedOk (e e' : Fmt.Entry) (L : Nat) : Bool :=
  Nat.beq e.poss 0 && decide (e.logN ≤ 64) && decide (1 ≤ e.drawE) && Nat.beq e.drawNZ 1 &&
    Nat.beq e.trits 0 && Nat.beq e.work 0 && decide (1 ≤ e'.answers) &&
    decide (e'.answers * (L * (L - 1) / 2 * clashSeeds (e.drawE - 1)) * 2 ^ 193 +
        3 * (e.drawE - 1 + 1 + 1) * (q ^ (e.drawE - 1) * (q - 1)) ≤
      q ^ (e.drawE - 1) * (q - 1) * 2 ^ (0 + 65))

/-- All such pairs of the plans. -/
def planSeeds (M : Configured) : List (Fmt.Entry × Fmt.Entry) :=
  (plans M).flatMap fun P => seedsIn P.plan.entries

/-- Each of them passes. -/
def seedsOk (L : Nat) (M : Configured) : Bool := (planSeeds M).all fun p => seedOk p.1 p.2 L

/-- Every stage's radius is below the Johnson radius, and its list at most L. -/
def listsOk (L : Nat) (M : Configured) : Bool :=
  (allStages M).all fun x => belowJohnson x.1.1 x.2 && decide (listAt x.1.1 x.2 ≤ L)

/-- How many entries «SEND seed» stand in front of an entry «CS». -/
def seedsAtSwitch (es : List Fmt.Entry) : Nat :=
  ((withNext es).filter fun p => p.1.name == "SEND seed" && p.2.name == "CS").length

/-- The same in all plans. -/
def switchSeeds (M : Configured) : Nat :=
  ((plans M).map fun P => seedsAtSwitch P.plan.entries).sum

/-- THE ROUNDS «SEND seed» OUTSIDE THE CODE SWITCHES: the nine tests; the lists; the seeds; and as
many «SEND seed» stand in front of «CS» as the tests have code switches. -/
def sendsOk (L : Nat) (M : Configured) : Bool :=
  testsOk M && listsOk L M && seedsOk L M &&
    Nat.beq (switchSeeds M) ((planTests M).flatMap fun T => pairsOf T.stages).length

/-- The plans' entries «BAT». -/
def batEntries (M : Configured) : List Fmt.Entry :=
  (plans M).flatMap fun P => P.plan.entries.filter fun e => e.name == "BAT"

/-- The stages in front of whose folds rows are batched. -/
def batStages (M : Configured) : List StageAt :=
  linkFolds M.sized.proof ++ (nineTests M.sized).flatMap fun x => (stagesAt x.1 x.2).take 1

/-- Each entry «BAT» with the stage of its number. -/
def planBats (M : Configured) : List (Fmt.Entry × StageAt) :=
  (batEntries M).zipWith (fun e x => (e, x)) (batStages M)

/-- THE ROUNDS «BAT»: as many entries as stages; each is the format's own round at its own rows; its
stage's sizes and radius are in order; the list times the rows less one passes. -/
def batsOk (M : Configured) : Bool :=
  Nat.beq (batEntries M).length (batStages M).length &&
    ((planBats M).all fun p =>
      decide (p.1 = (Fmt.M2.rBatN p.1.rows).entry) &&
        (sizesOk p.2.1.1 && belowJohnson p.2.1.1 p.2.2) &&
        oneElement (listAt p.2.1.1 p.2.2 * (p.1.rows - 1)))

/-- How many entries of the plans have that name. -/
def countOf (M : Configured) (name : String) : Nat :=
  ((plans M).map fun P => (P.plan.entries.filter fun e => e.name == name).length).sum

/-- The groups that are folded. -/
def foldGroups (Z : Params.Sized) : List GroupSize :=
  ((nineTests Z).flatMap fun x => x.2.dropLast.map (·.g)) ++ closedGroups Z.proof

/-- A CENSUS OF NAMES. -/
def censusOk (M : Configured) : Bool :=
  Nat.beq (countOf M "FOLD epsilon") (foldGroups M.sized).length &&
    Nat.beq (countOf M "FOLD round") ((foldGroups M.sized).map (·.k)).sum &&
    Nat.beq (countOf M "CS") ((nineTests M.sized).map fun x => x.2.length - 1).sum &&
    Nat.beq (countOf M "BASE lambda") (nineTests M.sized).length &&
    Nat.beq (countOf M "BASE") (nineTests M.sized).length

/-- The closing of a link's group: its batching and its fold. -/
def linkSlots (x : StageAt) : List Slot := batSlot x :: foldSlots x

/-- All slots: the closings of the proof file's links, then the nine tests. -/
def planSlots (M : Configured) : List Slot :=
  (linkFolds M.sized.proof).flatMap linkSlots ++ (planTests M).flatMap Test.slots

/-- The six names. -/
def testNames : List String := ["BAT", "FOLD epsilon", "FOLD round", "CS", "BASE lambda", "BASE"]

/-- The entries of the six names, and each «SEND seed» in front of a «CS». -/
def testEntries (es : List Fmt.Entry) : List Fmt.Entry :=
  ((withNext es).filter fun p =>
    testNames.contains p.1.name || (p.1.name == "SEND seed" && p.2.name == "CS")).map (·.1)

/-- The same of all plans, in the plans' order. -/
def planTestEntries (M : Configured) : List Fmt.Entry :=
  (plans M).flatMap fun P => testEntries P.plan.entries

/-- THE TESTS' ROUNDS, READ OFF THE PLANS' OWN ENTRIES. -/
def roundsOk (M : Configured) : Bool := rowsOk (planTestEntries M) (planSlots M)

/-- Every entry of every plan has at most 62 bits of work and stands for one round. -/
def workOk (M : Configured) : Bool :=
  (plans M).all fun P =>
    P.plan.entries.all fun e => decide (e.work + 66 ≤ 128) && Nat.beq e.count 1

/-- The scope with which the planner makes a shared chain, and a second chain (`sharedPlan`,
`secondPlan`, OnBytes/Params/DeriveLin.lean). -/
def sharedScope (x : LinSized) : Scope := if x.lines.oneTime then .once else .shared
def secondScope (x : LinSized) : Scope := if x.lines.oneTime then .once else .request

/-- The setting's bits of work for a round that draws positions, test by test, in the order of
`nineTests`, each at the setting and the scope with which the planner makes its chain
(`configure`, OnBytes/Params/Configure.lean). A proof file, at the proof's setting: the last test
of the links stands in the first chain (a request's own scope), the tests on the folded row and on
Omega in the shared chain, the test on its own rows in the second chain. A key file: the first chain
at the key's setting, made once; the shared and the second chain at the records' own setting. An
entry file's chain: at the records' own setting, made once. -/
def testWorks (Z : Params.Sized) : List Nat :=
  [Z.proof.set.workOf .query .request, Z.proof.set.workOf .query (sharedScope Z.proof.batch),
    Z.proof.set.workOf .query (sharedScope Z.proof.batch),
    Z.proof.set.workOf .query (secondScope Z.proof.batch), Z.key.set.workOf .query .once,
    Z.set.workOf .query (sharedScope Z.key.once), Z.set.workOf .query (sharedScope Z.key.once),
    Z.set.workOf .query (secondScope Z.key.once), Z.set.workOf .query .once]

/-- THE BITS OF WORK ARE THE SETTING's: at the nine entries «BASE» (and so, by `roundsOk`, at every
«CS» of their tests), and at the first chain's entries «LOC». A TEST BESIDE `planOk`. -/
def setWorkOk (M : Configured) : Bool :=
  decide (baseWorks M = testWorks M.sized) &&
    ((linkLocs M).all fun p => Nat.beq p.1.work (M.sized.proof.set.workOf .query .request))

/-! ## 8. The whole -/

/-- All tests, at the stored tables' radius rT and the bound L on the lists. The cap on the work
stands first: no power of an entry's work is taken before it has passed. -/
def allOk (rT L : Nat) (M : Configured) : Bool :=
  workOk M && (testsOk M && locsOk rT M && tablesOk rT M) && pointsOk rT M && sendsOk L M &&
    batsOk M && censusOk M && roundsOk M

/-- The distance at which a stored table is read: the one-time test's, or the later tests'. -/
def readAt (s : Setting) (T : TableSize) (y : LinSize) : Proximity :=
  if y.oneTime then (tableAnalysis s T).once else (tableAnalysis s T).later

/-- The planner's own radius of a stored table: the lower end of the distance at which the table is
read, times the length, rounded down; 0 where the sizes do not follow. -/
def tableRadOf (s : Setting) (T : TableSize) (x : Option LinSize) : Nat :=
  (x.map fun y => ((readAt s T y).delta * Bound.ofNat (wordOf T.code).n).lo.floor).getD 0

/-- The two stored tables' radii: the proof file's, the key file's. -/
def tableRads (Z : Params.Sized) : List Nat :=
  [tableRadOf Z.proof.set Z.proof.batch.table (linSizeOf Z.proof.codes Z.proof.batch),
    tableRadOf Z.key.set Z.key.once.table (linSizeOf Z.key.codes Z.key.once)]

/-- The first of them. -/
def tableRad (M : Configured) : Nat := (tableRads M.sized).headD 0

/-- The largest bound on a list among the records' stages. -/
def listTop (M : Configured) : Nat := ((allStages M).map fun x => listAt x.1.1 x.2).foldl max 0

/-- **THE TEST**: the two stored tables' radii agree, and all tests pass at that radius and the
largest list. ASK `setWorkOk` BESIDE IT: alone it takes a test's bits of work off the plan's own
entry «BASE», and passes any number of them up to 62. -/
def planOk (M : Configured) : Bool :=
  ((tableRads M.sized).all fun r => Nat.beq r (tableRad M)) && allOk (tableRad M) (listTop M) M

end Johnson.Bridge.OkNat

#print axioms Johnson.Bridge.OkNat.planOk
