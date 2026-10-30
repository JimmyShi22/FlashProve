-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Group.lean: the sizing of a group of rows, of the stages of a proximity test and of
the committed table's distances.

A group is a number of main rows under one code and of mask rows under a mask code, read at one
list of positions, with one joint distance. A row gets as many random entries as there are
positions at which it is opened. These entries raise the code's rate, and the rate fixes the number
of positions. So each group is solved by iteration from below.

The file renders what blocks/numbers/blocks.h says of groups, stages and the table, and the
routine solve_group of blocks/frame/derive.h, formula for formula. Where the C++ notes a refusal
and goes on, the functions here return nothing, and the caller refuses the public files.

Main definitions: `GroupSize`, `Analysis`, `analysis`, `groupHolds`, `sizeGroup`, `solveGroup`,
`StageSize`, `solveStages`, `TableSize`, `tableAnalysis`, `tableAdmitted`, `sizeRecordedTable`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Params.Distance

namespace OnBytes.Params

/-- The least a with n ≤ 2 ^ a. -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-! ## Groups -/

/-- A group: 2 ^ k main rows under one code (rows that nobody sent are zero and are counted) and
2 ^ h mask rows under the mask code, read at one list of positions (a mask row at the position
modulo its length), with one joint distance. `rule` and `m` are the two choices of the analysis:
what `analysis` says of the group follows from the fields of this structure and the setting. -/
structure GroupSize where
  main : CodeSize := {}
  /-- `mask.ell` = 0: the group has no mask rows -/
  mask : CodeSize := {}
  k : Nat := 0
  h : Nat := 0
  /-- every main row stands for so many rows that are folded side by side -/
  slots : Nat := 1
  /-- the rule that fixes the distance -/
  rule : Radius := .johnson
  /-- under the rule `johnson`: the assumed theorem's integer m (`johnson`) for the code with the
  larger rate. Under the rule `named`: the distance, in positions of the main code's length. Under
  the two other rules it is not read -/
  m : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- True if the group has mask rows. -/
def GroupSize.hasMask (g : GroupSize) : Bool := g.mask.ell != 0

/-- What the analysis says of a group. -/
structure Analysis where
  /-- the main code at the group's distance -/
  mainAt : Proximity := {}
  /-- the mask code at the same distance -/
  maskAt : Proximity := {}
  /-- the list size of main and mask rows together: the larger of the two codes' bounds -/
  list : Nat := 1
  /-- the group breaks a rule of shapes (`shapeFault`); `mainAt.count` is then bad -/
  fault : Bool := false
  withMask : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- True if the main code's `Proximity` is bad or, of a group with mask rows, the mask code's. -/
def Analysis.bad (a : Analysis) : Bool := a.mainAt.bad || (a.withMask && a.maskAt.bad)

/-- True if the mask code has the larger rate. The code with the larger rate fixes the distance: one
distance serves main and mask rows, and it must lie inside the range of the bounds for both codes.
At the late stages of a proximity test the mask rows can be the longer messages. -/
def maskRules (g : GroupSize) : Bool :=
  g.hasMask && decide (g.main.k * g.mask.n < g.mask.k * g.main.n)

/-- True if the group has a shape that the statements of the protocol's blocks exclude: mask rows
without a mask code; a mask code longer than the main code; more row variables for mask rows than
for main rows (mask rows are folded by the first of the row variables); or a single mask row beside
folded rows (h = 0 < k) under a code of a larger rate than theirs. Such a mask row has no closeness
term in any round of the fold, so only the list size would keep the distance below the mask code's
Johnson radius. -/
def shapeFault (g : GroupSize) : Bool :=
  if !g.hasMask then g.h != 0
  else decide (g.main.logN < g.mask.logN) || decide (g.k < g.h) ||
    (decide (0 < g.k) && g.h == 0 && maskRules g)

/-- What the analysis says of a group at the main code's `Proximity` x. A shape fault makes the main
count bad.

The mask rows' symbols are copies in the main rows' leaves, and no test forces the copies to agree.
So the mask code is read as its repetition to the main code's length n (`repeated`). Within a third
of the distance the count is the lemma's (`CountSource.third`), which holds for any linear code.
Beyond it the count is the assumed theorem's at the length n and the mask code's own rate, and one
list size more. The footing (blocks/numbers/blocks.h, analysis_at): counts and list sizes depend on
the code as a set of words only, and under some numbering of the n positions the repeated words are
a part of a Reed-Solomon code of that rate; the list size pays for the step to a part of a code. It
is added also where the two lengths are equal.

Not claimed: that under the format's copy map and the main code's own numbering a repeated word lies
in a Reed-Solomon code on the main domain. It does not. What the count asks of the format: one
public copy map under which every short position has equally many copies; a coset as the short
code's domain; n dividing p - 1; a distance below the mask code's own Johnson radius; mask symbols
combined and compared with mask symbols only. Of these only the distance is tested in this file.

The group's list size is the larger of the two codes' bounds. -/
def analysisAt (s : Setting) (g : GroupSize) (x : Proximity) : Analysis :=
  let fault := shapeFault g
  let x' : Proximity := if fault then { x with count := Bound.failed } else x
  if g.hasMask then
    let z := atDistance s (repeated g.mask g.main.logN) x.agree
    let z' : Proximity :=
      if z.source != .third then { z with count := z.count + Bound.ofNat z.list } else z
    { mainAt := x', maskAt := z', list := max x.list z.list, fault := fault, withMask := true }
  else { mainAt := x', list := x.list, fault := fault, withMask := false }

/-- The error of round j = 1 .. k of a fold (the block FOLD: a sumcheck over the row variables of a
group). The mask code's term counts twice in each round j up to h. -/
def foldRoundError (s : Setting) (g : GroupSize) (a : Analysis) (j : Nat) : Bound :=
  let e := mcaError s a.mainAt (2 ^ (g.k - j) * g.slots) + Bound.ofNat a.list * fieldError s 2
  if g.hasMask && decide (j ≤ g.h) then e + Bound.ofWord 2 * mcaError s a.maskAt (2 ^ (g.h - j))
  else e

/-- The error of the first round of the last step of a proximity test (the block BASE), for a group
of single rows. The mask code's term counts once. -/
def baseError (s : Setting) (g : GroupSize) (a : Analysis) : Bound :=
  let e := mcaError s a.mainAt g.slots + Bound.ofNat a.list * fieldError s 1
  if g.hasMask then e + mcaError s a.maskAt 1 else e

/-- What else the rounds that depend on a group's distance must carry, as whoever sizes the group
declares it. A plan that asks more of the group than was declared is not thereby admitted: the
plan's verdict (`Planned.holds`) compares every round that is really planned. -/
structure GroupLoad where
  /-- the largest cube of a sample on one of its oracle messages -/
  cubeBits : Nat := 40
  /-- how many of its oracle messages at most share one seed -/
  messages : Nat := 4
  /-- the largest number of rows that are batched on it -/
  batchedRows : Nat := 2 ^ 20
  deriving DecidableEq, Repr, Inhabited

/-- What a round's error may be, by its kind and scope. -/
def goalOf (s : Setting) (why : ErrorKind) (scope : Scope) : Binary :=
  let g := Binary.twoTo ((s.workOf why scope : Int) - (s.target : Int))
  if scope == .request then g.div (.ofNat s.instances) .down else g

/-- The analysis under the Johnson rule with the group's integer m. -/
def analysisOfM (s : Setting) (g : GroupSize) : Analysis :=
  if !maskRules g then analysisAt s g (johnson (wordOf g.main) g.m s.printed)
  else
    let z := johnson (repeated g.mask g.main.logN) g.m s.printed
    let a := analysisAt s g (atDistance s (wordOf g.main) z.agree)
    { a with maskAt := { z with count := z.count + Bound.ofNat z.list } }

/-- What the analysis says of a group, by the group's rule. The rule and m are choices: each gives
bounds for these codes, or a bad analysis. Whether the rounds then reach the target is for the
plan's verdict to say (`Planned.holds`). -/
def analysis (s : Setting) (g : GroupSize) : Analysis :=
  match g.rule with
  | .johnson => analysisOfM s g
  | .named =>
    analysisAt s g (atDistance s (wordOf g.main) (Bound.ofWord 1 - Bound.ratio g.m g.main.n))

/-- True if the analysis is not bad and three errors that depend on the distance are within their
goals: the closeness error of the fold's first round, which is no smaller than that of its other
rounds (of a group of single rows: of the last step's first round); the sample error at the declared
load; and the field error of a batching of the declared number of rows, with the fold's first
challenge. The draws of positions are not among them. What a plan asks beyond the declared load is
not seen here (`GroupLoad`). -/
def groupHolds (s : Setting) (scope : Scope) (g : GroupSize) (load : GroupLoad) : Bool :=
  let a := analysis s g
  if a.bad then false
  else
    let worst := if g.k != 0 then foldRoundError s g a 1 else baseError s g a
    worst.error.le (goalOf s .closeness scope) &&
    (Bound.ofNat load.messages * sampleError s a.list load.cubeBits s.samples).error.le
      (goalOf s .sample scope) &&
    (Bound.ofNat a.list * (powersError s load.batchedRows + fieldError s 1)).error.le
      (goalOf s .field scope)

/-- The group under the Johnson rule with the integer m. -/
def groupOfM (shape : GroupSize) (m : Nat) : GroupSize := { shape with m := m, rule := .johnson }

/-- The group under the Johnson rule with the m that `largestM` finds for `groupHolds`: the largest
m up to 2 ^ 40, that is the least slack, if the m that hold are one stretch of integers that begins
below 67. If no m from 3 to 66 holds, the group comes back with m = 0, and its analysis is bad. -/
def sizeGroup (s : Setting) (scope : Scope) (shape : GroupSize) (load : GroupLoad) : GroupSize :=
  groupOfM shape (largestM fun m => groupHolds s scope (groupOfM shape m) load)

/-- The number of positions of a list in a scope. -/
def scopePositions (s : Setting) (scope : Scope) (agree : Bound)
    (extra : Bound := Bound.ofWord 0) : Nat :=
  positions agree (s.target - s.workOf .query scope) extra
    (if scope == .request then s.instances else 1)

/-- For the iterations that solve positions and random entries from below (`turn`). On the way up a
shape can break a rule that it keeps at the fixed point: with few random entries the mask code may
still have the larger rate. Then the main code by itself gives a number of positions that is not too
large, because the mask code can only pull the distance down, and the iteration can go on. 0: the
main code by itself has no admissible distance either. -/
def positionsFromBelow (s : Setting) (scope : Scope) (shape : GroupSize) (load : GroupLoad)
    (extra : Bound) : Nat :=
  let g := sizeGroup s scope { shape with mask := {}, h := 0 } load
  if groupHolds s scope g load then scopePositions s scope (analysis s g).mainAt.agree extra else 0

/-- What a list of positions must carry beside its own term is far below the target. This margin, 30
bits below the target, takes its place while a group is solved. The plan's exact comparison
(`Planned.holds`) has the last word. -/
def margin (s : Setting) : Bound := Bound.exact (Binary.twoTo (-(s.target : Int) - 30))

/-- One outcome of a turn of the iteration. -/
inductive Turn where
  /-- the numbers have settled; t is the number of positions that follows from them -/
  | settled (g : GroupSize) (t : Nat)
  /-- more positions are needed -/
  | more (g : GroupSize) (t : Nat)
  /-- no admissible numbers follow -/
  | refused

/-- One turn of the iteration: sizes the group with the random entries mainR and maskR, derives the
number of positions t2 that follows, and compares it with the t from which the entries were made.
Refused if message and random entries exceed a code's length, or if the group's rounds do not hold
and t2 is not above t, so that no way up is left. -/
def turn (s : Setting) (scope : Scope) (load : GroupLoad) (shape : GroupSize)
    (mainR maskR t : Nat) : Turn :=
  let g : GroupSize :=
    { shape with main := { shape.main with r := mainR }, mask := { shape.mask with r := maskR } }
  if g.main.n < g.main.dim || g.mask.n < g.mask.dim then .refused
  else
    let sized := sizeGroup s scope g load
    let serves := groupHolds s scope sized load
    let a := analysis s sized
    let t2 :=
      if serves then scopePositions s scope a.mainAt.agree (margin s)
      else if a.fault then positionsFromBelow s scope g load (margin s)
      else 0
    if !serves && t2 ≤ t then .refused
    else if t2 ≤ t then .settled sized t2
    else .more sized t2

/-- A group and the number of positions at which it is tested. -/
structure Solved where
  group : GroupSize
  t : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The turns of `solveGroup`. -/
def solveGroupFrom (s : Setting) (scope : Scope) (load : GroupLoad)
    (draws : Nat → Nat) (shape : GroupSize) : Nat → Nat → Option Solved
  | 0, _ => none
  | fuel + 1, t =>
    match turn s scope load shape (tailFor (draws t)) (tailFor t) t with
    | .refused => none
    | .settled g t2 => if t2 == 0 then none else some ⟨g, t⟩
    | .more _ t2 => solveGroupFrom s scope load draws shape fuel t2

/-- Solves one group. `draws t` says at how many drawn positions a main row is opened in all when
one list has t; a mask row is opened at one list. The iteration goes up from t0 and stops where
the random entries are at least as many as the draws that follow from them. At most 32 turns. That
the result is the least such point is not proved under the Johnson rule, where a step of m can lower
the need by a position as the rate grows. -/
def solveGroup (s : Setting) (scope : Scope) (load : GroupLoad)
    (draws : Nat → Nat) (shape : GroupSize) (t0 : Nat := 0) : Option Solved :=
  solveGroupFrom s scope load draws shape 32 t0

/-! ## The stages of a proximity test

Stage 1 is the group that is tested. At each further stage the parameter file chooses the numbers of
row variables k' and h' into which the folded row and what travels with it are cut, and the lengths
of the two codes. The remainder follows (primes: the new stage; zk: the mask code):
 - main message: ell' = ell * slots / 2 ^ k'. It is cut by a power of two exactly, and no random
   entry goes into it.
 - mask message: 2 ^ h' * ell_zk' = 2 ell_zk + r * slots + 2 r_zk + r_ood. That is what the fold
   leaves of the two mask rows (the old one and the fresh one) and of the random entries with which
   the main row and these two were encoded, and r_ood further entries, at least `samples`, of which
   the last are the pad. ell_zk' is the least power of two that leaves room, and it is at least
   2 k' + 1 - h', for the next fold's mask.
 - random entries: r' = r_zk' = the number of positions at which the stage is opened. It depends on
   the rate, which depends on r': solved by iteration from below. -/

/-- A stage: its group, its positions, and the entries that fill its mask rows up. -/
structure StageSize where
  g : GroupSize
  /-- the positions at which this stage's rows are opened -/
  t : Nat := 0
  /-- the entries that fill the mask rows of this stage, the pad among them -/
  rOod : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The least power of two that is at least x. -/
def pow2AtLeast (x : Nat) : Nat := 2 ^ clog2 x

/-- The variables of the cube of a sample on a group's rows. -/
def stageCubeBits (g : GroupSize) : Nat :=
  let a := g.k + clog2 g.main.ell
  if g.hasMask then max a (g.h + clog2 g.mask.ell) + 1 else a

/-- The turns by which one later stage is solved, at most as many as the fuel. `beforeR`: the random
entries of a main row of the stage before. The switch into this stage batches three rows for each
position of that stage, so the declared load is 4 + 3 * max beforeR 1024 rows. -/
def solveStageFrom (s : Setting) (scope : Scope) (beforeR : Nat)
    (shape : GroupSize) : Nat → Nat → Option Solved
  | 0, _ => none
  | fuel + 1, t =>
    let load : GroupLoad :=
      { cubeBits := stageCubeBits shape, messages := 1, batchedRows := 4 + 3 * max beforeR 1024 }
    match turn s scope load shape (tailFor t) (tailFor t) t with
    | .refused => none
    | .settled g _ => some ⟨g, t⟩
    | .more _ t2 => solveStageFrom s scope beforeR shape fuel t2

/-- The later stages, one after the other. `o` is the group of the stage before. Nothing if a middle
stage does not have 1 ≤ k ≤ 32 and h ≤ k, if the last stage does not have k = h = 0, if the folded
row cannot be cut into 2 ^ k rows, or if a stage cannot be solved. -/
def solveLater (s : Setting) (scope : Scope) :
    GroupSize → List StageLine → Option (List StageSize)
  | _, [] => some []
  | o, c :: rest =>
    if c.k < c.h || 32 < c.k || (if rest.isEmpty then c.k != 0 else c.k == 0) ||
        o.main.ell * o.slots % 2 ^ c.k != 0 then none
    else
      let carried := 2 * o.mask.ell + o.main.r * o.slots + 2 * o.mask.r
      let ownFold := if c.k != 0 then 2 * c.k + 1 - c.h else 1
      let maskEll := max (pow2AtLeast ((carried + s.samples + 2 ^ c.h - 1) / 2 ^ c.h))
        (pow2AtLeast ownFold)
      let shape : GroupSize :=
        { main := { logN := c.logN, ell := o.main.ell * o.slots / 2 ^ c.k, overE := true }
          mask := { logN := c.maskLogN, ell := maskEll, overE := true }
          k := c.k
          h := c.h }
      match solveStageFrom s scope o.main.r shape 32 0 with
      | none => none
      | some x =>
        (solveLater s scope x.group rest).map
          (⟨x.group, x.t, maskEll * 2 ^ c.h - carried⟩ :: ·)

/-- The stages of a proximity test. `first` is stage 1 with its distance fixed and firstT its number
of positions. Nothing if no further stage is
chosen or stage 1 has k = 0: a proximity test folds at its first stage and has a last stage. -/
def solveStages (s : Setting) (scope : Scope) (first : GroupSize) (firstT : Nat)
    (choice : List StageLine) : Option (List StageSize) :=
  if choice.isEmpty || first.k == 0 then none
  else (solveLater s scope first choice).map (⟨first, firstT, 0⟩ :: ·)

/-! ## The committed table

The table has 2 ^ v rows over the base field under one code. It has a record, that is sample answers
for each row, taken once, right after the table is committed: a one-time test at a distance delta_M,
and every later test at a distance of at most delta_M, which may lie beyond unique decoding.
The price of a later test is a true bound only of a table that has passed the one-time test at the
same distances, and that test is in another file's plan (blocks/numbers/plan.h: TableTest). -/

/-- The two distances of a committed table: of the one-time test and of a later
test. Either in whole positions of the code's length (`radius`, `laterRadius`) or, where `mOnce` is
not 0, by the assumed theorem's integers (`mOnce`, `mLater`), which
`sizeRecordedTable` derives. -/
structure TableDistances where
  radius : Nat := 0
  laterRadius : Nat := 0
  mOnce : Nat := 0
  mLater : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The committed table: 2 ^ v rows over the base field under one code. -/
structure TableSize where
  code : CodeSize := {}
  v : Nat := 0
  /-- the answers for each row of the record -/
  answers : Nat := 1
  distances : TableDistances := {}
  deriving DecidableEq, Repr, Inhabited

/-- What the analysis says of the table. -/
structure TableAnalysis where
  /-- the code at the distance of the one-time test -/
  once : Proximity := {}
  /-- the code at the distance of a later test -/
  later : Proximity := {}
  deriving DecidableEq, Repr, Inhabited

/-- What the analysis says of a table, from its code, its distances and the setting. -/
def tableAnalysis (s : Setting) (T : TableSize) : TableAnalysis :=
  let c := wordOf T.code
  if T.distances.mOnce != 0 then
    let later := johnson c T.distances.mLater s.printed
    { once := johnson c T.distances.mOnce s.printed, later := later }
  else
    let share := Bound.ratio T.distances.radius T.code.n
    let once := atDistance s c (Bound.ofWord 1 - share)
    { once := once
      later := atDistance s c (Bound.ofWord 1 - Bound.ratio T.distances.laterRadius T.code.n) }

/-- The conditions under which the table's formulas hold. The record's round is charged with the list at the one-time distance, so no later test goes
beyond that distance. -/
def tableAdmitted (T : TableSize) (a : TableAnalysis) : Bool :=
  if a.once.bad then false
  else if a.later.bad || T.answers == 0 then false
  else if a.once.fromM && a.later.fromM then decide (a.later.m ≤ a.once.m)
  else surelyLe a.later.delta a.once.delta

/-- The sum of the closeness terms for the variables j = 1 .. v, from j on. -/
def tableFoldTerms (s : Setting) (v : Nat) (x : Proximity) : Nat → Nat → Bound → Bound
  | 0, _, e => e
  | fuel + 1, j, e => tableFoldTerms s v x fuel (j + 1) (e + mcaError s x (2 ^ (v - j)))

/-- The closeness term of a fold of all 2 ^ v rows by equality weights in one message. -/
def tableFoldError (s : Setting) (T : TableSize) (x : Proximity) : Bound :=
  tableFoldTerms s T.v x T.v 1 (Bound.ofWord 0) + Bound.ofNat x.list * fieldError s T.v

/-- Both distances go up to the Johnson radius and are derived. Each takes the m that
`largestM` finds, the largest under that function's condition, for which the round of the fold point
holds with its work, and for the one-time distance also the record's own round. The fold's closeness
term counts twice, because a link's such round carries the terms of two tables. A later test's m is
at most the one-time test's. `requests` share a batch's point, which has `pointVariables`
coordinates. The record's own round is held to the bare target: it has no work (`planRecord`),
whatever bits the setting has for samples. Nothing: no distance serves. -/
def sizeRecordedTable (s : Setting) (T : TableSize) (requests pointVariables : Nat) :
    Option TableSize :=
  let sized := fun (scope : Scope) (sharing : Nat) (withRecord : Bool) =>
    largestM fun m =>
      let x := johnson (wordOf T.code) m s.printed
      if x.bad then false
      else
        let point := Bound.ofNat sharing * fieldError s pointVariables +
          Bound.ofWord 2 * tableFoldError s T x
        point.error.le (goalOf s .closeness scope) &&
          (!withRecord ||
            (sampleError s x.list (clog2 T.code.ell) T.answers).error.le
              (Binary.twoTo (-(s.target : Int))))
  let mOnce := sized .once 1 true
  let mLater := min mOnce (sized .shared requests false)
  if mLater == 0 then none
  else some { T with distances := { T.distances with mOnce := mOnce, mLater := mLater } }

end OnBytes.Params
