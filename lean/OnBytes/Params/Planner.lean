-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Planner.lean: how the plan of a chain is written, round by round, with each round's
error.

A plan lists the rounds of a chain. For each round it says how many bytes the prover sends, what
the verifier draws and how much work is asked. The C++ programs make a plan by one routine for
each block of the protocol (blocks/numbers/plan.h, blocks.h). Each routine also bounds the error
of every round that it adds, and the finished plan is asked whether every round holds at the
target. This file renders these routines. To price a round is to compute the bound on its error.

What is left out of a C++ plan:
 - what it holds for prints and for accounts of sizes: the messages with their sizes in the files,
   names of places, repeats of equal rounds;
 - the trees and their openings (plan_open in blocks.h), with that routine's two refusals of a tree
   that is marked for one list of positions;
 - part of what it says beside a round so that the run can be compared with it: a group's numbers of
   rows, the table, a first list, the number of requests. What follows for the run of a proximity
   test is said in OnBytes/Iop/Prox.lean under "What is not asked here".

The blocks, by the words with which the names of their rounds begin in the format:
   SEND       an oracle message, the seed of its out-of-domain sample, the answer
   BAT        many linear rows on one group into one row; from here on some code word of the list is
              meant, so the error has the list size as a factor
   BAT-sigma  many linear rows into one, still about the decoded messages: no list size
   SPLIT      a row on two groups into a row on each
   PSC        a sumcheck for a polynomial summand, with a hiding polynomial and a further variable Y
   ZERO, LINE the point of a zero check; two evaluation claims into one
   LKP, JOIN  a lookup by product trees; claims of one shape into one
   RNG        the draw of the matrix with entries in {-1, 0, 1} for the test that cells are small
   FOLD       a sumcheck over the row variables of a group
   LOC        a draw of positions of a group whose fold was encoded anew in a sampled oracle message
   CS         the code switch inside a proximity test: SEND, then positions and the batching
              challenge in one message
   BASE       the last stage of a proximity test: a masked code word in the clear
   LIN, LINK, RECORD   the test on the committed table, the link of two tables, the table's sample

A routine is a `Planning`: it adds rounds to the state, or it refuses under a name. Unless a caller
gives another, the name is `parameters-not-admitted`, under which the C++ verifier refuses the
public files.

Main definitions: `PlanRound`, `PlanState`, `Planning`, `close`, `closeNone`, the routines
`planSend` to `planLink`, `Planned`, `finish`, `Planned.holds`.
What is not claimed: that the errors bound what their names say. No theorem is stated here.
-/
import OnBytes.Base
import OnBytes.Chain.Lists
import OnBytes.Params.Group

namespace OnBytes.Params

/-- The two codes of a group, each as (logN, ell, r), and the choice of the analysis (the rule and
its integer), as a plan says them beside a round. The C++ struct (plan.h: PricedGroup) also has the
numbers of rows k, h and slots, which the plan's verdict does not read. -/
structure PricedChoice where
  main : Nat × Nat × Nat
  mask : Nat × Nat × Nat
  rule : Radius
  m : Nat
  deriving DecidableEq, Repr, Inhabited

/-- What a plan says of a group's codes and choice. -/
def pricedOf (g : GroupSize) : PricedChoice where
  main := (g.main.logN, g.main.ell, g.main.r)
  mask := if g.hasMask then (g.mask.logN, g.mask.ell, g.mask.r) else (0, 0, 0)
  rule := g.rule
  m := g.m

/-- From what a round's error was priced: one word for every round with a verifier's message, given
by the routine that closes it (`close`). The plan's verdict compares the word with the round
(`wordFaultOf`). -/
inductive Priced where
  /-- the round has no error -/
  | nothing
  /-- from the setting alone -/
  | settingAlone
  /-- from the setting and a number that the round's own entry fixes -/
  | roundItself
  /-- from what the C++ plan says beside the round (rows, a group, combinations) and from nothing
  else. Of a group only the codes and the choice are kept here (`PricedChoice`), not the numbers of
  rows, which a fold's error reads too. In the C++ the block asks for these numbers at the run; for
  this program see OnBytes/Iop/Prox.lean, "What is not asked here" -/
  | asSaid
  /-- from a number that the caller of the routine supplies and that nothing checks at this round,
  whatever else the round says: the groups whose lists count at a sample or a batching, the cubes of
  the smaller oracle messages under one seed, a lookup's table and keys, the list of the next stage
  in a code switch's batching term, the table's distances. Nothing in this file checks that number.
  The C++ keeps the word in the round so that such rounds can be found and counted; here only
  `wordFaultOf` reads it -/
  | callersWord
  deriving DecidableEq, Repr, Inhabited

/-- A round of a plan: its entry in the parameter bytes, and what the plan's verdict reads. -/
structure PlanRound where
  entry : Fmt.Entry
  /-- an upper bound on the round's error, work not counted -/
  error : Binary := {}
  /-- the group from which the error was priced, if the plan says one -/
  group : Option PricedChoice := none
  /-- by which argument the error is bounded -/
  why : ErrorKind := .zero
  /-- of a round with a closeness term: the weakest footing of a count in it; the weakest of all
  unless the routine says better -/
  rests : CountSource := .johnson
  /-- who pays for the round's work -/
  scope : Scope := .request
  /-- the word on how the round was priced contradicts the round -/
  wordFault : Bool := false
  deriving Inhabited

/-- A plan that is being written. -/
structure PlanState where
  set : Setting
  scope : Scope := .request
  rounds : Array PlanRound := #[]
  /-- the bytes, roots and answers of the prover's message that no round has taken in yet -/
  openBytes : Nat := 0
  openRoots : Nat := 0
  openAnswers : Nat := 0

/-- A routine that writes into a plan, or refuses under a name. -/
abbrev Planning : Type → Type := StateT PlanState (Except String)

/-- The name under which public files are refused from which no admissible numbers follow. -/
def notAdmitted : String := "parameters-not-admitted"

/-- Refuses the plan. -/
def refusePlan {α : Type} (why : String := notAdmitted) : Planning α := fun _ => .error why

/-- Refuses the plan unless b is true. -/
def needs (b : Bool) (why : String := notAdmitted) : Planning Unit :=
  if b then pure () else refusePlan why

/-- The value of x, or a refusal if there is none. -/
def orRefuse {α : Type} (x : Option α) (why : String := notAdmitted) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error why

/-- The value of x inside a routine, or a refusal of the plan if there is none. -/
def must {α : Type} (x : Option α) (why : String := notAdmitted) : Planning α :=
  match x with
  | some a => pure a
  | none => refusePlan why

/-- The setting. -/
def theSetting : Planning Setting := fun p => .ok (p.set, p)

/-- The scope under which the next rounds are added. -/
def theScope : Planning Scope := fun p => .ok (p.scope, p)

/-- The prover sends n elements of the extension field. -/
def planScalars (n : Nat) : Planning Unit :=
  modify fun p => { p with openBytes := p.openBytes + 24 * n }

/-- The prover sends n answers to samples. -/
def planAnswers (n : Nat) : Planning Unit :=
  modify fun p => { p with openBytes := p.openBytes + 24 * n, openAnswers := p.openAnswers + n }

/-- The prover sends n roots. -/
def planRoots (n : Nat) : Planning Unit :=
  modify fun p => { p with openBytes := p.openBytes + 32 * n, openRoots := p.openRoots + n }

/-- A round in which the verifier says nothing. It still makes its query of the hash chain, which
takes the prover's message in. If that message holds a root, the plan is refused. -/
def closeNone (name : String) : Planning Unit := fun p =>
  if p.openRoots != 0 then .error notAdmitted
  else
    .ok ((), { p with
      rounds := p.rounds.push
        { entry := { name, msg := p.openBytes, answers := p.openAnswers }, scope := p.scope },
      openBytes := 0, openAnswers := 0 })

/-- What the routine that adds a round fills in: the draws of the round's entry, and what the plan
says beside the round. -/
structure Draws where
  drawE : Nat := 0
  drawNZ : Nat := 0
  poss : Nat := 0
  logN : Nat := 0
  trits : Nat := 0
  rows : Nat := 0
  group : Option PricedChoice := none
  rests : CountSource := .johnson
  /-- the combinations of a smallness test -/
  combinations : Nat := 0
  priced : Priced := .nothing

/-- True if the word on how a round was priced contradicts the round: a draw of positions or of a
matrix at the error 0 that is not priced on the caller's word; an error from nothing; a round that
is priced from the setting or from itself and says something beside; a round that is priced from
what is said beside it, and nothing is said. A C++ plan can also say a table, a first list or a
number of requests beside a round. These are not kept here: the rounds that say them are priced on
the caller's word, and of such a round nothing is asked about what it says. -/
def wordFaultOf (d : Draws) (error : Binary) : Bool :=
  let says := d.rows != 0 || d.group.isSome || d.combinations != 0
  ((d.poss != 0 || d.trits != 0) && error.isZero && d.priced != .callersWord) ||
  (d.priced == .nothing && !error.isZero) ||
  ((d.priced == .settingAlone || d.priced == .roundItself) && says) ||
  (d.priced == .asSaid && !says)

/-- A round with a verifier's message. The bits of work are the setting's for the kind of the error
and the scope. In a request's own rounds the error counts once for each instance. Refused if the
error is bad, if the work is not below the target, or if the work and six bits more do not fit the
nonce. The six bits of room are meant to keep an honest search for a nonce inside the nonce's range
(blocks/numbers/plan.h, Plan::close, gives the estimate). -/
def close (name : String) (why : ErrorKind) (error : Bound) (d : Draws := {}) : Planning Unit :=
  fun p =>
    let s := p.set
    let e := if p.scope == .request && 1 < s.instances then error * Bound.ofNat s.instances
      else error
    let work := s.workOf why p.scope
    if e.bad || s.target ≤ work || (work != 0 && 8 * s.nonceBytes < work + 6) then
      .error notAdmitted
    else
      .ok ((), { p with
        rounds := p.rounds.push
          { entry := { name, work, msg := p.openBytes, roots := p.openRoots,
                       answers := p.openAnswers, drawE := d.drawE, drawNZ := d.drawNZ,
                       poss := d.poss, logN := d.logN, trits := d.trits, rows := d.rows },
            error := e.error, group := d.group, why := why, rests := d.rests, scope := p.scope,
            wordFault := wordFaultOf d e.error },
        openBytes := 0, openRoots := 0, openAnswers := 0 })

/-- The place of a source in the order from the strongest footing to the weakest. -/
def CountSource.rank : CountSource → Nat
  | .third => 0
  | .johnson => 1

/-- On what a group's closeness terms rest: the weakest of the sources of its two codes. -/
def weakestSource (a : Analysis) : CountSource :=
  if a.withMask && a.mainAt.source.rank < a.maskAt.source.rank then a.maskAt.source
  else a.mainAt.source

/-- The analysis of a group. A bad one refuses the plan. -/
def planAnalysis (g : GroupSize) : Planning Analysis := do
  let a := analysis (← theSetting) g
  needs (!a.bad)
  pure a

/-- The number of positions of a list in the present scope. -/
def planPositions (agree : Bound) (extra : Bound := Bound.ofWord 0) : Planning Nat := do
  pure (scopePositions (← theSetting) (← theScope) agree extra)

/-- Refuses if a proof lists its positions (`positionBytes` and t are not 0) and a position below
2 ^ logN does not fit the setting's bytes for a listed position. It adds nothing to the plan: listed
positions do not enter the chain. -/
def planListed (logN t : Nat) : Planning Unit := do
  let s ← theSetting
  needs (t == 0 || s.positionBytes == 0 || !(s.positionBytes < 8 && 8 * s.positionBytes < logN))

/-! ## Sending, batching, splitting -/

/-- One oracle message as its sample sees it: the variables of its cube, and the groups in which
its rows are tested. -/
structure SampleSize where
  cubeBits : Nat
  groups : List GroupSize

/-- The largest list size among groups; a bad analysis refuses the plan. No group: 1, on the
caller's word. In the C++ only tests may write that case (blocks.h: no_sized_group). -/
def listOfGroups : List GroupSize → Planning Nat
  | [] => pure 1
  | g :: gs => do
    let a ← planAnalysis g
    let l ← listOfGroups gs
    pure (max a.list l)

/-- The sum of the sample errors of oracle messages, from e on. -/
def sampleErrors (s : Setting) : List SampleSize → Bound → Planning Bound
  | [], e => pure e
  | x :: xs, e => do
    let l ← listOfGroups x.groups
    sampleErrors s xs (e + sampleError s l x.cubeBits s.samples)

/-- The block SEND. All oracle messages of one prover's message: for each answer one seed (a point
of the largest cube, of which each message uses a prefix, and one pad factor, which is not 0);
answers for each message; the errors add. `roots`: how many roots the message holds. `answerRound`
false: the block that calls closes the round of the answers with a verifier's message of its own. -/
def planSend (o : List SampleSize) (roots : Nat) (answerRound : Bool := true) : Planning Unit := do
  let s ← theSetting
  planRoots roots
  let e ← sampleErrors s o (Bound.ofWord 0)
  let cube := o.foldl (fun c x => max c x.cubeBits) 0
  close "SEND seed" .sample e
    { drawE := s.samples * (cube + 1), drawNZ := s.samples, priced := .callersWord }
  planAnswers (s.samples * o.length)
  if answerRound then closeNone "SEND answer"

/-- The challenge that batches rows. `groups`: those in which the rows are tested. -/
def planBat (groups : List GroupSize) (rows : Nat) : Planning Unit := do
  let s ← theSetting
  let l ← listOfGroups groups
  close "BAT" .field (Bound.ofNat l * powersError s rows)
    { drawE := 1, rows := rows, priced := .callersWord }

/-- The challenge that batches pending rows on the committed matrix. -/
def planBatSigma (rows : Nat) : Planning Unit := do
  close "BAT-sigma" .field (powersError (← theSetting) rows)
    { drawE := 1, rows := rows, priced := .asSaid }

/-- The block SPLIT (a row on two groups into a row on each): the prover sends one target. -/
def planSplit : Planning Unit := do
  planScalars 1
  closeNone "SPLIT"

/-! ## Sumchecks, product trees, lookups -/

/-- A sumcheck with a hiding sum (the block PSC). `degree`: the round polynomial of each variable
has a degree below this number. `degreeY`: the total degree of the summand in the maps that it
evaluates. `values`: the values at the last point. `withY` false: the summand is affine in all its
maps, so there is no further variable and there are no end values. -/
structure PscSize where
  degree : List Nat := []
  degreeY : Nat := 2
  values : Nat := 2
  withY : Bool := true

/-- The rounds of the variables of a sumcheck. -/
def planPscRounds (s : Setting) : List Nat → Planning Unit
  | [] => pure ()
  | g :: gs => do
    planScalars (g - 1)
    close "PSC round" .field (fieldError s (g - 1)) { drawE := 1, priced := .roundItself }
    planPscRounds s gs

/-- The rounds of a sumcheck. The coefficient that the verifier's check fixes is not sent. The round
`PSC epsilon` has the error 1 / |E| with no list size as a factor (`FOLD epsilon` has one): the
claim speaks of one definite object, and nothing is read at a distance from a code word here. -/
def planPsc (x : PscSize) : Planning Unit := do
  let s ← theSetting
  planScalars 1
  close "PSC epsilon" .field (fieldError s 1) { drawE := 1, priced := .settingAlone }
  planPscRounds s x.degree
  if x.withY then
    planScalars x.degreeY
    close "PSC Y" .field (fieldErrorNonzero s x.degreeY)
      { drawE := 1, drawNZ := 1, priced := .roundItself }
    planScalars x.values
    closeNone "PSC values"

/-- A point at which a polynomial that should be zero is tested. -/
def planZero (variables : Nat) : Planning Unit := do
  close "ZERO" .field (fieldError (← theSetting) variables)
    { drawE := variables, priced := .roundItself }

/-- The point of a line between two values. -/
def planLine : Planning Unit := do
  close "LINE" .field (fieldError (← theSetting) 1) { drawE := 1, priced := .settingAlone }

/-- Several tables joined into one by a random shift theta: key + j theta is looked up in the union
of the tables T_j + j theta. The protocol's argument is that a key outside its table meets the union
for at most as many theta as the union has entries, which gives the round's error. -/
def planShift (unionEntries : Nat) : Planning Unit := do
  close "LKP shift" .field (fieldError (← theSetting) unionEntries)
    { drawE := 1, priced := .callersWord }

/-- 2 ^ variables claims of one shape joined into one at a fresh point, by equality weights. The
protocol's argument is that a false claim among them leaves the joined claim false, except with the
round's error, variables / |E|. -/
def planJoin (variables : Nat) : Planning Unit := do
  close "JOIN" .field (fieldError (← theSetting) variables)
    { drawE := variables, priced := .roundItself }

/-- The challenge at which two products over 2 ^ keysLog keys are compared. -/
def planLkp (keysLog : Nat) : Planning Unit := do
  close "LKP" .field (Bound.ratio (2 ^ keysLog - 1) (← theSetting).cardE)
    { drawE := 1, priced := .callersWord }

/-- The levels of a product tree from level l on, as many as the fuel. -/
def planTreeLevels (more : Nat) : Nat → Nat → Planning Unit
  | 0, _ => pure ()
  | fuel + 1, l => do
    planPsc { degree := List.replicate (l + more) 3 }
    planLine
    planTreeLevels more fuel (l + 1)

/-- The levels of a product tree from the root down. Level l = 0 .. levels - 1 is a sumcheck with
l + more variables for the product of two halves under equality weights, two values, then LINE.
`more`: variables that index the trees of a forest, or the bits of a multiplicity. -/
def planProductTree (levels more : Nat) : Planning Unit := planTreeLevels more levels 0

/-- Several pending rows on the committed matrix into one: a batching challenge, then a sumcheck
over the kCol column variables on maps that are kept, so without a round in Y and without end
values. -/
def planBatt (rows kCol : Nat) : Planning Unit := do
  planBatSigma rows
  planPsc { degree := List.replicate kCol 3, withY := false }

/-- One lookup: 2 ^ v keys, never sent, in a table of 2 ^ d entries, with the multiplicities in
2 ^ mu planes of bits, which the caller has sent and sampled. `shifted`: several functions share the
table. -/
structure LookupSize where
  v : Nat := 0
  d : Nat := 0
  mu : Nat := 0
  shifted : Bool := false
  /-- how many of the plane slots are real; 0: all -/
  live : Nat := 0
  /-- the logarithm of the keys of each part; empty: one part of 2 ^ v keys -/
  parts : List Nat := []

/-- Runs a routine n times. -/
def times (n : Nat) (x : Planning Unit) : Planning Unit :=
  match n with
  | 0 => pure ()
  | k + 1 => do
    x
    times k x

/-- Runs a routine on each member of a list. -/
def forEach {α : Type} (l : List α) (f : α → Planning Unit) : Planning Unit :=
  match l with
  | [] => pure ()
  | a :: t => do
    f a
    forEach t f

/-- The rounds of one lookup, in this order: the shift, if several functions share the table; the
challenge at which the two products are compared; the tie of the two sides' roots, a chain of
sumchecks without variable on values that are never sent; with several parts, from the product of
their roots to each root; a point that makes the planes' claims one; the key side's product trees;
the table side's; the layer of its leaves, affine in the bits; the test that the bits are bits.
Refused unless mu is from 1 to 6 and w, the number of live planes, from 2 to 2 ^ mu; a multiplicity
has room for all keys, keys < 2 ^ w; and the sum of all multiplicities, read in the base field,
cannot wrap around, 2 ^ d (2 ^ w - 1) < p. -/
def planLookup (x : LookupSize) : Planning Unit := do
  let s ← theSetting
  let slots := 2 ^ min x.mu 6
  let w := if x.live != 0 then x.live else slots
  let parts := if x.parts.isEmpty then [x.v] else x.parts
  let keys := sumT (parts.map (2 ^ ·))
  needs (decide (1 ≤ x.mu) && decide (x.mu ≤ 6) && decide (2 ≤ w) && decide (w ≤ slots))
  needs (decide (keys < 2 ^ w) && decide (2 ^ x.d * (2 ^ w - 1) < s.p))
  if x.shifted then planShift (2 ^ x.d)
  close "LKP" .field (Bound.ratio (keys - 1) s.cardE) { drawE := 1, priced := .callersWord }
  planPsc { degreeY := 3, values := 3 }
  times (w - 2) (planPsc { degreeY := 3, values := 2 })
  times (parts.length - 1) (planPsc {})
  planJoin x.mu
  forEach parts fun v => planProductTree v 0
  planProductTree x.d x.mu
  planPsc { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false }
  planZero (x.mu + x.d)
  planPsc { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 }

/-- The combinations of the smallness test: the target less the round's work, and the bits that
the number of instances costs. -/
def rngCombinations (s : Setting) (scope : Scope) : Nat :=
  (s.target - s.workOf .small scope) + (if scope == .request then clog2 s.instances else 0)

/-- The draw of the matrix of the smallness test. An entry is 0 with probability 1/2, and 1 or -1
with probability 1/4 each. For that draw the round is priced at 2 ^ -combinations (the C++ comment
has (5/9) ^ combinations for uniform entries). Refused if the number of drawn entries does not fit
64 bits. -/
def planRng (columns : Nat) : Planning Unit := do
  let n := rngCombinations (← theSetting) (← theScope)
  needs (n == 0 || decide (columns ≤ (2 ^ 64 - 1 - 31) / n))
  close "RNG" .small (Bound.exact (Binary.twoTo (-(n : Int))))
    { trits := columns * n, combinations := n, priced := .asSaid }

/-! ## Folding, positions, the proximity test -/

/-- The rounds of a fold from round j on, as many as the fuel. -/
def planFoldFrom (s : Setting) (g : GroupSize) (a : Analysis) : Nat → Nat → Planning Unit
  | 0, _ => pure ()
  | fuel + 1, j => do
    planScalars 2
    close "FOLD round" .closeness (foldRoundError s g a j)
      { drawE := 1, group := pricedOf g, priced := .asSaid,
        rests := if g.hasMask && j ≤ g.h then weakestSource a else a.mainAt.source }
    planFoldFrom s g a fuel (j + 1)

/-- The rounds j = 1 .. k of a fold, which follow the round `FOLD epsilon`. -/
def planFoldRounds (g : GroupSize) : Planning Unit := do
  let a ← planAnalysis g
  planFoldFrom (← theSetting) g a g.k 1

/-- A fold. `roots`: 1 if the fresh mask's tree is sent with this message, 0 if the mask went out
earlier. -/
def planFold (g : GroupSize) (roots : Nat) : Planning Unit := do
  let s ← theSetting
  let a ← planAnalysis g
  planRoots roots
  planScalars 1
  close "FOLD epsilon" .field (Bound.ofNat a.list * fieldError s 1)
    { drawE := 1, group := pricedOf g, priced := .asSaid }
  planFoldRounds g

/-- The block LOC: the positions of a group, after the answer to the sample of the oracle message
that encodes its fold anew. Returns their number. -/
def planLoc (g : GroupSize) : Planning Nat := do
  let a ← planAnalysis g
  let t ← planPositions a.mainAt.agree
  needs (t != 0)
  close "LOC" .query (Bound.pow a.mainAt.agree t)
    { poss := t, logN := g.main.logN, group := pricedOf g, priced := .asSaid }
  planListed g.main.logN t
  pure t

/-- The number of positions where the batching term grows with t. From below: each turn takes the
least t for the batching term at the t before. The sequence does not fall and never passes the least
t that serves, so where it stays the same it has found that t. 0: no number reaches the target. The
C++ loop has no bound on its turns. Here the last t is returned if the fuel is used up; the round is
priced at that t, and `Planned.holds` decides. -/
def csPositions (s : Setting) (scope : Scope) (agree : Bound) (list oldRows symbols : Nat) :
    Nat → Nat → Nat
  | 0, t => t
  | fuel + 1, t =>
    let next := scopePositions s scope agree
      (Bound.ofNat list * powersError s (oldRows + s.samples + symbols * t))
    if next == t || next == 0 then next
    else csPositions s scope agree list oldRows symbols fuel next

/-- Inside a proximity test: the new oracle message, its sample, then in one message the positions
of the old group and the challenge that batches old rows, sample rows and generator rows (`symbols`
generator rows at each position). Returns the number of positions. -/
def planCs (source target : GroupSize) (cubeBits oldRows symbols roots : Nat) : Planning Nat := do
  let s ← theSetting
  let a ← planAnalysis source
  let next ← planAnalysis target
  planSend [⟨cubeBits, [target]⟩] roots false
  let t := csPositions s (← theScope) a.mainAt.agree next.list oldRows symbols 64 0
  needs (t != 0)
  let rows := oldRows + s.samples + symbols * t
  close "CS" .query (Bound.pow a.mainAt.agree t + Bound.ofNat next.list * powersError s rows)
    { poss := t, logN := source.main.logN, drawE := 1, rows := rows, group := pricedOf source,
      priced := .callersWord }
  planListed source.main.logN t
  pure t

/-- The block BASE, the last step of a proximity test: a masked code word in the clear. `g`: one
main row and, if it has a mask code, one mask row. `roots`: 1 if the tree of the masking word is
sent with this message, 0 if it went out earlier. Returns the number of positions. -/
def planBase (g : GroupSize) (roots : Nat) : Planning Nat := do
  let s ← theSetting
  let a ← planAnalysis g
  planRoots roots
  planScalars 1
  close "BASE lambda" .closeness (baseError s g a)
    { drawE := 1, group := pricedOf g, rests := weakestSource a, priced := .asSaid }
  planScalars (g.main.dim * g.slots + (if g.hasMask then g.mask.dim else 0))
  let t ← planPositions a.mainAt.agree
  needs (t != 0)
  close "BASE" .query (Bound.pow a.mainAt.agree t)
    { poss := t, logN := g.main.logN, group := pricedOf g, priced := .asSaid }
  planListed g.main.logN t
  pure t

/-- The stages of a proximity test: fold and code switch for every stage except the last, then the
last step. `first` is true at stage 1. The numbers of positions are derived again here, each with
its round's whole error; a list may not be longer than the stage's random entries were sized for. -/
def planStages (firstMaskRoots : Nat) (masksRide : Bool) : Bool → List StageSize → Planning Unit
  | first, x :: y :: rest => do
    planFold x.g (if first then firstMaskRoots else if masksRide then 0 else 1)
    let t ← planCs x.g y.g (stageCubeBits y.g) 1 (x.g.slots + (if x.g.hasMask then 2 else 0)) 1
    needs (decide (t ≤ x.t))
    planStages firstMaskRoots masksRide false (y :: rest)
  | _, [x] => do
    let t ← planBase x.g (if masksRide then 0 else 1)
    needs (decide (t ≤ x.t))
  | _, [] => refusePlan

/-- A proximity test: the batching of `rows` rows, then fold and code switch stage by stage, then
the last step. `firstMaskRoots`: 1 if the fresh mask of stage 1's fold is sent by the fold, in a
tree of its own; 0 if it went out earlier. `masksRide` false: every later stage sends the fresh mask
of its fold (the last step: its masking word) in a tree of its own. True: those masks are sent in
the code switch's prover's message and share its tree. Refused for fewer than two stages. -/
def planIopp (st : List StageSize) (rows firstMaskRoots : Nat) (masksRide : Bool) :
    Planning Unit := do
  needs (decide (2 ≤ st.length))
  planBat (st.take 1 |>.map (·.g)) rows
  planStages firstMaskRoots masksRide true st

/-! ## The committed table -/

/-- The analysis of the table. Distances that are not admitted refuse the plan. -/
def planTable (T : TableSize) : Planning TableAnalysis := do
  let s ← theSetting
  let a := tableAnalysis s T
  needs (tableAdmitted T a)
  pure a

/-- The entry for a table's own sample, its record. It is no query of this chain: the seeds are
drawn on a chain of their own, without salt or work. The error is priced with the list at the
largest distance at which the table is ever read, the one-time test's. -/
def planRecord (T : TableSize) : Planning Unit := do
  let s ← theSetting
  let A ← planTable T
  let cube := clog2 T.code.ell
  let r : PlanRound :=
    { entry := { name := "RECORD", drawE := T.answers * (cube + 1), drawNZ := T.answers },
      error := (sampleError s A.once.list cube T.answers).error, why := .sample,
      scope := ← theScope }
  modify fun p => { p with rounds := p.rounds.push r }

/-- The query that ends a chain. Nothing of it is written into a proof. -/
def planSeal : Planning Unit := close "SEAL" .zero (Bound.ofWord 0)

/-- The sizes of the test on the table (the block LIN) before its proximity tests. The programs run
it on three hash chains: first, on the request's chain, the oracle message W of the request and its
sample (`planLinFirst`); then, on the batch's chain, `planLinShared`; then the proximity tests. `w`,
`u`, `omega`: the samples of W, of the folded row encoded anew, and of Omega, the table times the
equality vector of the shared point. `kLo`: the low variables of the shared point. `rowsLog`: the
variables of the point of comparison. -/
structure LinSize where
  w : SampleSize
  u : SampleSize
  omega : SampleSize
  /-- how many requests share the point -/
  instances : Nat := 1
  kLo : Nat := 0
  rowsLog : Nat := 0
  /-- further oracle messages in W's and in Omega's prover's message -/
  besideW : List SampleSize := []
  besideOmega : List SampleSize := []
  /-- the committer's own test -/
  oneTime : Bool := false
  rootsW : Nat := 1
  rootsU : Nat := 1
  rootsOmega : Nat := 1

/-- On a request's chain: the request's oracle message W (`LinSize`) and its sample. -/
def planLinFirst (x : LinSize) : Planning Unit := planSend (x.w :: x.besideW) x.rootsW

/-- On the batch's shared chain: the shared point; the folded row, encoded anew, and its sample; the
table's columns; Omega (the table times the equality vector of the shared point) and its sample; the
point at which the two are compared. Returns the number of columns. The rounds that are priced from
the table's distances are on the caller's word: a later test's price is a true bound only of a table
that has passed the one-time test at the same distances, and that test is in another file's plan. -/
def planLinShared (T : TableSize) (x : LinSize) : Planning Nat := do
  let s ← theSetting
  let A ← planTable T
  let y := if x.oneTime then A.once else A.later
  let point := Bound.ofNat x.instances * fieldError s (T.v + x.kLo)
  close "LIN point" .closeness (point + tableFoldError s T y)
    { drawE := T.v + x.kLo, rests := y.source, priced := .callersWord }
  planSend [x.u] x.rootsU
  let agree := y.agree
  let nu ← planPositions agree
  needs (nu != 0)
  close "LOC" .query (Bound.pow agree nu)
    { poss := nu, logN := T.code.logN, priced := .callersWord }
  planListed T.code.logN nu
  planSend (x.omega :: x.besideOmega) x.rootsOmega
  close "LIN zeta" .field (fieldError s x.rowsLog) { drawE := x.rowsLog, priced := .roundItself }
  pure nu

/-- The block LINK, the link of a further table to the first one, before its proximity test: the
fold point; two folded rows, encoded anew, and their samples; the columns of both tables in one
message; the point of comparison. The message with the two lists has the larger of the two lists'
errors, not their sum. The protocol's argument is that which of the two folded rows is false is
fixed before the draw, and that row's own list must miss it. Returns the numbers of columns of the
first and of the further table. -/
def planLink (T : TableSize) (u : SampleSize) : Planning (Nat × Nat) := do
  let s ← theSetting
  let A ← planTable T
  let first := A.later
  let e := fieldError s T.v + tableFoldError s T A.once
  close "LINK point" .closeness (e + tableFoldError s T first)
    { drawE := T.v, priced := .callersWord,
      rests := if A.once.source.rank < first.source.rank then first.source
        else A.once.source }
  planRoots 1
  let l ← listOfGroups u.groups
  close "SEND seed" .sample (Bound.ofWord 2 * sampleError s l u.cubeBits s.samples)
    { drawE := s.samples * (u.cubeBits + 1), drawNZ := s.samples, priced := .callersWord }
  planAnswers (2 * s.samples)
  closeNone "SEND answer"
  let a0 := first.agree
  let aj := A.once.agree
  let nuFirst ← planPositions a0
  let nuFurther ← planPositions aj
  needs (nuFirst != 0 && nuFurther != 0)
  let e0 := Bound.pow a0 nuFirst
  let ej := Bound.pow aj nuFurther
  close "LINK" .query (if e0.hi.lt ej.hi then ej else e0)
    { poss := nuFirst + nuFurther, logN := T.code.logN, priced := .callersWord }
  planListed T.code.logN (nuFirst + nuFurther)
  close "LINK phi" .field (fieldError s (clog2 T.code.ell))
    { drawE := clog2 T.code.ell, priced := .roundItself }
  pure (nuFirst, nuFurther)

/-! ## A finished plan and its verdict -/

/-- A finished plan. -/
structure Planned where
  set : Setting
  rounds : List PlanRound

/-- Runs a routine on an empty plan and finishes it. Refused if the routine refuses, or if the plan
ends in the middle of a prover's message. -/
def finish (s : Setting) (scope : Scope) (x : Planning Unit) : Except String Planned :=
  match x { set := s, scope := scope } with
  | .error e => .error e
  | .ok (_, p) =>
    if p.openBytes != 0 || p.openRoots != 0 || p.openAnswers != 0 then .error notAdmitted
    else .ok ⟨s, p.rounds.toList⟩

/-- Draws are capped. An element of the base field is made from the next words of the chain's
answer: a word that is not below p is passed over, and after six such words the element is 0. An
element of the extension field other than 0 is the first of two elements that is not 0, else 1.
Returns an upper bound on the chance that six words in a row fail, for an element of the extension
field. -/
def capped (s : Setting) : Binary :=
  let bits := bitsOf (s.p - 1)
  (Bound.ofWord s.degree * Bound.pow (Bound.ratio (2 ^ bits - s.p) (2 ^ bits)) 6).error

/-- The round's error with the distance from uniform of the field elements that it draws. `unit`:
the value of `capped`. -/
def wholeError (s : Setting) (unit : Binary) (r : PlanRound) : Binary :=
  if r.entry.drawE == 0 then r.error
  else
    let e := r.error.add (unit.mul (.ofNat (r.entry.drawE + r.entry.drawNZ)) .up) .up
    if r.entry.drawNZ != 0 then
      e.add (((Bound.ofWord 1 / Bound.pow (Bound.ofNat s.cardE) 2).error).mul
        (.ofNat r.entry.drawNZ) .up) .up
    else e

/-- True if the round holds at the target, work counted. An exact comparison. -/
def roundHolds (s : Setting) (unit : Binary) (r : PlanRound) : Bool :=
  (wholeError s unit r).le (Binary.twoTo ((r.entry.work : Int) - (s.target : Int)))

/-- True if all rounds that say the same two codes say the same rule and integer. -/
def oneChoice : List PricedChoice → Bool
  | [] => true
  | g :: gs =>
    (gs.all fun h => !(h.main == g.main && h.mask == g.mask) || (h.rule == g.rule && h.m == g.m)) &&
      oneChoice gs

/-- True if every round holds at the target, work counted. -/
def Planned.roundsHold (p : Planned) : Bool := p.rounds.all (roundHolds p.set (capped p.set))

/-- True if all rounds that say the same two codes say the same rule and integer (`oneChoice`). The
aim: all rounds of one stage are priced at one distance. A closeness term is cheap at a near
distance and positions are few at a far one: each price is true by itself, the two together are not.
The key of the test is the pair of codes, not the stage. So it is too strict: two stages of one plan
that share both codes must share the choice. By the comment in blocks/numbers/plan.h (judged), there
are parameter files, otherwise in order, that break this and are refused. Not reached: a number that
a round reads of another stage, and the lists that a stage's own sample and batching read. Such
rounds are priced on the caller's word. -/
def Planned.oneDistance (p : Planned) : Bool := oneChoice (p.rounds.filterMap (·.group))

/-- True if no round's word on how it was priced contradicts the round. -/
def Planned.wordsFit (p : Planned) : Bool := p.rounds.all (!·.wordFault)

/-- The plan's verdict: every round holds at the target, no word contradicts its round, and rounds
that say the same two codes say the same choice (`Planned.oneDistance`, with its limits). -/
def Planned.holds (p : Planned) : Bool := p.roundsHold && p.wordsFit && p.oneDistance

/-- Runs a routine on an empty plan and finishes it, and asks the plan's verdict. -/
def finishHeld (s : Setting) (scope : Scope) (x : Planning Unit) : Except String Planned := do
  let p ← finish s scope x
  if p.holds then pure p else throw notAdmitted

/-- True if some round has an error above 2 ^ -target with no work counted. If the plan holds, such
a round gets to the target only thanks to the bits of work that it is credited with. -/
def Planned.needsWork (p : Planned) : Bool :=
  let unit := capped p.set
  p.rounds.any fun r => !(wholeError p.set unit r).le (Binary.twoTo (-(p.set.target : Int)))

/-- The plan as it is written in a chain's parameter bytes. -/
def Planned.plan (p : Planned) : Fmt.Plan where
  field := .two
  salt := p.set.saltBytes
  nonce := p.set.nonceBytes
  posB := p.set.positionBytes
  samples := p.set.samples
  saved := 1
  entries := p.rounds.map (·.entry)

end OnBytes.Params
