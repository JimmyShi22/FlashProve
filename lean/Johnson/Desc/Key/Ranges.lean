-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Ranges.lean: the proximity test on the group of the lookups' own message ("the
ranges' test") in a key file's first chain: the numbers of its place, its seat, and what the seat
asks beside the test itself. Definitions only, all computable; nothing is proved here.

The test is the proximity test's own block (`K12.proximityTestKind K12.guardedProximityTestParts`: Johnson/Desc/K12/Frame.lean,
JoinGuarded.lean). It runs at a record of its own (`K12.T12`), which is made when the block is entered
and dropped when it is left (`Block.inside`). No line of the test is written here. What is here is
the key file's own: how that record is made of the chain's state, what is asked before the test
runs, and the place's numbers.

Main names.
  rangesNumbers: the place's numbers, from what the planner makes of the three public files.
  RangesLaid: what a chain's state hands the test.
  rangesPlace, rangesParams: the place; the test's parameters at the place's numbers.
  rangesRecord: the test's record, made of what is handed.
  testEnded: the test has run to its end, as its record shows. Whoever writes the record back
    asks it.
  asksOnPlan: asked on the plan. asksOnRecord: asked on the record, in front of the test.
  behindBatching, layoutIsStage: two helpers of asksOnRecord.
  enterAndAsk: make the record, then ask.
  rangesTest: the block, at any state: enter and ask; the test; leave.

Why the seat asks. The statements on the proximity test that are stated and proved under
Johnson/Desc/K12/Law/ take tests with code as premises. A premise that the
block asks is had from the block's yes. One that nobody asks would rest on an evaluation alone.
  asksOnPlan p is a conjunct of the block's test on the plan. Four clauses:
    p.early: the first fold's mask has come earlier;
    p.answers = 1: one answer to a sample;
    `H2K.First.cutOk p`: the first stage's rounds are cut as those statements read them;
    `H2K.Pub.spendOk p`: what a fold's rounds and the base case's first round send and draw, and
      the stages' sizes.
  asksOnRecord p t asks, in this order:
    the group, its layout and a stage are there;
    the record names the message that holds the first fold's mask;
    `H2K.Pub.pubOk`: the record's codes are the place's;
    `Means.combineAt`: every row that the batching takes lies on the group's tables;
    layoutIsStage: the layout's four numbers are the first stage's;
    `H2K.First.gpOk`: the group is what the first switch opens;
    `H2K.First.labelsOk`: the declared openings bear the numbers of the book's trees.
  None of these reads a value that a prover sends. They read shapes, numbers and places, and of a
  row on which tables its summands stand.

Asked twice. `K12.guardedProximityTestParts` itself asks p.early, p.answers = 1 and cutOk on the plan, and pubOk,
combineAt, gpOk and labelsOk on the record. Here they are asked once more, in front. Nothing hangs
on the second asking.

Where it is called. asksOnPlan is called at two places: in rangesTest's test on the plan, and in
three clauses of the file's test on the plan (Johnson/Desc/Key/FileOk.lean), for the file's other
three proximity tests. Three of its four clauses are the proximity test's own. The fourth, spendOk,
IS ASKED BY NO OTHER TEST: it follows from that test's yes by a theorem
(`H2K.Made.spendOk_of_planOk`, Johnson/Desc/K12/Law/SpendMade.lean), not by a test.

Not asked. That the first fold sends its own mask just where the record names none
(`p.nums.ownMask` against `t.mask`): here the record must name one. Nothing on the values in
rows or messages. Nothing on the ledgers of mask entries. At the file's other three proximity
tests asksOnRecord is not asked.

Limits. rangesNumbers: no entry and no declared round of the plan goes into rows, work, stages,
ownMask, idx, answers or early. They come of the planner's sized records, by the arguments of the
planner's own call for this test (OnBytes/Plan/Ranges.lean, `rangesPlan`; the chain's scope is
"once": OnBytes/Plan/KeyOneTime.lean). So the file's test of the blocks' rounds against the plan's
entries can fail at this place. Off the plan's entries come start (where the chain's first round
named "BAT" stands; the whole stretch is held against the names that the stages ask) and free (the
roots that the entries in front receive). first comes of both: of the trees that the chain's
sendings send, laid along the plan (`treesSent`, `onceOpens`). The cut by names for a proof file's
plans (`H2U.testCutAt`) reads those plans alone, so its five lines on names are said here once more,
over `H2U.batPlaces`, `towerLen` and `towerNames`. start is the chain's FIRST round named "BAT":
that this round is this test's is read off the planner's routine, not held.
behindBatching lays a row without coefficients: gpOk and labelsOk read of the batched row only
whether it has a kept form, which `K12.guardedProximityTestParts` asks behind its batching.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.Law.SpendOk
import Johnson.Desc.K12.Law.FirstCut
import Johnson.Desc.Means.TestsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params OnBytes.Slice Johnson.G.OfPlan
open VerifiableInference.Desc (Block Place need)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)

/-! ## The place's numbers -/

/-- **The numbers of the ranges' test's place**, from m: what the planner makes of the three public
files, with the chains' sendings.
  chain: 1. start, free: off the plan's entries (see the head's Limits).
  rows: `Wf.rowsBatched`: the own message's sample rows and what the lookups leave.
  work: the setting's bits of work for a round of positions, at the scope "once".
  stages: the sized stages (the two codes' log-length, message length and tail; k; h; t).
  ownMask: the first fold sends its own mask just where masks do not ride.
  first: the trees that the first round of positions opens: the head of the rule's list for a
    key's first chain (Johnson/G/RoundsOfPlan.lean, `onceOpens`): the own message's tree, in which
    the first fold's mask rides.
  firstTree: 0: the chain continues no other.
  idx: the numbers of the stages' codes in the chain's lists of codes.
  firstGroup: 1: the running record has one group in front of the test: the test's own.
  answers: the setting's answers to a sample. early: masks ride. -/
def rangesNumbers (m : Made) : Except String H2U.PlaceNums := do
  let C := m.p.chains.made
  let z := C.sized.key.ranges
  let x := z.x
  let P := m.p.chains.key.oneTime.given.plan
  let es := P.rounds
  let ts ← treesSent "key file, first chain" m.key.1 P []
  let first ← match (onceOpens ts).head? with
    | some l => pure l
    | none =>
      throw "the ranges' test's numbers: the rule has no list for the first round of positions"
  let start ← match (H2U.batPlaces es).head? with
    | some i => pure i
    | none => throw "the ranges' test's numbers: the plan has no round BAT"
  unless decide (2 ≤ x.stages.length) &&
      ((es.drop start).take (1 + H2U.towerLen x.stages)).map (·.name) ==
        "BAT" :: H2U.towerNames x.stages do
    throw "the ranges' test's numbers: fewer than two stages, or a round's name parts from what \
      the stages ask"
  pure
    { chain := 1, start := start
      nums :=
        { rows := Wf.rowsBatched x z.matrix, work := C.sized.set.workOf .query .once,
          stages := z.test.stages.map H2U.stageNums
          ownMask := !x.choice.masksRide, first := first,
          free := ((es.take start).map (·.roots)).foldl (· + ·) 0, firstTree := 0 }
      idx := x.stages.map fun s => (s.code, s.maskCode), firstGroup := 1,
      answers := C.sized.set.samples, early := x.choice.masksRide }

/-! ## The seat -/

/-- What a chain's state hands the test. -/
structure RangesLaid where
  /-- the statement, the book of trees and the count of roots -/
  d : _root_.Desc.Plain.DState Unit
  /-- the group under test -/
  grp : Nat
  /-- the message that holds the first fold's mask, if it came earlier -/
  rider : Option Nat

/-- The place: chain 1, behind the lookups. -/
def rangesPlace : Place := ⟨1, none, 5, .K12⟩

/-- The test's parameters at the place's numbers. -/
def rangesParams (N : H2U.PlaceNums) : P12 := H2U.proximityTestParametersAt rangesPlace N

/-- The test's record, made of what is handed. -/
def rangesRecord {σ : Type} (laid : σ → Except String RangesLaid) (s : σ) : Except String T12 :=
  (laid s).map fun l =>
    { st := l.d.st, book := l.d.book, roots := l.d.roots, g := l.grp, pass := .nothing,
      mask := l.rider }

/-- **The test has run to its end, as its record shows.** Nothing passes from part to part any more;
the group under test is there; it and every group made since have begun their test and hold no open
row; every message without a sample is spent as a mask. "Nothing passes" alone would not do: that is
also how the record is made. The last clause is what the base case leaves: its masking message is
spent by no other part. -/
def testEnded (t : T12) : Bool :=
  (match t.pass with
    | .nothing => true
    | _ => false) &&
  decide (t.g < t.st.groups.size) &&
  ((t.st.groups.toList.drop t.g).all fun G => G.inRun && G.rows.isEmpty) &&
  t.st.oracles.all fun o => o.sampled || o.spentAsMask

/-! ## What the seat asks -/

/-- Asked on the plan. -/
def asksOnPlan (p : P12) : Bool :=
  p.early && p.answers == 1 && H2K.First.cutOk p && H2K.Pub.spendOk p

/-- The record behind the batching, at a row without coefficients. -/
def behindBatching (t : T12) (G : Group) (L : GroupLayout) : T12 :=
  { t with st := begun t.st t.g G, pass := .claim {} L }

/-- The layout's four numbers are the first stage's. k is held in the form a.h + (a.k - a.h), in
which the statements take it: that is a.k where a.h ≤ a.k, which the test's own test on the plan
asks of every stage; where a.k < a.h it would be a.h. -/
def layoutIsStage (a : Fmt.M1.Stage) (L : GroupLayout) : Bool :=
  L.k == a.h + (a.k - a.h) && L.h == a.h && 2 ^ L.logEll == a.C.l && 2 ^ L.logEllZk == a.Z.l

/-- Asked on the record, in front of the test. -/
def asksOnRecord (p : P12) (t : T12) : Except String Unit :=
  match t.st.groups[t.g]?, t.st.layout t.g, p.nums.stages with
  | some G, some L, a :: _ => do
    need "the seat asks: the record names the message that holds the first fold's mask"
      t.mask.isSome
    need "the seat asks: the record's codes are the place's (pubOk)" (H2K.Pub.pubOk p t.st.codes)
    need "the seat asks: every row that the batching takes lies on the group's tables (combineAt)"
      (Means.combineAt (begun t.st t.g G) t.g ⟨L, runRows t.st G⟩)
    need "the seat asks: the layout's four numbers are the first stage's" (layoutIsStage a L)
    need "the seat asks: the group is what the first switch opens (gpOk)"
      (H2K.First.gpOk p (behindBatching t G L))
    need "the seat asks: the declared openings bear the book's trees' numbers (labelsOk)"
      (H2K.First.labelsOk p (behindBatching t G L))
  | _, _, _ => .error "the seat asks: the group, its layout and a stage are there"

/-- Make the record, then ask. -/
def enterAndAsk {σ : Type} (laid : σ → Except String RangesLaid) (p : P12) (s : σ) :
    Except String T12 :=
  (rangesRecord laid s).bind fun t => (asksOnRecord p t).map fun _ => t

/-- **The ranges' test at any state, with what the seat asks.** laid: what the state hands the test.
back: how the test's record is written back. -/
def rangesTest {σ Cl : Type} (laid : σ → Except String RangesLaid)
    (back : σ → T12 → Except String σ) (N : H2U.PlaceNums) : Block σ Cl :=
  { Block.inside (enterAndAsk laid (rangesParams N)) (proximityTestKind guardedProximityTestParts (rangesParams N)) back with
    name := "rng"
    planOk :=
      (Block.inside (enterAndAsk laid (rangesParams N))
        (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl) back).planOk &&
      asksOnPlan (rangesParams N) }

end VerifiableInference.Desc.Key
