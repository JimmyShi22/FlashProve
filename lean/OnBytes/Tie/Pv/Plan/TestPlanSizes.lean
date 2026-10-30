-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Plan/TestPlanSizes.lean: what the tests of the written lists of
OnBytes/Tie/Pv/Plan/PlanSizes.lean and Cb/Pv/Head/Sizes.lean compute.

From the three public files of an example the verifier's own reader (publicOf) and planner
(linkRounds, firstPlan) give the rounds of every sub-proof and their places in the plan of the
proof's first chain. This file cuts the sumchecks behind the lookups out of these rounds. The tests
themselves are in TestPlanSizesSmall.lean and
TestPlanSizesFull.lean: lines "#guard", which Lean's interpreter evaluates
when the file is compiled.

How a place in the chain is found. The plan of the first chain is made with a mark before each call
of a sub-proof's routine: a round without a message and without a draw, named MARK. A mark's place,
less the marks before it, is the place of the first round that the routine adds.

How a bound is compared. A round's bound is printed as a quotient k/|E| or k/(|E|-1) if it is the
bound that the planner's own arithmetic gives for that quotient.

What is tested: (1) every group of layers has seven such sumchecks, every attention eight, the head
five; (2) kind by kind, they are the written lists' members for that example, in all fields; (3) the
head's lists in Cb/Pv/Head/Sizes.lean agree with these, and its list of the head's other rounds with
the plan; (4) every round behind a lookup has the bound that the lists' comments state; (5) the last
round of every link's sub-proof is the written list's closing draw, and closeRows has the different
numbers of rows of that list.
Limits: it is not claimed that a bound bounds anything. No theorem is stated.
The program does not import this file.

-/
import OnBytes.Model.VerifyChains
import OnBytes.Tie.Pv.Plan.PlanKits
import OnBytes.Tie.Pv.Plan.PlanSizes
import Cb.Pv.Head.Sizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Plan

open OnBytes.Params (PlanRound Planning Setting Binary Bound Subproofs finish closeNone settingOf
  planForest planSmall ForestSize SmallSize firstPlan proofSized orRefuse)
open OnBytes.Model (forestSize smallSize)
open OnBytes.Model.Verify (Public publicOf linkRounds shapesOf)

/-- The rounds that a routine plans in a request's scope. -/
def roundsOf (s : Setting) (x : Planning Unit) : Except String (List PlanRound) :=
  (finish s .request x).map (·.rounds)

/-- The number b * n, rounded to the nearest natural number. -/
def nearest (b : Binary) (n : Nat) : Nat :=
  if 0 ≤ b.e then b.m * n * 2 ^ b.e.toNat
  else (b.m * n + 2 ^ ((-b.e).toNat - 1)) / 2 ^ (-b.e).toNat

/-- A round's error as text. -/
def errorText (s : Setting) (r : PlanRound) : String :=
  if r.error.isZero then "0"
  else
    let k := nearest r.error s.cardE
    if r.entry.drawNZ != 0 && (Bound.ratio k (s.cardE - 1)).error == r.error then
      s!"{k}/(|E|-1)"
    else if (Bound.ratio k s.cardE).error == r.error then s!"{k}/|E|"
    else s!"m={r.error.m} e={r.error.e}"

/-- The elements of the extension field that rounds send. -/
def sentBy (l : List PlanRound) : Nat := l.foldl (fun n r => n + r.entry.msg / 24) 0

/-- The sub-proofs with a mark before each call of their routine. -/
def marked (sub : Subproofs) : Subproofs :=
  { sub with plan := fun l m => do
      closeNone s!"MARK\t{l}\t{m}"
      sub.plan l m }

/-- The marks of a list of rounds, each with its place less the marks before it. -/
def marksOf : List PlanRound → Nat → List (String × Nat)
  | [], _ => []
  | r :: rs, i =>
    if r.entry.name.startsWith "MARK" then (r.entry.name, i) :: marksOf rs i
    else marksOf rs (i + 1)

/-- The kind of a link ("L": layers; "A": attention; "H": the head), its group, and the sizes of its
lookup and of its smallness test. -/
def looksOf (X : Public) (link : Nat) : Option (String × Nat × ForestSize × SmallSize) :=
  let step := if X.p4 then 2 else 1
  let g := link / step
  if link == step * X.NGr then some ("H", 0, forestSize X.HLy.fs, smallSize X.H.tl)
  else if link % step == 0 then
    X.G[g]?.map fun hp => ("L", g, forestSize X.y.fo, smallSize hp.tl)
  else X.A[g]?.map fun a => ("A", g, forestSize a.fs, smallSize a.seam.tl)

/-- The sumchecks of a list of rounds. i: the place of the list's first round in the moment's list.
c: the scalars sent before it. base: the place of the moment's first round in the chain's plan. -/
def cutPsc (full : Bool) (link group moment base : Nat) :
    List PlanRound → Nat → Nat → Option PscAt → List PscAt
  | [], _, _, cur => cur.toList
  | r :: rs, i, c, cur =>
    let n := r.entry.msg / 24
    let go := cutPsc full link group moment base rs (i + 1) (c + n)
    if r.entry.name == "PSC epsilon" then
      cur.toList ++ go (some { full, link, group, moment, place := i, chain := base + i, slot := c,
                               riders := n - 1, sent := [], inY := 0, values := 0, line := false })
    else if r.entry.name == "PSC round" then go (cur.map fun x => { x with sent := x.sent ++ [n] })
    else if r.entry.name == "PSC Y" then go (cur.map fun x => { x with inY := n })
    else if r.entry.name == "PSC values" then go (cur.map fun x => { x with values := n })
    else if r.entry.name == "LINE" then (cur.map fun x => { x with line := true }).toList ++ go none
    else cur.toList ++ go none

/-- The rounds of a list that belong to no sumcheck and are no LINE, as the head's list has them. -/
def cutOther (full : Bool) (moment base : Nat) :
    List PlanRound → Nat → Nat → List Cb.Pv.Head.OtherAt
  | [], _, _ => []
  | r :: rs, i, c =>
    let n := r.entry.msg / 24
    let rest := cutOther full moment base rs (i + 1) (c + n)
    if r.entry.name.startsWith "PSC" || r.entry.name == "LINE" then rest
    else { full, moment, place := i, chain := base + i, name := r.entry.name, scalars := n,
           slot := c, draws := r.entry.drawE, rows := r.entry.rows } :: rest

/-- The bound that the lists' comments state for a round, as errorText prints it; none for a round
of which they say nothing. -/
def saidBound (r : PlanRound) : Option String :=
  let e := r.entry
  if e.name == "PSC epsilon" || e.name == "LINE" then some "1/|E|"
  else if e.name == "PSC round" then some s!"{e.msg / 24}/|E|"
  else if e.name == "PSC Y" then some s!"{e.msg / 24}/(|E|-1)"
  else if e.name == "PSC values" then some "0"
  else if e.name == "ZERO" || e.name == "JOIN" then some s!"{e.drawE}/|E|"
  else if e.name == "BAT-sigma" then some (if e.rows == 1 then "0" else s!"{e.rows - 1}/|E|")
  else none

/-- What is computed of a link. -/
structure LinkCut where
  kind : String
  psc : List PscAt
  other : List Cb.Pv.Head.OtherAt
  bounds : Bool
  close : Option CloseAt

/-- All links of an example. -/
def cutsOf (full : Bool) (pol KL layout : ByteArray) : Except String (List LinkCut) := do
  let X ← publicOf pol KL (some layout)
  let s := settingOf X.P.frame
  let (_, shapes) ← shapesOf X (some layout)
  let z ← orRefuse (proofSized X.P.frame shapes.sub)
  let p ← firstPlan z (marked shapes.sub)
  let marks := (marksOf p.rounds 0).map (·.2)
  (List.range ((if X.p4 then 2 else 1) * X.NGr + 1)).mapM fun link => do
    let (kind, group, look, small) ← orRefuse (looksOf X link)
    let l0 ← roundsOf s (linkRounds X link 0)
    let l1 ← roundsOf s (linkRounds X link 1)
    let l2 ← roundsOf s (linkRounds X link 2)
    let n0 := (← roundsOf s (planForest look)).length
    let n2 := (← roundsOf s (planSmall small 1)).length
    let b := fun m => marks.getD (3 * link + m) 0
    let c0 := sentBy (l0.take n0)
    let c2 := sentBy l0 + sentBy l1 + sentBy (l2.take n2)
    pure { kind := kind
           psc := cutPsc full link group 0 (b 0) (l0.drop n0) n0 c0 none ++
             cutPsc full link group 2 (b 2) (l2.drop n2) n2 c2 none
           other := cutOther full 0 (b 0) (l0.drop n0) n0 c0 ++
             cutOther full 1 (b 1) l1 0 (sentBy l0) ++ cutOther full 2 (b 2) (l2.drop n2) n2 c2
           bounds := (l0.drop n0 ++ l2.drop n2).all fun r =>
             (saidBound r).all (· == errorText s r)
           close := l2.getLast?.map fun r =>
             { full, link, place := l2.length - 1, chain := b 2 + (l2.length - 1),
               rows := r.entry.rows } }

/-- The computed sumchecks, kind by kind, in the form of allAt. -/
def byKind (l : List LinkCut) : List (String × List PscAt) :=
  [("L", 7), ("A", 8), ("H", 5)].flatMap fun k =>
    (List.range k.2).map fun j =>
      (s!"{k.1}{j + 1}", l.filterMap fun x => if x.kind == k.1 then x.psc[j]? else none)

/-- A member of the head's lists as a member of this folder's. -/
def ofHead (a : Cb.Pv.Head.PscAt) : PscAt :=
  { full := a.full, link := a.link, group := 0, moment := a.moment, place := a.place,
    chain := a.chain, slot := a.slot, riders := a.riders, sent := a.sent, inY := a.inY,
    values := a.values, line := a.line }

/-- The five tests at an example. -/
def tests (full : Bool) (pol KL layout : ByteArray) : Except String (List Bool) := do
  let l ← cutsOf full pol KL layout
  let here := fun (x : List PscAt) => x.filter (·.full == full)
  pure
    [l.all fun x => x.psc.length == (if x.kind == "L" then 7 else if x.kind == "A" then 8 else 5),
     byKind l == allAt.map (fun x => (x.1, here x.2)),
     [Cb.Pv.Head.atSquares, Cb.Pv.Head.atTV, Cb.Pv.Head.atTN, Cb.Pv.Head.atTH,
       Cb.Pv.Head.atMerge].map (·.map ofHead) == [atH1, atH2, atH3, atH4, atH5] &&
       (l.filter (·.kind == "H")).flatMap (·.other) ==
         Cb.Pv.Head.others.filter (·.full == full),
     l.all (·.bounds),
     l.map (·.close) == (closeAt.filter (·.full == full)).map some &&
       closeRows == (closeAt.map (·.rows)).eraseDups]

end OnBytes.Tie.Pv.Plan
