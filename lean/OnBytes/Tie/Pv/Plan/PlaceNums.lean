-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Plan/PlaceNums.lean: the public numbers of every link of the proof's first chain, as
the records that the verifier's own reader makes from the three public files, and the places of a
link's lookups, own rounds, smallness test and last batching in that chain's plan.

Nothing is typed in: every number here is a field of a record that publicOf returns, or a length or
a place in the plan that firstPlan writes.

Main names:
  LinkNums: of one link: its kind ("L": a group of layers; "A": attention; "H": the head), its
    group, the record of its lookup on calls (Forest.Shape), the record of its smallness test
    (HTailF2, which holds the record f9 of the lookup on digits), the planner's record of its own
    rounds (LayerRounds, AttentionRounds inside the whole Attention.Plan, or HeadRounds), and the
    rows of its last batching.
  Chain1, chain1: the reader's record, the setting, the plan's rounds, the place of each link's
    three moments, and the links' numbers, from the three files.
  OurPlace, ourPlaces: for each link the stretches "lookupCalls", "chain", "rng", "lookupDigits",
    "batSigma" (and, at the head, "merge"), each with its first entry, counted from 1, and its
    number of entries.
  alone: the rounds that the planner's routine for a stretch writes when it is run by itself at the
    link's records.
  placeTests: by evaluation: each stretch of the chain's plan is, entry for entry, what alone gives.
  lawTests: by evaluation: (1) at every link what the last round batches is the record's number of
    linear claims and the smallness test's equationsF at the record's number of reads (the three
    plans define it so: the test computes their definitions anew, at the record as it ends up and
    at the plans' own functions for the reads); (2) when a
    link's routine is called for a moment, the planner's state has no open byte, root or answer and
    a request's scope (that the state's setting is the one of chain1 is by reading, not tested);
    (3) every record of a link of layers passes fullB: it has terms, routed
    experts, norms' instances and more than one bit of layers; (4) the layout has more than one bit
    of layers and routed experts, and the list of calls with terms is not empty.
  tailKey, ranTests: by evaluation: link by link, the kind, the group and the smallness test's
    record are those of the list of links that the verifier runs (linksOf), and the scalars that
    the link's rounds send are that list's number ns.
Limits: definitions and tests by evaluation. No theorem is stated. A stretch is found by marks and
lengths; that it is the stretch of a table that is written elsewhere is not said here. The rounds
between these stretches (sendings, the code switch, foldings) are not described here. Links of one
kind may have the same rounds, so placeTests does not
tell one group's records from another's; ranTests does, as far as tailKey reads the record: the
numbers and the matrices' names, sizes and kinds, not the tables and not the shapes of the arrays.
The record of a smallness test is the one before the verifier closes its list of tables.
roundsOf, marked and marksOf are taken from TestPlanSizes.lean in this folder, which holds
definitions alone. The program does not import this file.

-/
import OnBytes.Tie.Pv.Plan.TestPlanSizes
import OnBytes.Model.VerifyLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Plan

open OnBytes.Params (PlanRound Planning Setting settingOf planForest planSmall planAttentionOwn
  planLayerOwn planHeadOwn planHeadEnd planBatSigma firstPlan proofSized orRefuse)
open OnBytes.Model (forestSize smallSize)
open OnBytes.Model.Verify (Public publicOf linkRounds shapesOf linksOf layerNumbers borderOf)

/-- The reader's records of a link. -/
structure Records where
  kind : String
  group : Nat
  /-- the lookup on calls -/
  calls : OnBytes.Model.Forest.Shape
  /-- the smallness test; its field f9 is the record of the lookup on digits -/
  tail : OnBytes.Model.HTailF2
  /-- at a link of layers: the planner's record of its own rounds -/
  lay : Option OnBytes.Params.LayerRounds := none
  /-- at an attention link: its plan record; its field own is the planner's record -/
  att : Option OnBytes.Attention.Plan := none
  /-- at the head: the planner's record of its own rounds -/
  head : Option OnBytes.Params.HeadRounds := none
  /-- what the reader's records say that the last round batches -/
  claims : Nat
  /-- the plan's number of linear claims -/
  nLin : Nat
  /-- the plan's number of reads of the smallness test -/
  reads : Nat

/-- A link's public numbers: the reader's own records, whole, and its rounds. -/
structure LinkNums extends Records where
  link : Nat
  /-- the rows of the link's last batching, read off its last round -/
  rows : Nat
  /-- the rounds of the link's three moments -/
  l0 : List PlanRound
  l1 : List PlanRound
  l2 : List PlanRound

/-- The record of the lookup on digits. -/
def LinkNums.digits (n : LinkNums) : OnBytes.Model.Forest.Shape := n.tail.f9

/-- The reader's records of a link, by the case split of linkRounds. -/
def recordsOf (X : Public) (link : Nat) : Option Records :=
  let step := if X.p4 then 2 else 1
  let g := link / step
  if link == step * X.NGr then
    some { kind := "H", group := 0, calls := X.HLy.fs, tail := X.H.tl, head := some (X.H.own X.hS),
           claims := (X.H.own X.hS).rows, nLin := X.H.nLin,
           reads := OnBytes.Model.Head.readsH X.hS X.HLy (borderOf X.y) }
  else if link % step == 0 then
    X.G[g]?.map fun hp =>
      { kind := "L", group := g, calls := X.y.fo, tail := hp.tl,
        lay := some (layerNumbers X.layers hp g), claims := hp.nBatched, nLin := hp.nLin,
        reads := OnBytes.Model.Layer.readsCount X.y X.layers.rd g }
  else
    X.A[g]?.map fun a =>
      { kind := "A", group := g, calls := a.fs, tail := a.seam.tl, att := some a,
        claims := a.own.rows, nLin := a.nLin,
        reads := OnBytes.Attention.tableReads a.S (OnBytes.Attention.Counts.of a.S) }

/-- The proof's first chain at an example. -/
structure Chain1 where
  X : Public
  s : Setting
  /-- the plan's rounds -/
  rounds : List PlanRound
  /-- the place, from 0, of the first round of moment m of link l, at 3 l + m -/
  marks : List Nat
  /-- the marks themselves: a mark's entry has the bytes and answers that were open at its place -/
  markRounds : List PlanRound
  links : List LinkNums

/-- From the three public files. -/
def chain1 (pol KL layout : ByteArray) : Except String Chain1 := do
  let X ← publicOf pol KL (some layout)
  let s := settingOf X.P.frame
  let (_, shapes) ← shapesOf X (some layout)
  let z ← orRefuse (proofSized X.P.frame shapes.sub)
  let p ← firstPlan z (marked shapes.sub)
  let links ← (List.range ((if X.p4 then 2 else 1) * X.NGr + 1)).mapM fun link => do
    let r ← orRefuse (recordsOf X link)
    let l0 ← roundsOf s (linkRounds X link 0)
    let l1 ← roundsOf s (linkRounds X link 1)
    let l2 ← roundsOf s (linkRounds X link 2)
    pure { r with link, rows := (l2.getLast?.map (·.entry.rows)).getD 0, l0, l1, l2 : LinkNums }
  pure { X, s, rounds := p.rounds.filter fun r => !r.entry.name.startsWith "MARK",
         marks := (marksOf p.rounds 0).map (·.2),
         markRounds := p.rounds.filter fun r => r.entry.name.startsWith "MARK", links }

/-- A stretch of the chain's plan. first: its first entry, counted from 1. -/
structure OurPlace where
  link : Nat
  fam : String
  first : Nat
  entries : Nat
  deriving BEq, Repr

/-- The rounds that the planner's routine for a stretch writes when run by itself at the link's
records. The head's merge is what planHeadEnd writes before its last round. -/
def alone (s : Setting) (n : LinkNums) (fam : String) : Option (Except String (List PlanRound)) :=
  if fam == "lookupCalls" then some (roundsOf s (planForest (forestSize n.calls)))
  else if fam == "chain" then
    (n.lay.map fun x => roundsOf s (planLayerOwn x)) <|>
      (n.att.map fun a => roundsOf s (planAttentionOwn a.own)) <|>
      (n.head.map fun x => roundsOf s (planHeadOwn x))
  else if fam == "merge" then n.head.map fun x => (roundsOf s (planHeadEnd x)).map List.dropLast
  else if fam == "rng" then some (roundsOf s (planSmall (smallSize n.tail) 0))
  else if fam == "lookupDigits" then some (roundsOf s (planForest (forestSize n.digits)))
  else if fam == "batSigma" then some (roundsOf s (planBatSigma n.rows))
  else none

/-- The stretches of one link. -/
def placesOfLink (c : Chain1) (n : LinkNums) : Except String (List OurPlace) := do
  let n0 := (← roundsOf c.s (planForest (forestSize n.calls))).length
  let n2 := (← roundsOf c.s (planForest (forestSize n.digits))).length
  let b := fun m => c.marks.getD (3 * n.link + m) 0
  let mid := n.l2.length - n2 - 1
  pure ([{ link := n.link, fam := "lookupCalls", first := b 0 + 1, entries := n0 },
         { link := n.link, fam := "chain", first := b 0 + n0 + 1, entries := n.l0.length - n0 },
         { link := n.link, fam := "rng", first := b 1 + 1, entries := n.l1.length },
         { link := n.link, fam := "lookupDigits", first := b 2 + 1, entries := n2 }] ++
        (if mid == 0 then [] else
          [{ link := n.link, fam := "merge", first := b 2 + n2 + 1, entries := mid }]) ++
        [{ link := n.link, fam := "batSigma", first := b 2 + n.l2.length, entries := 1 }])

/-- The stretches of all links, in the chain's order. -/
def ourPlaces (c : Chain1) : Except String (List OurPlace) :=
  (c.links.mapM (placesOfLink c)).map List.flatten

/-- The entries of a stretch. -/
def stretch (c : Chain1) (p : OurPlace) : List Fmt.Entry :=
  ((c.rounds.drop (p.first - 1)).take p.entries).map (·.entry)

/-- By evaluation: (1) every stretch lies inside the plan and the stretches follow each other;
(2) alone names a routine for each stretch, and the stretch is, entry for entry, what that routine
writes by itself; (3) the rows of each link's last batching are what the reader's records say. At
"batSigma" test (2) compares the round with itself, since n.rows is read off that round: there the
content is in test (3). -/
def placeTests (c : Chain1) : Except String (List Bool) := do
  let ps ← ourPlaces c
  let ordered := (ps.zip (ps.drop 1)).all fun x => x.1.first + x.1.entries ≤ x.2.first
  let inside := ps.all fun p => 1 ≤ p.first && p.first + p.entries ≤ c.rounds.length + 1
  let same ← ps.mapM fun p => do
    match c.links[p.link]? with
    | none => pure false
    | some n =>
      match alone c.s n p.fam with
      | none => pure false
      | some r => pure ((← r).map (·.entry) == stretch c p)
  pure [ordered && inside, same.all id,
        c.links.all fun n => n.claims == n.rows]

/-- The record has terms, routed experts, instances of norms and more than one bit of layers. -/
def fullB (x : OnBytes.Params.LayerRounds) : Bool :=
  x.withTerms && x.routed && x.lNI != 0 && decide (1 < x.ll)

/-- Four tests on public numbers. A mark is written by closeNone, which refuses if a root is open
and puts the open bytes and answers into the mark's entry: so a mark with neither shows a state
without an open byte, root or answer. -/
def lawTests (c : Chain1) : List Bool :=
  [c.links.all fun n => n.claims == n.nLin + n.tail.equationsF n.reads,
   c.markRounds.length == 3 * c.links.length &&
     c.markRounds.all fun r => r.entry.msg == 0 && r.entry.answers == 0 && r.scope == .request,
   c.links.all fun n => n.lay.all fullB,
   decide (1 < c.X.y.h.ll) && c.X.y.h.p3 && !c.X.layers.rd.tscCalls.isEmpty]

/-- What is compared of a smallness test's record. -/
def tailKey (tl : OnBytes.Model.HTailF2) :
    List Nat × List (String × List Nat) × List (List Nat) :=
  ([tl.tau, tl.lidb, tl.mz, tl.NM, tl.foldColumns, tl.f9.v, tl.f9.d, tl.f9.NT, tl.ft.size],
   tl.mats.toList.map (fun M => (M.name, [M.m, M.k, M.kind, M.foreign.getD 0, M.ttOff])) ++
     tl.ft.toList.map (fun f => (f.name, [f.K, f.a, f.m, f.wp])),
   [tl.off.toList, tl.col0.toList, tl.gtTree.toList, tl.gtRow.toList, tl.kTX.toList,
    tl.f9.pub.toList, tl.nUF.toList, tl.tabFirst.toList, tl.tabLen.toList])

/-- By evaluation: the list of links that the verifier runs has as many links; link by link its
kind, group and smallness test's record (tailKey) are ours, and its number of scalars is what the
link's rounds send. The request's tokens, which no public number reads, are left empty. -/
def ranTests (c : Chain1) : Except String (List Bool) := do
  let L ← linksOf c.X default
  pure [L.size == c.links.length,
        c.links.all fun n => (L[n.link]?).any fun x =>
          x.kind == (if n.kind == "L" then 0 else if n.kind == "A" then 1 else 2) &&
            x.g == n.group && tailKey x.tl == tailKey n.tail,
        c.links.all fun n => (L[n.link]?).any fun x => x.ns == sentBy (n.l0 ++ n.l1 ++ n.l2)]

end OnBytes.Tie.Pv.Plan
