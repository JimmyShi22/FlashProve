-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Shape/StepStatement.lean: THE DECISION OF THE MERGE OF THE CLAIMS ON THE WEIGHTS AS
ONE TEST WITH CODE AND ONE UPDATE ON THE FIRST CHAIN's SHAPE (`ChainSh`, `chainSh`,
Johnson/Desc/First/Shape/Chain.lean): definitions, and STATEMENTS ALONE: three, each a definition of
a proposition. NOTHING IS PROVED IN THIS FILE, and none of the three is one of the library's goals:
they are lemmas' statements. The text is the verifier's; no prover is named.

THE DEFINITIONS, all with code, on shapes alone: no field element stands in any.
  `facFitsSh`, `claimFitsSh`   the kind's test on a claim's sizes (`claimFits`,
                               Johnson/Desc/First/Fork/MergeKind.lean), on the claim's shape
  `onRowsSh`, `rowPartSh`      the shape of what is left of a claim when the columns are bound
                               (`wsRowPart`, OnBytes/Model/Weights.lean), of the claim's shape
  `mergeGuardB P a`            THE TEST: no mark of failure; the head's link, open; nothing owed;
                               the claim and what the head heard are laid; the claim's sizes fit;
                               the ledger's arrays have their size; the mark at the claim's value's
                               slot is set; the end value's slot is there and free; the slots come
                               out at the plan's number
  `ledUpd`, `mergeShOf`, `mergeUpd P a`   THE UPDATE: nothing owed; the ledger's shape with
                               2 lk + 3 slots more taken, the plan's number of claims, and one mark
                               more; in the head's own fields: the shape of what the merge leaves,
                               the ledger's shape in front kept aside, the next free slot
  `StateReady P s`             the twelve clauses on the state itself: no mark, and the eleven
                               premises on the state of `HeadMergeDecideReturns`
                               (Johnson/Desc/K11/Returns/Statement.lean), in its own words

THE STATEMENTS.
  `GuardIsReady`    the test at a state's shape says yes just where `StateReady` holds
  `MergeCarries`    at rounds that pass the step's own test: where the decision returns and the test
                    says yes at the shape in front, the update of that shape IS the shape behind
  `MergeReturns`    at such rounds: where the test says yes at the shape in front, the decision
                    returns

Limits. No state is shown at which the test says yes. The kind tests no value: so no test on values
stands beside the test on the shape. At the bare decision: nothing on a seat. Nothing on any
property.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.K11.Returns.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.ShapeStep
open OnBytes.Model (WsLay WsGrp)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide claimFits)
open Johnson.Desc.First.ForkMerge.Returns (mergeEndSlot)

/-- The kind's test on one factor's sizes, on the three sizes. -/
def facFitsSh (x : Nat × Nat × Nat) (g : WsGrp) : Bool :=
  if g.cls == 'E' then x.1 == g.o && x.2.1 == g.z && x.2.2 == 0
  else x.2.2 == g.R && x.1 == 0 && x.2.1 == 0

/-- The kind's test on a claim's sizes, on the claim's shape. -/
def claimFitsSh (lay : WsLay) (c : WsClaimSh) : Bool :=
  match lay.U[c.ui]? with
  | none => false
  | some u => c.f.length == u.g.length && (c.f.zip u.g).all fun y => facFitsSh y.1 y.2

/-- The three sizes of the part of a factor that is left to the rows. -/
def onRowsSh (x : Nat × Nat × Nat) (g : WsGrp) : Nat × Nat × Nat :=
  if g.cls == 'E' then
    (x.1, ((List.range g.z).filter fun i => !g.takenBit (g.z - 1 - i)).length, 0)
  else if g.aTaken then (0, 0, 0)
  else (0, 0, x.2.2)

/-- The shape of what is left of a claim when the columns are bound. -/
def rowPartSh (lay : WsLay) (c : WsClaimSh) : RecSh :=
  match lay.U[c.ui]? with
  | none => { ui := c.ui, f := [] }
  | some u => { ui := c.ui, f := (c.f.zip u.g).map fun y => onRowsSh y.1 y.2 }

/-- **THE TEST.** -/
def mergeGuardB (P : HeadMergeP) (a : ChainSh) : Bool :=
  !a.marked && a.here == 3 &&
    (match a.rowsOwed with
      | none => true
      | some r => r == 0) &&
    match a.led, a.head with
    | some L, some h =>
      match h.claim, h.xEnd with
      | some c, some e =>
        claimFitsSh P.lay c && sizedB L && L.got.getD (e + 1) false &&
          decide (L.next + 2 * P.lay.lk + 2 < L.ns) &&
          !L.got.getD (L.next + 2 * P.lay.lk + 2) false && L.next + 2 * P.lay.lk + 3 == P.nMsg
      | _, _ => false
    | _, _ => false

/-- The ledger's shape behind. -/
def ledUpd (P : HeadMergeP) (L : LedSh) : LedSh :=
  LedSh.mk L.ns L.shown L.factors (L.got.set (L.next + 2 * P.lay.lk + 2) true) L.owed P.nLin
    L.trees (L.next + 2 * P.lay.lk + 3) L.coefs L.claims L.drawn L.handed L.shut

/-- The shape of what the merge leaves. L: the ledger's shape in front. c: the claim's shape. e: the
number that the shape holds of what the head heard: the claim's value's slot is e + 1. -/
def mergeShOf (P : HeadMergeP) (L : LedSh) (c : WsClaimSh) (e : Nat) : MergeSh :=
  { rm := P.lay.lk
    p := PscSh.mk false true (List.replicate P.lay.lk 3 ++ [2]) (P.lay.lk + 1) L.next
      (AffSh.mk [] [e + 1]) true
    sFv := L.next + 2 * P.lay.lk + 2
    recs := [rowPartSh P.lay c] }

/-- **THE UPDATE.** Where the shape holds no ledger, no fields of the head's, no claim or nothing of
what the head heard: the shape itself: the test says no there. -/
def mergeUpd (P : HeadMergeP) (a : ChainSh) : ChainSh :=
  match a.led, a.head with
  | some L, some h =>
    match h.claim, h.xEnd with
    | some c, some e =>
      ((a.setRowsOwed none).setLed (ledUpd P L)).setHead
        { h with
          wo := some (mergeShOf P L c e), Fm := L, slot := some (L.next + 2 * P.lay.lk + 3) }
    | _, _ => a
  | _, _ => a

/-- The twelve clauses on the state itself. Each "there is" is the one value of a reader at the
state. -/
def StateReady (P : HeadMergeP) (s : S) : Prop :=
  s.failed = none ∧
    ∃ a claim x, s.here = .head a ∧ a.opened = true ∧ s.noneWaits = true ∧
      a.claim = some claim ∧ a.x = some x ∧ claimFits P.lay claim = true ∧ Sized a.F ∧
      Filled a.F x.sV ∧ mergeEndSlot P.lay.lk a.F < a.F.ns ∧
      ¬ Filled a.F (mergeEndSlot P.lay.lk a.F) ∧ a.F.next + 2 * P.lay.lk + 3 = P.nMsg

/-- The statement on the test. Not proved here; a lemma's statement, none of the library's goals. -/
def GuardIsReady : Prop :=
  ∀ (P : HeadMergeP) (s : S), mergeGuardB P (chainSh s) = true ↔ StateReady P s

/-- The statement that the update carries. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergeCarries : Prop :=
  ∀ (P : HeadMergeP) (rs : List Fmt.RoundView) (s s' : S), roundsFit (headClaimMergeKind P).rounds rs = true →
    headMergeDecide P s (rs.map noDigest) = .ok s' → mergeGuardB P (chainSh s) = true →
    mergeUpd P (chainSh s) = chainSh s'

/-- The statement that the decision returns. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergeReturns : Prop :=
  ∀ (P : HeadMergeP) (rs : List Fmt.RoundView) (s : S), roundsFit (headClaimMergeKind P).rounds rs = true →
    mergeGuardB P (chainSh s) = true → ∃ s', headMergeDecide P s (rs.map noDigest) = .ok s'

end Johnson.Desc.First.ForkMerge.ShapeStep

#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.facFitsSh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.claimFitsSh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.onRowsSh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.rowPartSh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeGuardB
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.ledUpd
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeShOf
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeUpd
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.StateReady
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.GuardIsReady
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.MergeCarries
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.MergeReturns
