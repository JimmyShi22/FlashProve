-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RowReturns.lean: THE STATEMENT, AND NO PROOF: "THE PENDING ROW CAN BE MADE OF
WHAT K4's HEARING LEAVES". Definitions alone: what of the merge's leavings the routine's return
hangs on (RowSkel), the law as a sentence (RowReturn), and the parts. The proofs: PendSkel and
RowReturn in Johnson/Road/K4/Total/RowProofs.lean, HearRowSkel in
Johnson/Road/K4/Total/HearRowSkel.lean.

WHY IT IS OWED. The frame's reader of the pending row (Johnson/Top/H0/Walk/FrameRow.lean: rowAt)
calls pendingRowO (Johnson/Desc/First/Pend/Row.lean) on the merge's leavings, which K4's hearing
lays. A public test on the verifier's state (hasRow) asks that this reader returns. Every law on the
routine begins "where it returns". THE LAW IS NEEDED FOR THAT TEST, NOT ENOUGH: that what is left at
the state behind K4's yes is the hearing's leavings, roomB, and that the test is asked at this
layout, this number of claims and this shape stand beside it.

WHAT THE RETURN HANGS ON. The routine falls in two (pend_of, Johnson/Top/H0/MergeLaw/PendRow.lean):
the routine wsPending (OnBytes/Model/Pending.lean), on the layout of W, the plan's number of claims,
the shape of the test on W and the merge's leavings; and the taking of a mask entry off a ledger of
the statement. wsPending TESTS NO ELEMENT: of the leavings it reads the length of the merge's point,
how many claims' rests there are, and of each rest its unit's number, the number of its factors and
three lengths of each factor (RowSkel). The elements go into products and sums alone.

  `RowSkel w w₀`: two leavings of one skeleton: the points are as long; the rests are as many and
    name, one by one, one unit with factors of the same sizes (All2 RecSizes,
    OnBytes/Flat/DryRel.lean, PendingSizes.lean).
  `PendSkel`: at two leavings of one skeleton wsPending returns at both or at neither.
  `roomB im os`: A TEST WITH CODE on the statement's oracle messages: message number im has a ledger
    with an entry to take.
  `RowReturn`: THE LAW: w of w₀'s skeleton · wsPending returns at w₀ (THE MEMBER) · roomB: then
    pendingRowO returns at w.
  `HearRowSkel`: two returns of K4's hearing (hear at the plain engine), at one sub-proof's plan hp
    and one group g, leave merges of one skeleton.
**Limits.** SENTENCES: NOTHING IS PROVED HERE. THE MEMBER IS A PREMISE: that wsPending returns
anywhere is said BY NO THEOREM HERE, AND NO RUN IS CITED HERE. One member is owed for each
sub-proof's plan and group, that is for each layers' place, at the layout, number of claims and
shape at which the test is asked. HearRowSkel carries a member to K4's leavings only if w₀ is itself
a hearing's leavings at that plan: a w₀ made by hand needs a law of its own: rowSkel_plan
(Johnson/Road/K4/Total/PlanRow.lean) is one. A run would pay no premise of a theorem. roomB: NO
TABLE OF PUBLIC ITEMS THAT IS CITED HERE SAYS IT; it speaks of the state's statement, which K4's
hearing does not turn; IT IS NO INVARIANT OF THE CHAIN: each link that leaves a row takes an entry:
what can ride is a count (roomFor, Johnson/Road/K4/Total/RoomFor.lean). One direction is meant: that
the row can be made, not what it says. Nothing on soundness. K04_law, the law of K4's block itself,
IS NOT PROVED.


-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.Flat.PendingSizes
import Johnson.Desc.First.Pend.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Params (LinShape)
open OnBytes.Flat (All2 RecSizes)
open VerifiableInference.Desc.First.Pend (pendingRowO takeEntry)

/-- **What of the merge's leavings the pending row's return hangs on.** No clause holds an element.
-/
structure RowSkel (w w₀ : WsForkOut) : Prop where
  rm : w.rm.size = w₀.rm.size
  recs : All2 RecSizes w.recs w₀.recs

/-- The routine wsPending returns at two leavings of one skeleton, or at neither. -/
def PendSkel : Prop :=
  ∀ (lay : WsLay) (n : Nat) (lin : LinShape) (w w₀ : WsForkOut), RowSkel w w₀ →
    (wsPending lay w n lin).toOption.isSome = (wsPending lay w₀ n lin).toOption.isSome

/-- Message number im of the statement has a ledger with an entry to take. -/
def roomB (im : Nat) (os : Array Oracle) : Bool :=
  (((os[im]?).bind (·.ledger)).bind takeEntry).isSome

/-- **THE LAW**: of a leaving of the member's skeleton the pending row can be made, if the ledger
has an entry to take. -/
def RowReturn : Prop :=
  ∀ (lay : WsLay) (im n : Nat) (lin : LinShape) (os : Array Oracle) (w w₀ : WsForkOut),
    RowSkel w w₀ → (wsPending lay w₀ n lin).toOption.isSome = true → roomB im os = true →
    ∃ r, pendingRowO lay im w n lin os = .ok r

/-- Two returns of the hearing at the plain engine, at one sub-proof's plan hp and one group g, at
two values of the public parameters with one layout, one list of reads and one layout of the
weights, leave merges of one skeleton. -/
def HearRowSkel : Prop :=
  ∀ (P P₀ : Pub) (hp : HPlan2) (g : Nat) (fo fo₀ : Forest.Heard) (F G F₀ G₀ : Fork)
    (t u t₀ u₀ : Tape) (o o₀ : Own), P.y = P₀.y → P.rd = P₀.rd → P.wsLay = P₀.wsLay →
    hear engFl P hp g fo F t = some (o, G, u) →
    hear engFl P₀ hp g fo₀ F₀ t₀ = some (o₀, G₀, u₀) → RowSkel o.wo o₀.wo

end OnBytes.Desc.First.K4.Total
