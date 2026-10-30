-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Tests.lean: DEFINITIONS WITH CODE; NO THEOREM: THE TESTS BEHIND THE ADDING,
as a sub-protocol (`Block`) without a round.

Where it stands. A segment of the first chain hears its messages, draws the element that batches its
claims, and adds the claims to one equation. Behind the last claim, and in front of the segment's
closing, the verifier tests its own books, in this order:
  (1) every sent scalar stands in a claim (`K9.freeSlot`, Johnson/Desc/First/Batch/Sums.lean, by
  name);
  (2) the segment's sort's own counts. THEY ARE NOT K9's TEXT: they are a parameter: a list of tests
      on the state, each under one name;
  (3) the smallness test's three: its test of its own books; THE ROWS' WEIGHTS ARE WRITTEN; the test
      by a second computation. THEY ARE NOT K9's TEXT EITHER (K8's run behind the batching): a
      parameter: one function from the tables' numbers of entries, the smallness test's state and
      the ledger to the ledger behind it.
So of this block K9's own are the order, the one call of (1), and what is read and written.
WHOSE LINE IS WHICH, BY THE LINES OF THE PROGRAM `verify-on-bytes`. `testsBehind` TAKES WHATEVER
LISTS IT IS HANDED: that (2) and (3) are these lines is the seat's duty
(Johnson/Desc/First/Batch/TestsAtS.lean: countsAt · First.Door.weightsE), not asked here.
  (1) K9's: Layer.lean:632 · Attention.lean:231 · Head.lean:273-274.
  (2) the number of claims is the plan's: Layer.lean:633 · Head.lean:275 · at attention that program
      asks it behind the closing (Attention.lean:159): `countsAt`
      (Johnson/Desc/First/Batch/TestsAtS.lean) asks it HERE at all three sorts;
      the matrix drawn once · two lookups: Head.lean:276-277 (the head's); at a feed-forward segment
      they stand in front of the smallness test's claims (Layer.lean:620-621: another step's);
      the list of tables is the closed one: Layer.lean:634 · Attention.lean:232 · Head.lean:278.
  (3) K8's: Layer.lean:635-637 · Attention.lean:83-85 · Head.lean:279-281.

Main names:
  `TWhere`: the place's numbers. `TPart`, `TLens`: what is read and written of a state.
  `countsHold`: (2). `testsText`: **the step**, on the part. `testsBehind`: the step as a block.

AGAINST `verify-on-bytes` (OnBytes/Model/Layer.lean:632-637 · Attention.lean:231-232 with :83-85 ·
Head.lean:271-281): meant to be the same tests in the same order; no theorem of this file compares
them. AT (1), AT A LAYERS' SEGMENT, THAT PROGRAM
MARKS THE STATE AND GOES ON (Blk.check, Layer.lean:515); at attention and at the head it refuses at
once (testAs, Attention.lean:146 · Head.lean:273), AS THIS BLOCK DOES AT ALL THREE. At a layers'
segment that program asks (1) at the end of the step in front (the back half of the claims); nothing
lies between that line and this step's first.

Limits: no round, no view, no column. The ledger and the smallness test's record are records of
`verify-on-bytes` (`Model.Fork`, `Model.HTailF2`). No law is stated. By that program's own word
most of these tests guard against a slip of the verifier's own text and are meant to fail on no
file; (1) can fail at an unlucky challenge. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

variable {T Cl : Type}

/-- The numbers of the place. -/
structure TWhere where
  chain : Nat
  link : Nat
  /-- the block's number inside its segment -/
  piece : Nat
  /-- the slots that the segment's messages fill -/
  filled : Nat
  /-- the numbers of entries of the tables U1, U2, U3 -/
  nU : Array Nat

/-- What the step reads of the state. It writes the ledger alone. -/
structure TPart where
  /-- the slot of the merge's end value, if the segment has a merge -/
  merge : Option Nat
  /-- the smallness test's record -/
  tl : HTailF2
  /-- the segment's ledger, which holds the sums -/
  F : Fork

/-- The part inside a state T; nothing where no segment is open. -/
structure TLens (T : Type) where
  get? : T → Option TPart
  set : T → Fork → T

/-- (2): the sort's own counts, each under its name, in the order of the list. -/
def countsHold (counts : List (String × (T → Bool))) (t : T) : Ans Unit :=
  counts.forM fun c => need c.1 (c.2 t)

/-- **The step.** counts: (2). weights: (3). The ledger behind it. -/
def testsText (p : TWhere) (counts : List (String × (T → Bool)))
    (weights : Array Nat → HTailF2 → Fork → Ans Fork) (t : T) (s : TPart) : Ans Fork := do
  freeSlot p.filled s.merge s.F
  countsHold counts t
  weights p.nU s.tl s.F

/-- **The tests behind the adding.** No round. General in the state and in the type of claims. -/
def testsBehind (X : TLens T) (p : TWhere) (counts : List (String × (T → Bool)))
    (weights : Array Nat → HTailF2 → Fork → Ans Fork) : Block T Cl :=
  { name := "K9: the tests behind the adding"
    place := ⟨p.chain, some p.link, p.piece, .K9⟩
    planOk := true
    rounds := []
    oracles := []
    before := []
    decide := fun t _ _ => do
      let s ← there "K9.in-a-segment" (X.get? t)
      let G ← testsText p counts weights t s
      pure (X.set t G)
    claims := []
    after := [] }

end VerifiableInference.Desc.K9
