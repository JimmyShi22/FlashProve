-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Attention.lean: the check of the attention sub-proof.

The attention sub-proof of a group of layers is about the attention function. Its statement is that
the committed outputs follow from the committed queries, keys and values
(docs/format/11-3-attention-segment.md, section 11.3 of the format). This file is the frame of its
check. It follows the function run of verifier/src/vf_attention_check.h. It runs the parts in their
order, and it makes the tests that belong to no single part. OnBytes/Model/AttentionHeard.lean
explains the terms of the attention files. Of the terms that all sub-proofs share, smallness test is
explained in OnBytes/Model/Frame.lean, slot, claim, array and virtual row in
OnBytes/Model/Hide.lean, and link in OnBytes/Model/Trees.lean.

The seven parts, with their files in OnBytes/Model/.
 1. The lookup of all calls of the sub-proof, as one group (Look.lean).
 2. The sub-proof's own messages (AttentionScores.lean, AttentionDivide.lean).
 3. The commitment to the tables, and the tables' weights (AttentionTables.lean).
 4. The messages of the smallness test (Tail.lean).
 5. The draw of the element whose powers batch the linear claims (Trees.lean).
 6. The claims: the lookup's, the sub-proof's own (AttentionClaimsA.lean, AttentionClaimsB.lean),
    and the smallness test's.
 7. The closing steps: the claims add up to one equation, which the chain tests at its end.

Main definitions: Seam.start, Seam.transcript, Seam.batch, Seam.objects, Seam.finish, weighedUnits,
allJoined, laidPadding, paddingLaid, noFreeSlot, countsHeld, hear, claims, run, frameNames, names.

What this file does not claim. It holds no theorem. It is not proved here that an accepted sub-proof
shows its statement. The file does not test that a message has no scalar left over. That is tested
elsewhere: a round can be closed only when all its items are taken, and a chain's decision must use
up all rounds. Names that differ from the C++: see the section The names of the refusals.
-/
import OnBytes.Model.Tail
import OnBytes.Model.AttentionPlan
import OnBytes.Model.AttentionScores
import OnBytes.Model.AttentionDivide
import OnBytes.Model.AttentionTables
import OnBytes.Model.AttentionClaimsA
import OnBytes.Model.AttentionClaimsB

namespace OnBytes.Attention

open OnBytes.Model

/-! ## The seam: what this check uses of the smallness test and of the list of arrays

The routines are in OnBytes/Model/Tail.lean and OnBytes/Model/Trees.lean. The C++ verifier gathers
these steps in one record, AttentionSeam. Each step of a run (start, transcript, batch, objects,
finish) has a definition here under its C++ name, even where it only calls one routine. The record
Seam and the steps shape, iU3, smallElems and plan, which read no proof, are in
OnBytes/Model/AttentionPlan.lean. -/

namespace Seam

/-- The start of a run. Gives every virtual row its column weights L, all 0, and sets up ns empty
slots. Returns the plan's state of the smallness test, with the list of tables open and no matrix
drawn. The caller must first let the chain receive and sample the link's first commitments, which
the lookup relies on (OnBytes/Model/Look.lean, What the caller owes), and must run this check on
the plan's arrays (s.Fp as the state, s.Tp as LinkCtx.list); the C++ start copies both itself.
Neither is tested here. runLinkH in OnBytes/Model/StagesLinks.lean does both. -/
def start (s : Seam) (ns : Nat) : LinkM HTailF2 := do
  LinkM.sub (SubM.change fun F => some (F.fillL.slots ns))
  pure { s.tl with funClosed := false, foldDrawn := 0 }

/-- The messages of the smallness test. -/
def transcript (tl : HTailF2) : LinkM HTailF2 := tl.transcript

/-- The draw of the element that batches the claims, after the sub-proof's last message. used is the
number of slots taken so far. No other round of the chain comes between that message and the first
claim. -/
def batch (used : Nat) : LinkM Unit := t2Batch used

/-- The claims of the smallness test. -/
def objects (tl : HTailF2) (funs : Array HFun) : SubM HTailF2 := tl.objectsF funs

/-- The steps after the last claim, in this order. selfTest: no column that a virtual row is meant
to read has the weight 0. coefficients: each virtual row's weights on the rows of its array.
rkSelfTest: a second computation of part of the smallness test's weights. doorH: the one equation
goes to the link's closing. OnBytes/Model/Tail.lean says what the first three cover. Refuses under
internal-f-draws if Seam.objects has not run: the count that doorH needs (equationsLaidF) is then
missing. -/
def finish (tl : HTailF2) (nU : Array Nat) : LinkM Unit := do
  tl.selfTest nU
  tl.coefficients
  tl.rkSelfTest
  let some laid := tl.equationsLaidF | refuse "internal-f-draws"
  doorH laid

end Seam

/-! ## The tests of the frame -/

/-- The units whose pieces have a weight in a key form: rm and rd in each call of kind KR that holds
them, fm and fd in each call of kind KFD that holds them, and each of wl, ix and wh in the last call
that holds it. The list is computed from the shape by unitsOf (AttentionScores.lean) and
lastHolding, the functions by which part 2 picks its units. It is not a record of the run; the C++
verifier marks a piece where it computes the piece's weight (pieces in run). -/
def weighedUnits (S : Shape) : List (Nat × Seg) :=
  let listed (kind : Table) (segs : List Seg) : List (Nat × Seg) :=
    (unitsOf S kind segs).map fun u => (u.1, u.2.2)
  let single (s : Seg) : List (Nat × Seg) := ((lastHolding S s).map fun q => (q, s)).toList
  listed .kr [.rm, .rd] ++ listed .kfd [.fm, .fd] ++ single .wl ++ single .ix ++ single .wh

/-- Every call's key form has been set, and set once. -/
def allJoined (j : Joins) : SubM Unit := do
  mustAs "af-unclosed-call" (j.joined.all (· == 1))

/-- Adds the padding places of call number q to laid, which has one count for each tree of the
lookup. These are the places of every piece without a weight in a key form, and all places after
the last piece that has one. It assumes, and does not test, that the pieces follow one another
without a gap (layOff in OnBytes/Model/AttentionShape.lean). -/
def paddingOfCall (h : Forest.Shape) (units : List (Nat × Seg)) (q : Nat) (c : ACall)
    (laid : Array Nat) : Except String (Array Nat) := do
  let step (st : Array Nat × Nat) (pc : Piece) : Except String (Array Nat × Nat) :=
    if units.contains (q, pc.seg) then pure (st.1, max st.2 (pc.off + 2 ^ pc.b))
    else do
      let l ← Forest.pubRun h st.1 q pc.off (2 ^ pc.b)
      pure (l, st.2)
  let (l, upto) ← c.pcs.toList.foldlM step (laid, 0)
  Forest.pubRun h l q upto (2 ^ c.call.n - upto)

/-- For each tree of the lookup, the number of places that the key forms leave to the padding. -/
def laidPadding (S : Shape) (h : Forest.Shape) : Except String (Array Nat) :=
  let units := weighedUnits S
  S.calls.toList.zipIdx.foldlM (fun laid x => paddingOfCall h units x.2 x.1 laid) (Forest.noPub h)

/-- The two descriptions of the padding must agree. The lookup counts the padding keys of each tree
from ACall.tot, the sum of the sizes of a call's pieces. Except in calls of kind KFD a key form has
no term for a padding place, so it reads the key 0 there, which must be the call's padding key
(internal-af-padding-key). The places are counted from weighedUnits and not from the forms, so a
fault inside a form is not seen. Forest.paddingLaid makes the comparison
(internal-forest-padding-places). All numbers are public: a failure is a fault of this program, not
of a proof. -/
def paddingLaid (S : Shape) (g : Forest.Heard) : SubM Unit := do
  mustAs "internal-af-padding-key"
    (S.calls.all fun c => c.kind == .kfd || c.call.tauAt c.call.t0 == 0)
  let .ok laid := laidPadding S g.shape | refuse "internal-forest-pub"
  Forest.paddingLaid g laid

/-- Every slot of a message has a coefficient other than 0 in the one equation. This is a test of
the list of claims, not of the proof: a value that was sent and occurs in no claim is found here. A
coefficient is a sum of products of drawn elements, so an unlucky challenge can make it 0; no bound
on how often is stated or proved here. The run is refused then too. -/
def noFreeSlot (nMsg : Nat) : SubM Unit := do
  let F ← get
  testAs "internal-a-free-slot" ((Array.range nMsg).all fun j => !isZeroE (F.LS.getD j zeroE))

/-- The counts at the end. As many claims were added as planned, each under a power of its own of
the batching element. In the smallness test the sums of every matrix were taken once, the matrix of
combinations was drawn once, and the lookup ran, so that two lookups ran in all. These tests, and
those on the list of tables in run (internal-f-fun-closed, internal-f-fun-moved), guard variables
that the C++ verifier changes in place. Here the state is a value that run passes from step to step,
so they can fail only if run or a routine that it calls is changed; the three on the claims repeat
what doorH has tested. -/
def countsHeld (P : Plan) (tl : HTailF2) : SubM Unit := do
  mustAs "internal-f-draws" ((← SubM.claims) == (← get).planClaimsF)
  SubM.allTaken
  mustAs "internal-f-draws" tl.foldAllTakenF
  mustAs "internal-a-claim-count" ((← SubM.claims) == P.nLin)
  mustAs "internal-af-rows-booked" (tl.foldDrawn == 1)
  mustAs "internal-a-calls-booked" (1 + tl.groupsRun == 2)

/-! ## The check

The check is a function in the type Blk (OnBytes/Iop/Ground.lean), which is run twice: a dry run
lists the chain's rounds, and a run on the values read from a proof file gives the decision. It
reads no bytes and calls no hash.
-/

/-- What parts 1 and 2 return. -/
structure First where
  /-- what the lookup of the sub-proof's calls has stored -/
  g : Forest.Heard
  /-- the plane claims -/
  planes : Array PlaneClaim
  /-- the units of the scores -/
  scores : Array Score
  /-- the division and the value product -/
  d : Divide
  /-- the maximum and the index's bits -/
  x : Attain

/-- Parts 1 and 2: the messages up to the commitment to the tables. The lookup's messages come
first; they give every call its key point. Then come the sub-proof's own messages. -/
def hear (P : Plan) : SubM First := do
  let g ← Forest.pad (P.S.calls.map (·.call)) P.fs.pub P.lid
  let (planes, scores) ← scores P.S g.zk
  let d ← divide P.S g.zk
  let x ← attain P.S
  pure { g, planes, scores, d, x }

/-- The claims of the sub-proof and of its lookup, in their order. The claims of the smallness
test follow them. -/
def claims (P : Plan) (h : Heard) : SubM Unit := do
  Forest.objects h.g
  let j ← claim3 h (Joins.empty P.NC)
  let j ← claim4 h j
  let j ← claim5 h j
  allJoined j
  paddingLaid h.S h.g
  SubM.lin (← Forest.join h.g j.kf)
  claim6 h
  claim7 h
  claim8 h
  Forest.planeLins h.g h.S.cf.lmb
    (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
    (fun col => u3at h h.t.tPin col)

/-- The check of the attention sub-proof, as a link of the request's chain. After part 4 it tests
that the messages have taken exactly the planned slots. What the caller owes stands at Seam.start;
run does not test it. -/
def run (P : Plan) : LinkM Unit := do
  let tl ← P.seam.start P.ns
  let f ← hear P
  -- The tables are committed to. Their weights follow from what was drawn before.
  rootInH [P.iU3]
  mustAs "internal-f-fun-closed" tl.funOpen
  let t ← tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x
  let some tl := tl.closeFuns t.funs | refuse "internal-f-fun-closed"
  -- The list of tables is closed before the smallness test draws its matrix: transcriptF in
  -- OnBytes/Model/Tail.lean refuses an open list. Then come the smallness test's messages and the
  -- batching element.
  let tl ← Seam.transcript tl
  mustAs "internal-slot-count" ((← SubM.slot) == P.nMsg)
  SubM.setPlanClaims P.nLin
  Seam.batch (← SubM.slot)
  -- The claims.
  claims P { S := P.S, g := f.g, planes := f.planes, scores := f.scores, d := f.d, x := f.x, t,
             iU3 := P.iU3 }
  let tl ← Seam.objects tl t.funs
  noFreeSlot P.nMsg
  mustAs "internal-f-fun-moved" (tl.funsHeld t.funs)
  -- The closing steps.
  Seam.finish tl P.seam.nU
  countsHeld P tl

/-! ## The names of the refusals

Where the C++ verifier refuses under a name, the test refuses here under that name (mustAs, testAs
and refuse in OnBytes/Model/Frame.lean), by a reading of the C++ source (no theorem). The C++
verifier puts the sub-proof's prefix (the argument G_ of run) before most of these names. Here a
name has no prefix, and a failure gets the sub-proof's name as its place (runLinkH in
OnBytes/Model/StagesLinks.lean). In this file one test has no name: SubM.allTaken in countsHeld
fails under the general name refused (unnamed in OnBytes/Iop/Ground.lean), where the C++ verifier
says internal-f-draws.
-/

/-- The names that this file passes to its tests. -/
def frameNames : List String :=
  ["af-unclosed-call", "internal-af-padding-key", "internal-forest-pub", "internal-a-free-slot",
   "internal-f-draws", "internal-a-claim-count", "internal-af-rows-booked",
   "internal-a-calls-booked", "internal-f-fun-closed", "internal-slot-count",
   "internal-f-fun-moved"]

/-- The names that the check of the attention sub-proof and its plan pass to their tests: those of
this file, of the attention files that it imports, and of OnBytes/Model/Tensors.lean. A name may
be in several of the lists. The names of OnBytes/Model/AttentionConfig.lean are in configNames
there. The check can also fail under a name of a routine that it calls, which is not listed here
(for example lookNames, Forest.names, Tail.names, Trees.names, Rounds.names), and under the general
name refused (unnamed in OnBytes/Iop/Ground.lean) where a test has no name. -/
def names : List String :=
  tensorsNames ++ shapeNames ++ sumsNames ++ planNames ++ divideNames ++ tablesNames ++
    claimsANames ++ frameNames

end OnBytes.Attention
