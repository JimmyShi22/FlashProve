-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionScores.lean: the attention sub-proof's messages on the matrix `as` and on
the scores.

This is the first half of part 2 of the check of the attention sub-proof, the sub-proof's own
messages (OnBytes/Model/Attention.lean lists the parts). The second half is in
OnBytes/Model/AttentionDivide.lean. The file follows the two steps of the function run of
verifier/src/vf_attention_check.h that the comments there number 3 and 4. The page on the sub-proof
is docs/format/11-3-attention-segment.md (section 11.3 of the format).
OnBytes/Model/AttentionHeard.lean explains the terms.

What is received.
 - For each unit of a call of kind KR: three hidden values. They are the first three planes of the
   matrix `as` at the unit's inner point, summed over the unit's pieces with their weights.
 - For each unit of a call of kind KFD: seven hidden values. They are the five planes of `as`, the
   row maximum and the score, each at the unit's inner point and summed over the unit's pieces with
   their weights. A sumcheck of products follows, which starts from the seventh value. Its maps A_b
   and B_b are the queries and the keys of the unit's piece b.

No equation is tested here. Each value is stored under its slot, and each sumcheck leaves its row.
The claims that tie them to the committed matrices are added in part 6
(OnBytes/Model/AttentionClaimsA.lean). The only tests are on public numbers. Which messages are
received depends only on the shape.

Main definitions: unitsOf, planeUnit, scoreFactor, scoreUnit, scores.

This file holds no theorem. It claims neither soundness nor hiding.
-/
import OnBytes.Model.AttentionHeard

namespace OnBytes.Attention

/-! ## Units -/

/-- The units of the calls of one kind: the calls in list order, and for each call those members of
segs that it holds, in the order of segs. Each unit comes as the call's number, the call and the
segment. -/
def unitsOf (S : Shape) (kind : Table) (segs : List Seg) : List (Nat × ACall × Seg) :=
  S.calls.toList.zipIdx.flatMap fun x =>
    if x.1.kind == kind then (segs.filter fun s => x.1.holds s).map fun s => (x.2, x.1, s)
    else []

/-! ## The calls of kind KR -/

/-- Receives the three plane values of one unit of a call of kind KR. zk holds the key point of
every call. -/
def planeUnit (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg) :
    Model.SubM PlaneClaim := do
  let key := zk.getD u.1 #[]
  let s0 ← Model.SubM.claimsIn 3
  let p : PlaneClaim :=
    { call := u.1, seg := u.2.2, z := inner S key u.2.2, isD := u.2.2 == Seg.rd,
      pw := pieces u.2.1 key u.2.2, s0 := s0, np := 3 }
  pure p

/-- Runs planeUnit on each unit of the list and adds what it returns to the plane claims. -/
def planeUnits (S : Shape) (zk : Array (Array E)) :
    List (Nat × ACall × Seg) → Array PlaneClaim → Model.SubM (Array PlaneClaim)
  | [], planes => pure planes
  | u :: us, planes => do
    let p ← planeUnit S zk u
    planeUnits S zk us (planes.push p)

/-! ## The calls of kind KFD -/

/-- The factor that all weights of a unit's sumcheck share, at the sumcheck's point r. The point
begins with the coordinates of g. After them come those of the slot row and the tile slot (segment
fm) or of the tile row (segment fd). The last ones are those of the feature within a head, which
have no weight. The factor is eq of the inner point's parts with these coordinates. For segment fm
the tile slot without a tile is taken out: its term is the product of all coordinates of zs and of
the tile slot's part of r. -/
def scoreFactor (S : Shape) (s : Seg) (zg zP zs zI r : Array E) : E :=
  let lgk := S.cf.lgk
  let f := eqPts zg (r.extract 0 lgk)
  if s == Seg.fm then
    let a := lgk + (S.lnT - 1)
    let rs := r.extract a (a + S.lnT)
    mulE (mulE f (eqPts zP (r.extract lgk a))) (subE (eqPts zs rs) (mulE (onesOf zs) (onesOf rs)))
  else
    mulE f (eqPts zI (r.extract lgk (lgk + S.lnT)))

/-- Receives the messages of one unit of a call of kind KFD: seven hidden values, then the
sumcheck of products, whose row it makes. claim is the number that the unit's plane claim will have
in the list of plane claims. Returns that plane claim and what is stored of the unit.

The inner point is cut into its parts: g; the slot row and the tile slot (segment fm) or the tile
row (segment fd); the row within a tile; the column within a tile. The test asks that the inner
point has exactly these coordinates. It has no name of its own: a failure is reported as refused
(unnamed in OnBytes/Iop/Ground.lean). The C++ verifier does not make this test: there the lengths
agree by the way in which the shape is made. wI is the weight of each tile row at the inner
point. -/
def scoreUnit (S : Shape) (zk : Array (Array E)) (claim : Nat) (u : Nat × ACall × Seg) :
    Model.SubM (PlaneClaim × Score) := do
  let s := u.2.2
  let fm := s == Seg.fm
  let key := zk.getD u.1 #[]
  let pw := pieces u.2.1 key s
  let z := inner S key s
  let lgk := S.cf.lgk
  let lB := S.cf.lB
  let a := lgk + (S.lnT - 1)
  let b := if fm then a + S.lnT else lgk + S.lnT
  Model.SubM.must (z.size == b + 2 * lB)
  let zg := z.extract 0 lgk
  let zP := if fm then z.extract lgk a else #[]
  let zs := if fm then z.extract a b else #[]
  let zI := if fm then #[] else z.extract lgk b
  let s0 ← Model.SubM.claimsIn 7
  let p : PlaneClaim :=
    { call := u.1, seg := s, z := z, isD := s == Seg.fd, pw := pw, s0 := s0, np := 5 }
  let wI := if fm then (tileSums S (Model.eqTab zP) (Model.eqTab zs)).1 else Model.eqTab zI
  let sc ← sc3In (S.nvKF s) pw.size (Model.Aff.slot (s0 + 6))
  let sc ← sc3Row sc (timesW pw (scoreFactor S s zg zP zs zI sc.r))
  let k : Score :=
    { call := u.1, claim := claim, seg := s, pw := pw, zg := zg, zs := zs,
      zi := z.extract b (b + lB), zj := z.extract (b + lB) (b + 2 * lB), wI := wI, s0 := s0,
      sc := sc }
  pure (p, k)

/-- Runs scoreUnit on each unit of the list. It adds the unit's plane claim to the plane claims and
what is stored of the unit to the list of scores. -/
def scoreUnits (S : Shape) (zk : Array (Array E)) :
    List (Nat × ACall × Seg) → Array PlaneClaim → Array Score →
      Model.SubM (Array PlaneClaim × Array Score)
  | [], planes, stored => pure (planes, stored)
  | u :: us, planes, stored => do
    let x ← scoreUnit S zk planes.size u
    scoreUnits S zk us (planes.push x.1) (stored.push x.2)

/-! ## Both kinds

The hidden values of a unit do not close a round. They are the first items of the message that the
next sumcheck opens.
-/

/-- Receives the messages on the matrix `as` and on the scores. First come the units of the calls of
kind KR, with the segments in the order rm, rd. Then come the units of the calls of kind KFD, with
the segments in the order fm, fd. zk holds the key point of every call, in list order. Returns the
plane claims and the units of the scores, each in the order in which the values were sent. -/
def scores (S : Shape) (zk : Array (Array E)) : Model.SubM (Array PlaneClaim × Array Score) := do
  let planes ← planeUnits S zk (unitsOf S Table.kr [Seg.rm, Seg.rd]) #[]
  scoreUnits S zk (unitsOf S Table.kfd [Seg.fm, Seg.fd]) planes #[]

end OnBytes.Attention
