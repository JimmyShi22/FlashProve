-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionScores.lean: tests of OnBytes/Model/AttentionScores.lean.

The tests run when this file is compiled. The program does not import this file.

What is tested, at shapes with four and eight tiles along a side: the order of the units; the
weights of the tile rows against the numbering of the tiles written out by hand; the factor of a
unit's sumcheck against products computed by hand.

Of the functions that receive messages two things are tested, in dry runs of the own part of the
check at a small configuration, spelled out in OnBytes/Model/TestAttentionPlan.lean (smallCfg: 64
tokens, a group of four layers, four query heads, two heads of keys and values). Below it is called
the example. No file of the repository is read; the examples under prover/examples may have other
numbers.
 - The test in scoreUnit on the length of the inner point. A run at the example does not reach its
   refusal, since there the lengths agree. Here the dry run (ownPasses in
   OnBytes/Model/TestAttentionDivide.lean) is made once with a key point of just the length that is
   needed and once with one coordinate fewer.
 - Which call's key point a unit reads. At the example all calls have as many keys as a tree of the
   lookup, so a proof gives all of them the same key point, and a unit that read another call's
   point would not be noticed. Here each call gets a key point of its own, and all its coordinates
   differ, so that the cuts of the inner points in scoreUnit and divide are seen too.
-/
import OnBytes.Model.AttentionScores
import OnBytes.Model.TestAttentionDivide

namespace OnBytes.Attention.TestScores

/-- A point whose coordinates are small numbers. -/
def ptOf (v : List Nat) : Array E := (v.map fun x => ofF (UInt64.ofNat x)).toArray

/-- A call of the given kind that holds the given segments. -/
def callWith (kind : Table) (segs : List Seg) : ACall := { (default : ACall) with kind, segs }

/-- A shape with four tiles along a side, two heads of keys and values, and four calls. -/
def tiles4 : Shape :=
  { cf := { lt := 3, lB := 1, lgk := 1, ldh := 1 }, nT := 4, hP := 2, lnT := 2,
    calls := #[callWith .kfd [.fd], callWith .kr [.rd, .rm], callWith .r16 [.wl, .ix],
      callWith .kfd [.fm, .fd]] }

/-- A shape with eight tiles along a side. -/
def tiles8 : Shape :=
  { cf := { lt := 4, lB := 1, lgk := 1, ldh := 1 }, nT := 8, hP := 4, lnT := 3 }

/-- For each tile row, its weight at the point (zP, zs) on the tiles below the diagonal, as
scoreUnit forms it. -/
def rowWeights (S : Shape) (zP zs : Array E) : Array E :=
  (tileSums S (Model.eqTab zP) (Model.eqTab zs)).1

/-- The units as pairs of the call's number and the segment. -/
def unitNumbers (u : List (Nat × ACall × Seg)) : List (Nat × Seg) := u.map fun x => (x.1, x.2.2)

-- calls in list order; segments in the order asked for, not in the call's own order
#guard unitNumbers (unitsOf tiles4 .kr [.rm, .rd]) == [(1, Seg.rm), (1, Seg.rd)]
#guard unitNumbers (unitsOf tiles4 .kfd [.fm, .fd]) == [(0, Seg.fd), (3, Seg.fm), (3, Seg.fd)]
#guard unitNumbers (unitsOf tiles4 .wh [.wh]) == []

-- Slot row 0 has the three tiles of tile row 3. Slot row 1 has the tile of tile row 1, then the two
-- tiles of tile row 2.
#guard rowWeights tiles4 (ptOf [0]) (ptOf [0, 0]) == ptOf [0, 0, 0, 1]
#guard rowWeights tiles4 (ptOf [0]) (ptOf [0, 1]) == ptOf [0, 0, 0, 1]
#guard rowWeights tiles4 (ptOf [0]) (ptOf [1, 0]) == ptOf [0, 0, 0, 1]
#guard rowWeights tiles4 (ptOf [1]) (ptOf [0, 0]) == ptOf [0, 1, 0, 0]
#guard rowWeights tiles4 (ptOf [1]) (ptOf [0, 1]) == ptOf [0, 0, 1, 0]
#guard rowWeights tiles4 (ptOf [1]) (ptOf [1, 0]) == ptOf [0, 0, 1, 0]

-- the last tile slot of a slot row has no tile
#guard rowWeights tiles4 (ptOf [0]) (ptOf [1, 1]) == ptOf [0, 0, 0, 0]
#guard rowWeights tiles4 (ptOf [1]) (ptOf [1, 1]) == ptOf [0, 0, 0, 0]

-- Coordinate 0 is the top bit of a number: this is slot row 2, tile slot 1, a tile of tile row 2.
-- Read the other way, the slot row would be 1 (tile row 6) or the tile slot 4 (tile row 5).
#guard rowWeights tiles8 (ptOf [1, 0]) (ptOf [0, 0, 1]) == ptOf [0, 0, 1, 0, 0, 0, 0, 0]

-- at this point the weights add up to 1 minus the weight of the last tile slot, which is 77 here
#guard (rowWeights tiles4 (ptOf [5]) (ptOf [7, 11])).foldl addE zeroE == subE oneE (ofF 77)

-- tile row 1 has the one tile at slot row 1, tile slot 0: 5 (1 - 7) (1 - 11) = 300
#guard (rowWeights tiles4 (ptOf [5]) (ptOf [7, 11])).getD 1 zeroE == ofF 300

-- segment fm at g = 1, slot row 0, tile slot 1: 3 (1 - 5) (1 - 7) 11 = 792; the last coordinate has
-- no weight
#guard scoreFactor tiles4 .fm (ptOf [3]) (ptOf [5]) (ptOf [7, 11]) #[] (ptOf [1, 0, 0, 1, 9])
  == ofF 792

-- segment fm at the tile slot without a tile
#guard scoreFactor tiles4 .fm (ptOf [3]) (ptOf [5]) (ptOf [7, 11]) #[] (ptOf [1, 0, 1, 1, 9])
  == zeroE

-- segment fd at g = 0, tile row 2: (1 - 3) 5 (1 - 7) = 60
#guard scoreFactor tiles4 .fd (ptOf [3]) #[] #[] (ptOf [5, 7]) (ptOf [0, 1, 0, 9]) == ofF 60

-- The calls are KR, KFD, R16, WH. KFD holds fm, whose inner point has 12 coordinates, and fd, whose
-- inner point has 11. A key point of 12 coordinates passes, one of 11 does not. The test has no
-- name of its own. The inner point of fd is never the only one that is too short.
#guard ownPasses id (cutPoint 1 12) == some true
#guard ownPasses id (cutPoint 1 11) == some false
#guard ownRefusal id (cutPoint 1 11) == some (some "refused")

/-- Coordinate i of the marked key point of call q: the number 100 (q + 1) + i. -/
def mark (q i : Nat) : E := ofF (UInt64.ofNat (100 * (q + 1) + i))

/-- For each call a key point of the call's length, made of the call's marks. A key point has fewer
than 100 coordinates. -/
def markedPoints (S : Shape) : Array (Array E) :=
  S.calls.mapIdx fun q c => (Array.range c.call.n).map (mark q)

/-- True if z is not empty and all its coordinates are marks of call q. -/
def markedBy (q : Nat) (z : Array E) : Bool :=
  !z.isEmpty && z.all fun x => (List.range 100).any fun i => x == mark q i

/-- The coordinates from a up to but not including b of the marked key point of call q. -/
def marks (q a b : Nat) : Array E := ((List.range (b - a)).map fun i => mark q (a + i)).toArray

/-- What scores and divide store in the dry run of the own part at the example, under the entries of
its plan, with the marked key points. -/
def dryStored : Option ((Array PlaneClaim × Array Score) × Divide) := do
  let P ← smallPlan.toOption
  let planned ← (Params.finish {} .request (Params.planAttentionOwn P.own)).toOption
  let zk := markedPoints P.S
  let part : Model.SubM ((Array PlaneClaim × Array Score) × Divide) := do
    let x ← scores P.S zk
    let d ← divide P.S zk
    let _ ← attain P.S
    pure (x, d)
  let block : Blk ((Array PlaneClaim × Array Score) × Divide) :=
    part.run' (({} : Model.Fork).slots 502)
  (Blk.dryRun block { entries := planned.rounds.map (·.entry), st := {} }).map (·.2)

-- four plane claims and two units of scores: each reads the key point of its own call
#guard (dryStored.map fun x => (x.1.1.size, x.1.2.size)) == some (4, 2)
#guard (dryStored.map fun x => x.1.1.all fun pc => markedBy pc.call pc.z) == some true
#guard (dryStored.map fun x => x.1.2.all fun k =>
  markedBy k.call k.zg && markedBy k.call k.zi && markedBy k.call k.zj) == some true
-- the calls are KR, KFD, R16, WH: the plane claims belong to calls 0, 0, 1, 1
#guard (dryStored.map fun x => x.1.1.toList.map (·.call)) == some [0, 0, 1, 1]
-- wl and ix are read at the key point of call 2, wh at that of call 3
#guard (dryStored.map fun x => markedBy 2 x.2.ziW && markedBy 2 x.2.ziX && markedBy 3 x.2.ziH) ==
  some true

-- The cuts. A key point has 20 coordinates, and an inner point is its last ones. For fm these are
-- coordinates 8 to 19: g, the slot row, two for the tile slot, four for the row within a tile, four
-- for the column. For fd they are 9 to 19: g, two for the tile row, then four and four.
#guard (dryStored.map fun x => x.1.2.toList.map fun k => (k.zg, k.zs, k.zi, k.zj)) ==
  some [(marks 1 8 9, marks 1 10 12, marks 1 12 16, marks 1 16 20),
        (marks 1 9 10, #[], marks 1 12 16, marks 1 16 20)]
-- the weights of the tile rows are made from the slot row (coordinate 9) and the tile slot, and on
-- the diagonal from the tile row (coordinates 10 and 11)
#guard (do
    let P ← smallPlan.toOption
    let x ← dryStored
    pure (x.1.2.toList.map (·.wI) ==
      [rowWeights P.S (marks 1 9 10) (marks 1 10 12), Model.eqTab (marks 1 10 12)])) == some true
-- wl's inner point is coordinates 5 to 19 of call 2: one coordinate, g, six for the token and seven
-- for the feature. ix's is 13 to 19: g and the token. wh's is 6 to 19 of call 3: as wl's without
-- the first.
#guard (dryStored.map fun x => (x.2.zsl, x.2.zgW, x.2.ziW, x.2.zcW)) ==
  some (mark 2 5, marks 2 6 7, marks 2 7 13, marks 2 13 20)
#guard (dryStored.map fun x => (x.2.zgX, x.2.ziX)) == some (marks 2 13 14, marks 2 14 20)
#guard (dryStored.map fun x => (x.2.zgH, x.2.ziH, x.2.zcH)) ==
  some (marks 3 6 7, marks 3 7 13, marks 3 13 20)

end OnBytes.Attention.TestScores
