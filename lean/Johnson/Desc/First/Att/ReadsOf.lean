-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ReadsOf.lean: kind K5: the declaration of the segment's reads: for each read
its name, the matrix that it sums, the make of its runs of cells, the run's length, the number of
entries, the first entry, and its weights as a formula in the heard points.

What a read is. The claims of an attention segment's own rounds read values of the committed
matrices at points. Each such value is put together from entries of a table. An entry of a table is
a sum over a run of cells of one column of one matrix, under weights that are fixed once the points
are heard. The prover commits to all tables in one vector, the vector of reads, and the smallness
test ties that vector to the matrices.

This file lists the reads as data: no ledger, no routine, nothing that can refuse. The record is
ReadDecl of Johnson/Desc/Reads/Decl.lean, one type for all kinds.

What "heard" means here. The weights are formulas in p and lk. p (Pts, Att/Points.lean) is made by
pointsOf of three things: what this kind's rounds heard; each call's key point, which the lookup's
kind heard (the units' inner points are cuts of these); and the rows that the sumchecks leave, which
no weight reads. lk holds the lookup's own point zx, at which the first table in parts stands.

Main names:
  `Matrix`: the five matrices. `Weights`: the weights, by the four makes. `Read`: the names.
  `Read.of g lk p`: which matrix a read sums, and under which weights.
  `reads n`: all reads of a segment with n units of softmax-table calls, in the order in which
    their tables lie in the vector of reads.
  `Read.field`: the field of the record TablesP (Att/TablesP.lean) under which the claims ask for
    the read's first entry; `Read.first t`: what stands there. `Read.count`, `Read.start`: the
    number of entries; the first entry.
  `Weights.array`: one weight a cell of a run. `Read.decl`: the record of one read.
  `readsOfK5 g lk p`: the segment's whole declaration.
  `fit g lk p`: every read has as many weights as its run has cells.
  `tablesOf`: a record's tables as the smallness test takes them.
The weights are arrays, read with the default 0: weight number j is 0 from the array's end on. No
number is cast into the field in a formula of this file or in eqTab, tok, tileSums, scoreTiles,
blockRows, lastN, pointM, pointD: an index only says which member of an array is read.
More parts than one have run nowhere with us: NAs = 1 at both example geometries
(Johnson/Road/Lane5KvCfg.lean:31 and :37).
Three reads (bitsAtLeaves, bitsAtBits, counts) are on the lookup's matrix. Their weights are three
arrays that the lookup's kind hands in: no formula of them stands here.
That Att/TablesP.lean's tablesP lays just these tables, in this order, is
Johnson/Desc/First/Att/Claims/ReadsOfIs.lean's.

Definitions alone; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Reads.Decl
import Johnson.Desc.First.Att.TablesP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open VerifiableInference.Reads (Make ReadDecl)

/-- The matrices that are read, with their names in the C++ source.
scores (as): numbers that stand one a pair of positions, in planes; cut in NAs parts of equally many
  columns.
rows (ah): numbers that stand one a position: maxima, denominators, bits of the index.
out (ao): the high parts of the division's two remainders.
planes (bA): the bit planes of the lookup's counts.
qkv (qa): queries, keys, values and outputs; another sub-proof has committed to it. -/
inductive Matrix | scores | rows | out | planes | qkv
  deriving DecidableEq, Repr

/-- The weights of a read, by the make of its runs of cells.
short w: an entry is one feature: a run of T cells, one a position, weighed by w.
long zc w: an entry is a block of 2^ls features: a run of 2^ls T cells, weighed on the feature in
  the block by the equality weights of the last ls coordinates of zc, and on the position by w.
part w: an entry is a whole column of one part of the matrix scores: 2^lmS cells, weighed by w.
  There is no axis of positions.
column w: an entry is a whole column of the matrix planes: 2^lmb cells, weighed by w. -/
inductive Weights
  | short (onPosition : Array E)
  | long (zc onPosition : Array E)
  | part (onCell : Array E)
  | column (onCell : Array E)

/-- The names of the reads. u: the number of a unit of a softmax-table call, in the order of
hearing. -/
inductive Read
  /-- the scores' planes at the lookup's point; at the two value products' points -/
  | planesAtKeys | planesAtBelow | planesAtOn
  /-- the maxima at unit u's point -/
  | maxAtUnit (u : Nat)
  /-- the rows at the division's two points, at the division's sumcheck's point, at the drawn
  point, and at the points of the sumchecks for the key and for the bits -/
  | rowsAtDivide | rowsAtIndex | rowsAtProduct | rowsAtDrawn | rowsAtKey | rowsAtBits
  /-- the division's remainders at its point -/
  | outAtDivide
  /-- queries and keys at unit u's sumcheck's point -/
  | queriesAtUnit (u : Nat) | keysAtUnit (u : Nat)
  /-- outputs at the division's sumcheck's point; values at the two value products' points;
  queries at the point of the score at the index; keys at the point of the key at the index -/
  | outputsAtProduct | valuesAtBelow | valuesAtOn | queriesAtIndex | keysAtIndex
  /-- the lookup's three: the counts' bits at its two points, and the counts -/
  | bitsAtLeaves | bitsAtBits | counts
  deriving DecidableEq, Repr

/-- The unit that stands for a number at which there is none: all empty. -/
def noUnit : ScoreP :=
  { call := 0, claim := 0, below := false, pw := #[], zg := #[], zs := #[], zi := #[], zj := #[],
    wI := #[], s0 := 0, sc := { r := #[], ends := 0, row := {} } }

/-- Unit number u of the softmax-table calls. -/
def Pts.unit (p : Pts) (u : Nat) : ScoreP := p.scores.getD u noUnit

/-- **Which matrix a read sums, and under which weights.** g: the place's numbers. lk: what the
lookup's kind hands in: its point zx and its three weight vectors. p: what the claims read of what
was heard. -/
def Read.of (g : Geo) (lk : LookIn) (p : Pts) : Read → Matrix × Weights
  | .planesAtKeys  => (.scores, .part (lastN lk.zx g.lmS))
  | .planesAtBelow => (.scores, .part (lastN (pointM g p.d) g.lmS))
  | .planesAtOn    => (.scores, .part (lastN (pointD g p.d) g.lmS))
  | .maxAtUnit u   => (.rows, .short (tok g (p.unit u).wI (p.unit u).zi))
  | .rowsAtDivide  => (.rows, .short (eqTab p.d.ziW))
  | .rowsAtIndex   => (.rows, .short (eqTab p.d.ziX))
  | .rowsAtProduct => (.rows, .short (eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))))
  | .rowsAtDrawn   => (.rows, .short (eqTab p.x.ti))
  | .rowsAtKey     => (.rows, .short (eqTab (p.x.pi g)))
  | .rowsAtBits    => (.rows, .short (eqTab (p.x.ri2 g)))
  | .outAtDivide   => (.out, .long p.d.zcW (eqTab p.d.ziW))
  | .queriesAtUnit u => (.qkv, .long (lastCoords (p.unit u).sc.r g.ldh)
      (tok g (scoreTiles g (p.unit u)).1 (p.unit u).zi))
  | .keysAtUnit u  => (.qkv, .long (lastCoords (p.unit u).sc.r g.ldh)
      (tok g (scoreTiles g (p.unit u)).2 (p.unit u).zj))
  | .outputsAtProduct => (.qkv, .long p.d.zcW (eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))))
  | .valuesAtBelow => (.qkv, .long p.d.zcW (tok g p.d.wJv (lastCoords p.d.vpm.r g.lB)))
  | .valuesAtOn    => (.qkv, .long p.d.zcW
      (tok g (eqTab (p.d.vpd.r.extract g.lgk (g.lgk + g.lnT))) (lastCoords p.d.vpd.r g.lB)))
  | .queriesAtIndex => (.qkv, .long (p.x.rc g) (eqTab (p.x.ri g)))
  | .keysAtIndex   => (.qkv, .long (p.x.rc g) (eqTab (p.x.pj g)))
  | .bitsAtLeaves  => (.planes, .column lk.phiB0)
  | .bitsAtBits    => (.planes, .column lk.phiB1)
  | .counts        => (.planes, .column lk.phiP)

/-- **All reads of a segment with n units**, in the order in which their tables lie in the vector
of reads. -/
def reads (n : Nat) : List Read :=
  [.planesAtKeys, .planesAtBelow, .planesAtOn] ++ (List.range n).map .maxAtUnit ++
  [.rowsAtDivide, .rowsAtIndex, .rowsAtProduct, .rowsAtDrawn, .rowsAtKey, .rowsAtBits,
   .outAtDivide] ++
  (List.range n).flatMap (fun u => [.queriesAtUnit u, .keysAtUnit u]) ++
  [.outputsAtProduct, .valuesAtBelow, .valuesAtOn, .queriesAtIndex, .keysAtIndex,
   .bitsAtLeaves, .bitsAtBits, .counts]

/-- The field of the record TablesP under which the claims ask for the read's first entry. -/
def Read.field : Read → String
  | .planesAtKeys => "tA" | .planesAtBelow => "tVM" | .planesAtOn => "tVD"
  | .maxAtUnit u => "score[" ++ toString u ++ "].tM"
  | .rowsAtDivide => "hW" | .rowsAtIndex => "hX" | .rowsAtProduct => "hE" | .rowsAtDrawn => "hT"
  | .rowsAtKey => "hPi" | .rowsAtBits => "hR2" | .outAtDivide => "tO"
  | .queriesAtUnit u => "score[" ++ toString u ++ "].tQ"
  | .keysAtUnit u => "score[" ++ toString u ++ "].tK"
  | .outputsAtProduct => "qO" | .valuesAtBelow => "qVM" | .valuesAtOn => "qVD"
  | .queriesAtIndex => "qF" | .keysAtIndex => "qKx"
  | .bitsAtLeaves => "tBit0" | .bitsAtBits => "tBit1" | .counts => "tPin"

/-- What stands in that field: the first entry under which the claims ask for the read's table. -/
def Read.first (t : TablesP) : Read → Nat
  | .planesAtKeys => t.tA | .planesAtBelow => t.tVM | .planesAtOn => t.tVD
  | .maxAtUnit u => (t.score.getD u ⟨0, 0, 0⟩).tM
  | .rowsAtDivide => t.hW | .rowsAtIndex => t.hX | .rowsAtProduct => t.hE | .rowsAtDrawn => t.hT
  | .rowsAtKey => t.hPi | .rowsAtBits => t.hR2 | .outAtDivide => t.tO
  | .queriesAtUnit u => (t.score.getD u ⟨0, 0, 0⟩).tQ
  | .keysAtUnit u => (t.score.getD u ⟨0, 0, 0⟩).tK
  | .outputsAtProduct => t.qO | .valuesAtBelow => t.qVM | .valuesAtOn => t.qVD
  | .queriesAtIndex => t.qF | .keysAtIndex => t.qKx
  | .bitsAtLeaves => t.tBit0 | .bitsAtBits => t.tBit1 | .counts => t.tPin

/-- The number of a matrix, of its first part, in the segment's list: the NAs parts of scores come
first. -/
def Matrix.number (g : Geo) : Matrix → Nat
  | .scores => 0
  | .rows => g.NAs
  | .out => g.NAs + 1
  | .planes => g.NAs + 2
  | .qkv => g.NAs + 3

/-- In how many parts a matrix is committed. -/
def Matrix.parts (g : Geo) : Matrix → Nat
  | .scores => g.NAs
  | _ => 1

/-- The numbers of entries: of a table on scores, all parts together; on rows; on out; on qkv; on
planes. -/
def Geo.nScores (g : Geo) : Nat := g.NAs * (g.kAs / g.NAs)
def Geo.nRows (g : Geo) : Nat := g.fillH
def Geo.nOut (g : Geo) : Nat := g.fillO * g.T / 2 ^ g.la
def Geo.nQkv (g : Geo) : Nat := g.fillQ * g.T / 2 ^ g.la
def Geo.nPlanes (g : Geo) : Nat := g.kbA

/-- The number of entries of a read's table. -/
def Read.count (g : Geo) : Read → Nat
  | .planesAtKeys | .planesAtBelow | .planesAtOn => g.nScores
  | .maxAtUnit _ | .rowsAtDivide | .rowsAtIndex | .rowsAtProduct | .rowsAtDrawn | .rowsAtKey
  | .rowsAtBits => g.nRows
  | .outAtDivide => g.nOut
  | .queriesAtUnit _ | .keysAtUnit _ | .outputsAtProduct | .valuesAtBelow | .valuesAtOn
  | .queriesAtIndex | .keysAtIndex => g.nQkv
  | .bitsAtLeaves | .bitsAtBits | .counts => g.nPlanes

/-- **The first entry of a read's table** in the segment's vector of reads, at n units. It is the
sum of the numbers of entries of the reads before it (starts_running,
Johnson/Desc/First/Att/Claims/ReadsOfIs.lean). -/
def Read.start (g : Geo) (n : Nat) : Read → Nat
  | .planesAtKeys  => 0
  | .planesAtBelow => g.nScores
  | .planesAtOn    => 2 * g.nScores
  | .maxAtUnit u   => 3 * g.nScores + u * g.nRows
  | .rowsAtDivide  => 3 * g.nScores + n * g.nRows
  | .rowsAtIndex   => 3 * g.nScores + (n + 1) * g.nRows
  | .rowsAtProduct => 3 * g.nScores + (n + 2) * g.nRows
  | .rowsAtDrawn   => 3 * g.nScores + (n + 3) * g.nRows
  | .rowsAtKey     => 3 * g.nScores + (n + 4) * g.nRows
  | .rowsAtBits    => 3 * g.nScores + (n + 5) * g.nRows
  | .outAtDivide   => 3 * g.nScores + (n + 6) * g.nRows
  | .queriesAtUnit u => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + 2 * u * g.nQkv
  | .keysAtUnit u  => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * u + 1) * g.nQkv
  | .outputsAtProduct => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + 2 * n * g.nQkv
  | .valuesAtBelow => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 1) * g.nQkv
  | .valuesAtOn    => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 2) * g.nQkv
  | .queriesAtIndex => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 3) * g.nQkv
  | .keysAtIndex   => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 4) * g.nQkv
  | .bitsAtLeaves  => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 5) * g.nQkv
  | .bitsAtBits    => 3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 5) * g.nQkv + g.nPlanes
  | .counts =>
    3 * g.nScores + (n + 6) * g.nRows + g.nOut + (2 * n + 5) * g.nQkv + 2 * g.nPlanes

/-- The make. A block of a long table has 2^ls features. -/
def Weights.make (g : Geo) : Weights → Make
  | .short _ => .short
  | .long _ _ => .long (2 ^ g.ls)
  | .part _ => .part
  | .column _ => .column

/-- The run's length: the number of cells that one entry sums. -/
def Weights.len (g : Geo) : Weights → Nat
  | .short _ => g.T
  | .long _ _ => 2 ^ g.la
  | .part _ => 2 ^ g.lmS
  | .column _ => 2 ^ g.lmb

/-- One weight a cell of a run. In a long table the weight of feature r of the block at position i
has the number r T + i. -/
def Weights.array (g : Geo) : Weights → Array E
  | .short w => w
  | .long zc w => blockRows (eqTab (lastCoords zc g.ls)) w
  | .part w => w
  | .column w => w

/-- **The record of one read**, at n units. -/
def Read.decl (g : Geo) (lk : LookIn) (p : Pts) (r : Read) : ReadDecl E :=
  let weights := (r.of g lk p).2.array g
  { name := r.field
    mat := (r.of g lk p).1.number g
    parts := (r.of g lk p).1.parts g
    make := (r.of g lk p).2.make g
    len := (r.of g lk p).2.len g
    count := r.count g
    start := r.start g p.scores.size
    w := fun j => weights.getD j zeroE }

/-- **The segment's whole declaration**, in the order of the vector of reads. -/
def readsOfK5 (g : Geo) (lk : LookIn) (p : Pts) : List (ReadDecl E) :=
  (reads p.scores.size).map (Read.decl g lk p)

/-- Every read has as many weights as its run has cells. A test on lengths alone. -/
def fit (g : Geo) (lk : LookIn) (p : Pts) : Bool :=
  (reads p.scores.size).all fun r => ((r.of g lk p).2.array g).size == (r.of g lk p).2.len g

/-- **A record's tables as the smallness test takes them**: one a part, each with an equal share of
the entries, one behind the other; all in vector number 2, the vector of reads. Of the weights those
below the run's length are taken, and no other. -/
def tablesOf (d : ReadDecl E) : List Fun1 :=
  let weights := Array.ofFn fun j : Fin d.len => d.w j
  (List.range d.parts).map fun q =>
    ⟨d.mat + q, d.len, weights, 2, d.start + q * (d.count / d.parts)⟩

end VerifiableInference.Desc.First.Att.P
