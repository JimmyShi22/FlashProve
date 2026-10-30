-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Wf.lean: the block WF, the committer's proof that the entries of the committed matrix
lie in their ranges.

The C++ counterpart is blocks/iop/wf.h.

Before the block: a matrix M that a committed table holds, and the public lookups of the parameter
item "ranges". OnBytes/Key/Ranges.lean says what they mean and defines key, digit, part, place, run,
padding and plane. The keys are never sent.

Words of OnBytes/Iop/Ground.lean. A row is a linear claim with a public target on what oracle
messages hold. A group is the set of oracle messages that one proximity test reads together. A block
is read twice: the dry run states its rounds and computes no value, and the run on a view makes the
tests on what was read from a file. Masks ride if `choice.masksRide` is set: the fresh
mask of the proximity test's first fold then comes in the prover's message that holds the block's
oracle message (`messageOf`), and the masks of the later stages in the message of the switch that
makes their stage (OnBytes/Iop/Prox.lean).

The course of the block.
 1. The caller has sent and sampled the index-mask message, an oracle message with mask rows only.
 2. The prover sends one oracle message. Its main rows hold the real planes of the multiplicities
    of all lookups, in bits. Its mask rows hold the mask entries of the lookups' sumchecks,
    except those of the claims on keys. If masks ride, the fresh mask of the first fold of the
    block's own proximity test goes out with it.
 3. Each lookup runs in turn (OnBytes/Iop/Lkp.lean). Its rows go into the group of that one oracle
    message. For each part it hands on a claim on the part's keys.
 4. Each such claim becomes a row on the matrix (`TensorRow`), whose mask entries lie in the
    index-mask message. These pending rows are the block's result. The caller hands them to the
    test on the committed table.
 5. The proximity test on the group closes everything else.

The block makes one test of its own on values: the weights that a lookup hands on add up to the
sum of the equality vector over the places that the runs cover. Which places are covered is said
twice, both times from the same public runs: `lookupOf` tells the lookup its padding, and
`pendingRow` puts the weights on the matrix's rows. The test compares the two descriptions. It is
meant to catch a fault in the verifier's own text: where the two agree it holds at every point, so
no file can make it fail. Where it fails, wf.h ends the process (BLK_REQUIRE); here the block fails.

Main definitions: `Wf.lookupsOf`, `Wf.admitted`, `Wf.indexMaskEntries`, `Wf.rowsBatched`,
`Wf.planesAt`, `Wf.weightsOnRows`, `Wf.pendingRow`, `Wf.dryRow`, `Wf.Output`, `Wf.rowsVerify`,
`Wf.verify`.

Not claimed here: soundness or hiding. No theorem is stated here. A key is an element of the base
field. That it is the integer that it looks like is not tested: the reader concludes it from the
parameters, since digits in small ranges under weights of a few bits cannot wrap around the prime.
-/
import OnBytes.Key.Ranges
import OnBytes.Iop.Batt
import OnBytes.Iop.Lkp
import OnBytes.Iop.Prox

namespace OnBytes.Wf

open OnBytes.Params (WfRun WfPart WfLookup WfPublic LinShape)

/-! ## What follows from the parameters -/

/-- The places lo, .., hi - 1 of part `number` as one run of padding that holds row `row` of the
range table. A place is 2^kCol consecutive key numbers. The empty list if lo is not below hi. -/
def stretch (kCol number row lo hi : Nat) : List Lkp.Padding :=
  if lo < hi then
    [{ part := number, first := lo * 2 ^ kCol, logStep := 0, length := (hi - lo) * 2 ^ kCol,
       row := row }]
  else []

/-- The padding of a part from the place `upto` on, appended to what `acc` holds already: every
stretch of places from there on that no run covers. -/
def paddingFrom (kCol number row logPlaces : Nat) :
    Nat → List WfRun → Array Lkp.Padding → Array Lkp.Padding
  | upto, [], acc => acc ++ stretch kCol number row upto (2 ^ logPlaces)
  | upto, r :: rs, acc =>
    paddingFrom kCol number row logPlaces (r.firstPlace + r.places) rs
      (acc ++ stretch kCol number row upto r.firstPlace)

/-- One lookup as the block LKP takes it. -/
def lookupOf (messageId : Nat) (m : Matrix) (l : WfLookup) : Lkp.Public where
  parts := l.parts.map fun p => p.logPlaces + m.kCol
  d := l.d
  mu := l.mu
  live := l.live
  readFrom := [messageId]
  keys := [{ first := 0, logTrees := 0, function := some 0, paddingRow := 0 }]
  tables := [{ first := 0, logRows := l.d, function := 0, rows := [] }]
  padding := l.parts.zipIdx.flatMap fun p =>
    (paddingFrom m.kCol p.2 l.paddingKey.toNat p.1.logPlaces 0 p.1.runs #[]).toList
  lastKeyLevelOrder := l.firstBound

/-- The lookups as the block LKP takes them. -/
def lookupsOf (x : WfPublic) (m : Matrix) : List Lkp.Public :=
  x.lookups.map (lookupOf x.messageId m)

/-- The entries of the index-mask message that the lookups take: two for each part. -/
def indexMasks (x : WfPublic) (m : Matrix) : Nat :=
  sumT ((lookupsOf x m).map Lkp.keyMasks)

/-- All that a key's one-time chain takes of the index-mask message: the lookups' entries, and what
the batching of the pending rows into one (`Batt.verify`) takes if there is more than one. Whoever
sizes that message (OnBytes/Plan/KeyOneTime.lean) or asks whether it has room
(OnBytes/Key/Fixed.lean) calls this function, so that the count is written once. -/
def indexMaskEntries (x : WfPublic) (m : Matrix) : Nat :=
  indexMasks x m +
    (if 1 < sumT (x.lookups.map (·.parts.length)) then Batt.masksOf m.kCol else 0)

/-- The entries of the block's own mask rows that the lookups take. -/
def ownMasks (x : WfPublic) (m : Matrix) : Nat :=
  sumT ((lookupsOf x m).map fun p => Lkp.allMasks p - Lkp.keyMasks p)

/-- The rows that the block's proximity test batches: the sample rows of the oracle message, and
what the lookups leave. A lookup leaves one row for each step of the tie (step 1 at `Lkp.run` in
OnBytes/Iop/Lkp.lean; there is one step fewer than there are real planes), one for each part except
the first, one for each level of each part's tree and of the table's tree, one for the leaves, two
for the bits and one for the number of keys. -/
def rowsBatched (x : WfPublic) (m : Matrix) : Nat :=
  x.message.shape.answers +
    sumT ((lookupsOf x m).map fun p =>
      (p.planes - 1) + (p.parts.length - 1) + p.d + 1 + 2 + 1 + sumT p.parts)

/-- The length in bits of the prime of the base field. -/
def fBits : Nat := 64

/-- The conditions on the item "ranges" by itself: there is a lookup; the oracle message has main
rows over the base field and mask rows, and is sampled; each lookup is in order. -/
def publicOk (x : WfPublic) : Bool :=
  !x.lookups.isEmpty &&
  x.message.shape.mainRows != 0 && x.message.shape.maskRows != 0 &&
  x.message.shape.mainDeg == 1 && decide (1 ≤ x.message.shape.answers) &&
  x.lookups.all (lookupOk fBits)

/-- The conditions on the item "ranges" together with the matrix's size and the codes.
 - The item is in order by itself, and so is the matrix's size.
 - Each lookup fits the matrix.
 - Some lookup that takes single entries as keys, with the weight 1, reaches every row of the
   matrix: the block is to say that every entry of the matrix is in its range.
 - The oracle message names codes that are there.
 - The largest block of planes fits a main row, and the blocks fill exactly the main rows.
 - The mask rows have room for the lookups' masks.
 - The first stage of the proximity test has the oracle message's codes, and the sizes of the
   stages fit each other and the codes (`ioppOk`). -/
def admitted (codes : Codes) (x : WfPublic) (m : Matrix) : Bool :=
  let s := x.message.shape
  publicOk x && m.ok &&
  x.lookups.all (fitsMatrix m) &&
  x.lookups.any (coversAllRows m) &&
  decide (s.code < codes.base.size) && decide (s.maskCode < codes.mask.size) &&
  (let ell := (codes.base.getD s.code default).ell
   let blocks := layout x.lookups ell
   (blocks.head?.any fun b => decide (2 ^ b.bits ≤ ell)) &&
   (blocks.getLast?.any fun b => b.row + 1 == s.mainRows)) &&
  decide (ownMasks x m ≤
    Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers) &&
  (x.stages.head?.any fun t => t.code == s.code && t.maskCode == s.maskCode) &&
  ioppOk codes x.stages s.answers

/-- What the prover's message holds, in order: the oracle message and, if masks ride, the fresh mask
of the first fold of the block's proximity test, under the same class of leaves. -/
def messageOf (x : WfPublic) : Array OracleNotice :=
  match x.stages.head? with
  | some t =>
    if x.choice.masksRide then
      #[x.message,
        foldMaskNotice { ioppFoldShape t {} with maskLeafClass := x.message.leafClass }]
    else #[x.message]
  | none => #[x.message]

/-- Adds a vector on the multiplicities of lookup i to a row. The vector has mu + d variables, the
plane in the low ones. Only the real planes are read. v must be of product form: a written-out
factor is silently dropped (`Lkp.setBits`). -/
def planesAt (x : WfPublic) (codes : Codes) (i : Nat) (row : Row) (v : Tensor) : Row :=
  let s := x.message.shape
  let code := codes.base.getD s.code default
  let mu := (x.lookups.getD i default).mu
  ((layout x.lookups code.ell).filter (·.lookup == i)).foldl
    (fun r b =>
      r.add x.messageId .main
        (((Lkp.onBlock v mu (b.first, b.logPlanes)).insertChoice b.bits (code.logEll - b.bits)
          (b.firstPlace / 2 ^ b.bits)).insertChoice 0 (ceilLog2 s.mainRows) b.row))
    row

/-! ## A pending row -/

/-- rowBlockBits kRow start stop fuel d: the logarithm of the largest aligned block of rows that
begins at `start` and ends at or before `stop`, at most kRow. d is the logarithm reached so far; a
caller gives 0. fuel bounds the search; kRow suffices, since each step adds 1 to d and is made only
while d is below kRow. -/
def rowBlockBits (kRow start stop : Nat) : Nat → Nat → Nat
  | 0, d => d
  | fuel + 1, d =>
    if d < kRow && start % 2 ^ (d + 1) == 0 && start + 2 ^ (d + 1) ≤ stop then
      rowBlockBits kRow start stop fuel (d + 1)
    else d

/-- weightsFrom kRow values scale stop fuel start first: row weights scale * values[first + i] on
the rows start + i below stop, and 0 elsewhere, as vectors on aligned blocks of rows. All blocks
read the one written-out vector `values`. fuel bounds the number of blocks; the number of rows
suffices, since each block covers at least one row. -/
def weightsFrom (kRow : Nat) (values : Array E) (scale : E) (stop : Nat) :
    Nat → Nat → Nat → List Tensor
  | 0, _, _ => []
  | fuel + 1, start, first =>
    if start < stop then
      let d := rowBlockBits kRow start stop kRow 0
      let t : Tensor :=
        if d == 0 then
          ({ scalar := mulE (values.getD first zeroE) scale } : Tensor).insertChoice 0 kRow start
        else
          ((({ scalar := scale } : Tensor).pushDense d).insertChoice d (kRow - d)
            (start / 2 ^ d)).setValues values first
      t :: weightsFrom kRow values scale stop fuel (start + 2 ^ d) (first + 2 ^ d)
    else []

/-- Row weights scale * values[first + i] on the rows firstRow + i, i < count, and 0 elsewhere. -/
def weightsOnRows (kRow firstRow : Nat) (values : Array E) (first count : Nat) (scale : E) :
    List Tensor :=
  weightsFrom kRow values scale (firstRow + count) count firstRow first

/-- The sum of values[first], .., values[first + count - 1], as far as the array goes. -/
def sumSlice (values : Array E) (first count : Nat) : E :=
  values.foldl addE zeroE first (first + count)

/-- The sum of all entries of a coefficient vector whose summands are product forms and single
entries. -/
def sumOfForm (c : Form) : E :=
  let products := c.tensors.foldl
    (fun s t => addE s (t.pairs.foldl (fun r p => mulE r (addE p.1 p.2)) t.scalar)) zeroE
  c.entries.foldl (fun s e => addE s e.2) products

/-- The equality vector at the place coordinates of a claim's point: coordinate t belongs to bit t
of the place. -/
def eqPlaces (m : Matrix) (point : List E) : Array E := eqTable (point.drop m.kCol)

/-- The sum of the equality vector over the places that a part's runs cover. -/
def coveredSum (p : WfPart) (e : Array E) : E :=
  p.runs.foldl (fun s r => addE s (sumSlice e r.firstPlace r.places)) zeroE

/-- The pending row of one part, from the claim that the lookup hands on:
  sum over the key numbers i of weights[i] * key[i] + (mask form) = target.
weights[i] is eq(point, i) at a covered place and 0 at a place of padding, whose share the lookup
has already moved into the target. The point is (column | place), the column in the low
coordinates. A key is (OnBytes/Key/Ranges.lean)
  offset + sum over the digits q of digitWeight[q] * M[row of (place, q)][column].
With e the equality vector at the place coordinates, and since the weights on the columns add up to
1, the sum over the key numbers is
  < g (x) eq(column point, .), M > + offset * (sum of e over the covered places),
where g[row of (place, q)] = e[place] * digitWeight[q] on the covered places, added up where rows
meet, and 0 elsewhere. The term with the offset is moved into the row's target. The caller hands in
e = `eqPlaces m claim.point`. -/
def pendingRow (m : Matrix) (l : WfLookup) (p : WfPart) (claim : Lkp.Keys) (e : Array E) :
    TensorRow where
  g := p.runs.flatMap fun r =>
    l.digitWeight.zipIdx.flatMap fun w =>
      weightsOnRows m.kRow (r.firstRow + w.2 * r.stride) e r.firstPlace r.places (ofF w.1)
  psi := claim.point.take m.kCol
  masks := claim.masks
  target := subE claim.target (mulE (coveredSum p e) (ofF l.offset))

/-- What the dry run takes in place of a pending row, with no arithmetic in it: the claim's column
point and mask form, the target 0, and one weight vector on the matrix's row variables, where a
pending row has one for each aligned block of rows of each run and digit. It agrees with the pending
row in what later blocks test of a row in both readings (`Batt.fits`, `memberRowsFit`): it has a
weight vector, each weight vector has kRow variables, and the column point and the mask entries are
the same. -/
def dryRow (m : Matrix) (claim : Lkp.Keys) : TensorRow where
  g := [({} : Tensor).insertChoice 0 m.kRow 0]
  psi := claim.point.take m.kCol
  masks := claim.masks
  target := zeroE

/-! ## The block -/

/-- What the block hands on. -/
structure Output where
  /-- the rows on the matrix, one for each part of each lookup, in their order. Without the test on
  the committed table that takes them, the block says nothing about the matrix. In wf.h the process
  ends if they are dropped (WfPending). Here nothing enforces it: the caller must hand on all of
  them. -/
  pending : List TensorRow := []
  /-- the number of the oracle message with the multiplicities -/
  message : Nat := noId
  /-- the group of that oracle message -/
  group : Nat := noId
  deriving Inhabited

/-- The conditions at the start of the block: the parameters are admitted; the index-mask message
is a sampled message with mask rows only; the oracle message has as many answers to a sample as the
plan's setting says. The index-mask message must be fixed, and its sample answered, before any
challenge is drawn under which a value of the matrix is shown. That order is meant to keep a mask
from being chosen after its challenge, when it could be fitted to a false value. -/
def startCheck (x : WfPublic) (m : Matrix) (indexMasksId : Nat) : Blk Unit := do
  let st ← Blk.statement
  Blk.must (admitted st.codes x m)
  let o ← Blk.oracle indexMasksId
  Blk.must (o.sampled && o.shape.mainRows == 0)
  let c ← getThe Ctx
  Blk.must (x.message.shape.answers == c.ch.samples)

/-- The pending rows of one lookup, from the claims on its parts. Fails in both readings if there
are not as many claims as parts, if a claim's point does not have one coordinate for each bit of a
key's number, or if a claim's weights have a written-out factor. Fails in the run on a view if the
weights do not add up to the sum of the equality vector over the covered places (see the head of
this file). The arithmetic is done only in the run on a view; the dry run takes `dryRow`. done: the
rows so far, the last one first; the new rows are put in front of them, so the result is in reverse
order. -/
def pendingOf (m : Matrix) (l : WfLookup) : List WfPart → List Lkp.Keys → List TensorRow →
    Blk (List TensorRow)
  | p :: ps, claim :: claims, done => do
    Blk.must (claim.point.length == m.kCol + p.logPlaces)
    Blk.must (claim.weights.tensors.all (·.denseVars.isEmpty))
    let e ← Blk.onView #[] fun _ => eqPlaces m claim.point
    Blk.testOnView fun _ => sumOfForm claim.weights == coveredSum p e
    let row ← Blk.onView (dryRow m claim) fun _ => pendingRow m l p claim e
    pendingOf m l ps claims (row :: done)
  | [], [], done => pure done
  | _, _, _ => Blk.fail

/-- The lookups from number i on, each with its pending rows. done: the rows of the lookups before,
the last one first; the result is in the order of the lookups and of their parts. There are as many
lookups and parts as the item "ranges" says, and no test bounds their number. So this function and
`pendingOf` call themselves as the last thing that they do, for the stack not to grow with them. -/
def lookupsVerify (x : WfPublic) (m : Matrix) (codes : Codes) (group indexMasksId : Nat) :
    Nat → List WfLookup → List TensorRow → Blk (List TensorRow)
  | _, [], done => pure done.reverse
  | i, l :: ls, done => do
    let left ← Lkp.verify (lookupOf x.messageId m l) (planesAt x codes i) x.messageId group
      (some indexMasksId)
    let mine ← pendingOf m l l.parts left.keys done
    lookupsVerify x m codes group indexMasksId (i + 1) ls mine

/-- The block without its proximity test (wf_rows_verify in wf.h): the oracle message and the
lookups. The multiplicities are received and sampled before the first lookup draws its alpha. The
protocol's argument for the lookup's first error term rests on this order, and `Lkp.verify` fails
if the sample is not answered. Fails if the oracle message gets another number than the parameters
say. Returns also the number of the oracle message that holds the first fold's mask, if masks ride.
Without the test nothing is shown; `verify` is this and the test, and it is the only caller. In
wf.h a type fences this routine off from other callers (WfRowsAlone); here nothing does. -/
def rowsVerify (x : WfPublic) (table : LinShape) (indexMasksId : Nat) :
    Blk (Output × Option Nat) := do
  let m := matrixOf table
  startCheck x m indexMasksId
  let ids ← sendVerify (messageOf x)
  let message ← Blk.get ids[0]?
  Blk.must (message == x.messageId)
  let s := x.message.shape
  let group ← Blk.newGroup s.code s.maskCode
  Blk.join group message
  let st ← Blk.statement
  let pending ← lookupsVerify x m st.codes group indexMasksId 0 x.lookups []
  pure (⟨pending, message, group⟩, if x.choice.masksRide then ids[1]? else none)

/-- The block WF on the verifier's side (wf_verify in wf.h). table: the shape of the test on the
committed table. The matrix's size is taken from it and from nowhere else. If the item "ranges" held
the size too, the two could differ: ranges that count one row fewer than the test would leave that
row unread, and every test would pass. indexMasksId: the number of the index-mask message. -/
def verify (x : WfPublic) (table : LinShape) (indexMasksId : Nat) : Blk Output := do
  let (out, firstMask) ← rowsVerify x table indexMasksId
  ioppVerify out.group x.stages x.choice firstMask
  pure out

end OnBytes.Wf
