-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLeaves.lean: the claim on the leaves of a part's key tree and the row on the matrix
that the program makes of it. Definitions and the statement.

A key file's first chain proves that the entries of the committed matrix M lie in their ranges, by
lookups (OnBytes/Key/Ranges.lean, OnBytes/Iop/Wf.lean, OnBytes/Iop/Lkp.lean). The keys of a lookup
are never sent. They come in parts. Key number i of a part belongs to the column i mod 2 ^ kCol and
the place i / 2 ^ kCol. At a place that a run covers the key is a public constant plus a public
combination of entries of one column of M, one for each digit. At any other place, a place of
padding, it is a public value. A part's product tree has the leaves alpha - key. The verifier goes
down the tree and ends with a claim on the leaves: their multilinear extension at a point, plus a
form in mask entries, is a value. The program rewrites that claim in two steps. `Lkp.keysOf` takes
the padding's share out of the target; for that it cuts each stretch of padding into aligned cubes.
`Wf.pendingRow` makes a row on M: weights on the rows of M, a point for its columns, a form in mask
entries and a target.

This file has, over the field: the keys as a function of M (`key`); the table of the leaves in the
form that OnBytes/Slice/KeyTreeMaps.lean takes (`leafTab`); the two steps of the program, with the
program's text where they compute elements (`cubeWeightF`, `takeOutF`, `keysOfF`, `eqTableF`,
`coveredSumF`, `pendingRowF`); and what a row on M says (`TRowF.Holds`). Two things are not kept as
the program has them. The weights on the rows of M are a function of the row's number here, where
the program has a list of structured vectors. And the weights on the keys that `Lkp.keysOf` also
returns are left out: `Wf.pendingRow` does not read them.

Main statement: `Top`. Under the program's own public tests on a lookup and the matrix's size, and
for a point with one coordinate for each bit of a key's number, the claim on the leaves holds
exactly if the row on M holds. It is a definition of type Prop here;
OnBytes/Slice/KeyLeavesFuel.lean proves it (`top`).

Not claimed. `Top` is stated here, not proved. That the functions of this file are the readings of
the program's: the texts are the same where said, and no theorem here compares them. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyTreeMaps
import OnBytes.Iop.Wf

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Slice.PscF (World scaleForm)

/-! ## The equality vector, by numbers -/

/-- eq(j, z): the product over the coordinates x of z of x if the matching bit of j is 1, and of
1 - x if it is 0. The first coordinate goes with the lowest bit. -/
def eqW : List GE → ℕ → GE
  | [], _ => 1
  | x :: xs, j => (if j % 2 = 1 then x else 1 - x) * eqW xs (j / 2)

/-! ## The keys of a part, as a function of the matrix -/

/-- The public elements of a lookup: the offset, what a place of padding holds, and one weight for
each digit. -/
structure LkF where
  off : GE
  pad : GE
  dw : List GE

/-- The key at a place that the run r covers, in a column. M: the matrix, by row and column. -/
def runKey (L : LkF) (M : ℕ → ℕ → GE) (r : WfRun) (place col : ℕ) : GE :=
  L.off + (L.dw.zipIdx.map fun w =>
    w.1 * M (r.firstRow + (place - r.firstPlace) + w.2 * r.stride) col).sum

/-- The key at a place, in a column: that of the first run that covers the place, or the padding's
value. -/
def keyAt (L : LkF) (M : ℕ → ℕ → GE) : List WfRun → ℕ → ℕ → GE
  | [], _, _ => L.pad
  | r :: rs, place, col =>
    if r.firstPlace ≤ place ∧ place < r.firstPlace + r.places then runKey L M r place col
    else keyAt L M rs place col

/-- Key number i of a part. -/
def key (L : LkF) (M : ℕ → ℕ → GE) (kCol : ℕ) (runs : List WfRun) (i : ℕ) : GE :=
  keyAt L M runs (i / 2 ^ kCol) (i % 2 ^ kCol)

/-! ## The table of the leaves -/

open Classical in
/-- 0 for the element 0, and 1 for any other. -/
noncomputable def bitN (x : GE) : ℕ := if x = 0 then 0 else 1

/-- The number whose bits, the highest first, are those of a and then the list's. -/
noncomputable def numFrom : ℕ → List GE → ℕ
  | a, [] => a
  | a, x :: q => numFrom (2 * a + bitN x) q

/-- The table of the leaves alpha - key, on lists of 0 and 1 with the highest bit of the key's
number first. -/
noncomputable def leafTab (α : GE) (k : ℕ → GE) : List GE → GE := fun q => α - k (numFrom 0 q)

/-! ## The first step: the padding's share leaves the target -/

/-- x if the bit is set, 1 - x if not. -/
def pickF (bit : Bool) (x : GE) : GE := if bit then x else 1 - x

/-- The sum of the equality vector at z over a cube. -/
def cubeWeightF (c : Lkp.Cube) (z : List GE) : GE :=
  ((List.range z.length).zip z).foldl (fun w p =>
    if c.mask.testBit p.1 then w * pickF (c.value.testBit p.1) p.2 else w) 1

/-- What the making of a claim on the keys carries along: the target so far, and for each block of
tree numbers the weight of its real places. -/
structure KeyAccF where
  target : GE
  real : List GE

/-- The places of a cube hold one row of the table: the row's share is subtracted from the target.
rowV: the rows of the table. -/
def takeOutF (rowV : ℕ → GE) (point : List GE) (a : KeyAccF) (cube : Lkp.Cube) (row : ℕ)
    (block : Option ℕ) : KeyAccF :=
  let weight := cubeWeightF cube point
  { target := a.target - weight * rowV row
    real :=
      match block with
      | some b => a.real.set b (a.real.getD b 0 - weight)
      | none => a.real }

/-- The claim on one part of the keys, without its weights. -/
structure KeysF where
  point : List GE
  masks : PscF.MaskForm
  target : GE

/-- The claim on the leaves of one part's tree, rewritten as a claim on the real keys. natV: a
number as an element. -/
def keysOfF (S : Lkp.Public) (rowV natV : ℕ → GE) (θ α : GE) (part : ℕ)
    (onLeaves : PscF.PointClaim) : KeysF :=
  let point := onLeaves.point
  let start : KeyAccF :=
    { target := α - onLeaves.value
      real := S.keys.map fun b =>
        if b.function.isNone then 0 else cubeWeightF (Lkp.cubeOfBlock S b) point }
  let a1 := (S.keys.filter (·.function.isNone)).foldl
    (fun a b => takeOutF rowV point a (Lkp.cubeOfBlock S b) b.paddingRow none) start
  let a2 := (S.padding.filter (·.part == part)).foldl (fun a p =>
    let b := S.keys.findIdx fun k => k.holds S.g p.first
    (Lkp.cubesOf p point.length).foldl (fun a c => takeOutF rowV point a c p.row (some b)) a) a1
  let target := (S.keys.zip a2.real).foldl (fun t q =>
    match q.1.function with
    | some n => if n == 0 then t else t - θ * natV n * q.2
    | none => t) a2.target
  { point := point
    masks := scaleForm (-1) onLeaves.masks
    target := target }

/-! ## The second step: a row on the matrix -/

/-- The weights of all corners: entry j is eq(j, z). -/
def eqTableF (z : List GE) : List GE :=
  z.foldl (fun out x =>
    let hi := out.map fun w => w * x
    List.zipWith (· - ·) out hi ++ hi) [1]

/-- The equality vector at the place coordinates of a claim's point. -/
def eqPlacesF (kCol : ℕ) (point : List GE) : List GE := eqTableF (point.drop kCol)

/-- The sum of values[first], .., values[first + count - 1], as far as the list goes. -/
def sumSliceF (values : List GE) (first count : ℕ) : GE := ((values.drop first).take count).sum

/-- The sum of the equality vector over the places that the runs cover. -/
def coveredSumF (runs : List WfRun) (e : List GE) : GE :=
  runs.foldl (fun s r => s + sumSliceF e r.firstPlace r.places) 0

/-- The row weight scale * values[first + i] on the row firstRow + i, i < count, and 0 elsewhere. -/
def rowsW (firstRow : ℕ) (values : List GE) (first count : ℕ) (scale : GE) (row : ℕ) : GE :=
  if firstRow ≤ row ∧ row < firstRow + count then scale * values.getD (first + (row - firstRow)) 0
  else 0

/-- A row on the matrix: weights on its rows, a point for its columns, a form in mask entries, a
target. -/
structure TRowF where
  g : ℕ → GE
  psi : List GE
  masks : PscF.MaskForm
  target : GE

/-- The row holds of the matrix M of nRows rows and 2 ^ kCol columns, in the world W. -/
def TRowF.Holds (W : World) (M : ℕ → ℕ → GE) (nRows kCol : ℕ) (t : TRowF) : Prop :=
  (∑ r ∈ Finset.range nRows, ∑ c ∈ Finset.range (2 ^ kCol), t.g r * eqW t.psi c * M r c) +
    W.form t.masks = t.target

/-- The pending row of one part, from the claim on its keys. e: the equality vector at the place
coordinates. -/
def pendingRowF (kCol : ℕ) (L : LkF) (runs : List WfRun) (claim : KeysF) (e : List GE) : TRowF where
  g := fun row => (runs.flatMap fun r =>
    L.dw.zipIdx.map fun w =>
      rowsW (r.firstRow + w.2 * r.stride) e r.firstPlace r.places w.1 row).sum
  psi := claim.point.take kCol
  masks := claim.masks
  target := claim.target - coveredSumF runs e * L.off

/-! ## The statement -/

/-- The claim on the leaves holds exactly if the row on the matrix holds. m: the matrix's size.
l: a lookup that passes the program's tests by itself and with m. p: its part number i. L: its
public elements; there is a weight for each digit, and the table's row at the padding's number is
the padding's value. c: a claim whose point has one coordinate for each bit of a key's number. -/
def Top : Prop :=
  ∀ (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (L : LkF) (rowV natV : ℕ → GE)
    (θ α : GE) (W : World) (M : ℕ → ℕ → GE) (c : PscF.PointClaim),
    m.ok = true → Wf.lookupOk Wf.fBits l = true → Wf.fitsMatrix m l = true → l.parts[i]? = some p →
    L.dw.length = l.digitWeight.length → rowV l.paddingKey.toNat = L.pad →
    c.point.length = m.kCol + p.logPlaces →
    (c.Holds W (treeMap (m.kCol + p.logPlaces) (leafTab α (key L M m.kCol p.runs))) ↔
      (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).Holds W M m.rows m.kCol)

end OnBytes.Slice.Leaves
