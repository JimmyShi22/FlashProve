-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionTables.lean: the tables of the attention sub-proof.

This is part 3 of the check of the attention sub-proof (OnBytes/Model/Attention.lean), after the
prover's commitment to the array of tables. It follows step 8 of the function run of
verifier/src/vf_attention_check.h. OnBytes/Model/AttentionHeard.lean explains the terms,
OnBytes/Model/Frame.lean the smallness test.

What this file does. From what parts 1 and 2 have stored it computes, for each table, the matrix,
the block length, the weight vector and the first entry in the array. The order of the tables is
fixed. It decides which entry of the committed array a claim reads. The sections below say what a
table is, why the weight vectors are not computed in the dry run, and which tests are made.

Main definitions: Placed, PlaceM, PlaceM.weights, add, addAs, lastN, tok, lng, scoreTiles, pointM,
pointD, mergedPlanes, mergedTokens, placeAll, tables, tablesNames.

This file reads no message of the prover and draws no challenge. It does not test that a weight
vector has the length of its block: the smallness test does, where it adds its claims (objectsF in
OnBytes/Model/Tail.lean). The C++ routine add checks at every table that the list of tables is still
open (funOpen). The function add of this file does not: run (OnBytes/Model/Attention.lean) checks it
once, before it calls tables, and closes the list with what tables returns. The file holds no
theorem. The smallness test is meant to tie every entry of a table to its matrix; no theorem here
says that it does.
-/
import OnBytes.Model.AttentionHeard

namespace OnBytes.Attention

/-! ## Placing one table after the other

What a table is. Let M be one of the committed matrices, with m rows and k columns. Let len
divide m, and let phi be a public vector of len weights. The table of M under phi has k (m / len)
entries. Entry c (m / len) + s is the sum over y below len of phi[y] M[s len + y][c]: column c,
block s of len rows, weighted by phi. The prover commits to all tables in one array, one after the
other. The claims (part 6) read a matrix only through entries of its tables. The smallness test is
meant to tie every entry to its matrix; no theorem here says that it does.

The matrices are `as` (committed in NAs parts, each a matrix of its own in the list), ah, ao, bA and
qa. OnBytes/Model/AttentionHeard.lean says what each holds and where a cell of `as` is. A block of a
part of `as` is a whole column of 2^lmS rows, so column c of `as` is entry c of a table on `as`.
-/

/-- The tables placed so far. -/
structure Placed where
  /-- the first entry of the array that no table has taken -/
  next : Nat := 0
  /-- pairs (a table's first entry, its length), the newest first -/
  tabLen : List (Nat × Nat) := []
  /-- the tables as the smallness test takes them, in their order -/
  funs : Array Model.HFun := #[]

/-- An action that places tables: a function in the type Blk (OnBytes/Iop/Ground.lean) that also
carries the tables placed so far. Of Blk it uses only the refusal and the flag that says whether
this is the dry run. A test has the name under which the C++ verifier refuses, without the
sub-proof's prefix (see tablesNames), by a reading of the C++ source (no theorem). -/
abbrev PlaceM : Type → Type := StateT Placed Blk

/-- The value of x. Whether x has a value depends only on public numbers. Refuses under the name if
it has none. -/
def PlaceM.getAs {α : Type} (name : String) (x : Option α) : PlaceM α :=
  match x with
  | some a => pure a
  | none => StateT.lift (Model.refuse name)

/-- A weight vector of len entries. In the run on a view, which holds the values read from a proof
file, it is f (). The dry run takes len zeros and does not compute f: no test of the dry run reads a
value, and of a weight vector its tests read only the length. -/
def PlaceM.weights (len : Nat) (f : Unit → Array E) : PlaceM (Array E) :=
  StateT.lift (Blk.onView (Array.replicate len zeroE) f)

/-- The tables placed so far. -/
def PlaceM.placed : PlaceM Placed := fun t => pure (t, t)

/-- True if the list has a matrix number mat, len is not 0 and divides the number m of its rows,
and elems is k (m / len), with k the number of its columns. -/
def fits (mats : Array Model.TMat) (mat len elems : Nat) : Bool :=
  match mats[mat]? with
  | none => false
  | some M => len != 0 && M.m % len == 0 && elems == M.k * (M.m / len)

/-- Places a table of elems entries on matrix number mat, with blocks of len rows and the weights
phi, after the tables placed so far. Returns its first entry. Refuses unless the number of entries
is the one that the matrix and the block length give. The table is in the vector U3
(HFun.tree = 2). -/
def add (mats : Array Model.TMat) (mat len : Nat) (phi : Array E) (elems : Nat) : PlaceM Nat :=
  fun t => do
    Model.mustAs "internal-a-table-length" (fits mats mat len elems)
    let table : Model.HFun := { mat := mat, len := len, phi := phi, tree := 2, start := t.next }
    pure (t.next, { next := t.next + elems, tabLen := (t.next, elems) :: t.tabLen,
                    funs := t.funs.push table })

/-- Stores, under the entry start, the length of all tables placed from there on. The pair of the
first of these tables, which has the same first entry, stays in the list. The new pair comes before
it, so a search from the front finds the new one. (The C++ map overwrites the old length.) -/
def PlaceM.total (start : Nat) : PlaceM Unit := fun t =>
  pure ((), { t with tabLen := (start, t.next - start) :: t.tabLen })

/-- Places a table on `as`. The prover commits to `as` in parts, which are the first matrices of
the list. A block is a whole column. The table is the tables of the parts side by side, all under
the weights that phi gives. Returns the first entry of the first part's table. Under that entry the
total length is stored. -/
def addAs (S : Shape) (mats : Array Model.TMat) (phi : Unit → Array E) : PlaceM Nat := do
  let phi ← PlaceM.weights (2 ^ S.cf.lmS) phi
  let start := (← PlaceM.placed).next
  (List.range S.cf.NAs).forM fun q =>
    discard (add mats q (2 ^ S.cf.lmS) phi (S.kAs / S.cf.NAs))
  PlaceM.total start
  pure start

/-! ## Weight vectors

The dry run is a first pass of the check on zeros, which only yields the list of rounds
(OnBytes/Iop/Ground.lean). That list does not depend on a weight, and the weight vectors are the
heavy part of this file: at full size, that is at lt 10, la 16, lmS 16, lmb 14, with `as` in one
part and two units of kind KFD, they have 909,312 entries in all. So each is computed under
PlaceM.weights, which in the dry run returns zeros of the same length.
-/

/-- The last n coordinates of a point; all of z if it has fewer than n. -/
def lastCoords (z : Array E) (n : Nat) : Array E := z.extract (z.size - n) z.size

/-- The equality weights of the last n coordinates of a point: 2^n weights. -/
def lastN (z : Array E) (n : Nat) : Array E := Model.eqTab (lastCoords z n)

/-- Token weights from tile weights. A token is a tile and a position within the tile. The token at
position x of tile I gets hi[I] times the equality weight of the point lo at x. Meant for hi of nT
entries and lo of lB coordinates. A missing weight counts as 0, and no later test sees it, since the
result always has T entries. The callers cut hi and lo from points whose lengths follow from the
shape. -/
def tok (S : Shape) (hi lo : Array E) : Array E :=
  let el := Model.eqTab lo
  (Array.range S.T).map fun i => mulE (hi.getD (i / S.B) zeroE) (el.getD (i % S.B) zeroE)

/-- The weights of a block of 2^ls neighbouring features, all tokens of each. zc is a point on the
features within a head, of ldh coordinates, of which only the last ls are used here. ptk gives the
token weights. The row of token t of the feature with low bits c gets the equality weight of those
coordinates at c times ptk[t]. Refuses unless there is a weight for each token, a block has 2^la
rows, and zc has at least ls coordinates. -/
def lng (S : Shape) (zc : Array E) (ptk : Unit → Array E) : PlaceM (Array E) := do
  let tokens ← PlaceM.weights S.T ptk
  Model.mustAs "plan-tensor-layout" (tokens.size == S.T && 2 ^ S.cf.la == 2 ^ S.ls * S.T)
  let c ← PlaceM.getAs "plan-tensor-layout" (Model.cutLast zc S.ls).toOption
  PlaceM.weights (2 ^ S.cf.la) fun _ => Model.blockRows (Model.eqTab c.2) tokens

/-- The tile weights of a unit of kind KFD at the point of its sumcheck: for the tile rows, and for
the tile columns. Below the diagonal the point has coordinates for a slot row and for a tile slot,
and a tile row or column gets the sum of the weights of its tile slots (tileSums). On the diagonal a
tile's row is its column, and both are the equality weights of the point's tile coordinates. -/
def scoreTiles (S : Shape) (k : Score) : Array E × Array E :=
  let r := k.sc.r
  let g := S.cf.lgk
  if k.seg == Seg.fm then
    tileSums S (Model.eqTab (r.extract g (g + S.lnT - 1)))
      (Model.eqTab (r.extract (g + S.lnT - 1) (g + 2 * S.lnT - 1)))
  else
    let e := Model.eqTab (r.extract g (g + S.lnT))
    (e, e)

/-! ## Points -/

/-- The point at which the value product below the diagonal reads `as`. From its sumcheck's
point come the head g of keys and values, the slot row and the tile slot. The query token's position
within its tile comes from the token of segment wl. The key token's position comes from the
sumcheck's point again. -/
def pointM (S : Shape) (d : Divide) : Array E :=
  d.vpm.r.extract 0 (S.cf.lgk + 2 * S.lnT - 1) ++ d.zilo S ++ lastCoords d.vpm.r S.cf.lB

/-- The point at which the value product on the diagonal reads `as`. From its sumcheck's point
come the head g of keys and values and the tile. The query token's position within the tile comes
from the token of segment wl. The key token's position comes from the sumcheck's point again. -/
def pointD (S : Shape) (d : Divide) : Array E :=
  d.vpd.r.extract 0 (S.cf.lgk + S.lnT) ++ d.zilo S ++ lastCoords d.vpd.r S.cf.lB

/-- True if the point of every plane claim ends in the last n coordinates of zx. -/
def mergedPlanes (n : Nat) (zx : Array E) (planes : Array PlaneClaim) : Bool :=
  planes.all fun pc => lastCoords pc.z n == lastCoords zx n

/-- True if token and feature of segment wl's inner point are those of segment wh's, and are the
last coordinates of zx. -/
def mergedTokens (S : Shape) (zx : Array E) (d : Divide) : Bool :=
  let w := d.ziW ++ d.zcW
  w == d.ziH ++ d.zcH && w == lastCoords zx (S.cf.lt + S.cf.ldh)

/-! ## The list of tables

The tests.
 - Every table has exactly k (m / len) entries (add).
 - The last table ends where the planned array ends (placeAll). With the test before, the tables
   cover the array without a gap and without an overlap.
 - For a table on blocks of features there are exactly T token weights, 2^ls T is the block length
   2^la that add is given, and the point on the features has at least ls coordinates (lng).
 - One table on `as` serves every plane claim, and one table on ao serves two segments. For this the
   points concerned must end in the same coordinates. They do, because the lookup cuts them from
   one point and a tree of the lookup is deep enough: dT is at least lmS and at least lt + ldh
   (forest-depth-A in shapeHid, OnBytes/Model/AttentionShape.lean). The file compares them anyway
   (mergedPlanes, mergedTokens).
 - lmb is from 5 to kT + 5, as the weights on bA need it. bA has 2^lmb rows and holds the planes of
   the lookup's counts (forest-planes, by Forest.planeCols; shapeHid has tested it before).
-/

/-- Places a table on ah, which comes after the parts of `as` in the list. A block is the rows of
one feature, and psi gives the token weights. -/
def addRow (S : Shape) (mats : Array Model.TMat) (psi : Unit → Array E) : PlaceM Nat := do
  add mats S.cf.NAs S.T (← PlaceM.weights S.T psi) S.fillH

/-- Places a table of elems entries on blocks of features of matrix number mat, at the point zc on
the features within a head and under the token weights that ptk gives. -/
def addLong (S : Shape) (mats : Array Model.TMat) (mat : Nat) (zc : Array E)
    (ptk : Unit → Array E) (elems : Nat) : PlaceM Nat := do
  let phi ← lng S zc ptk
  add mats mat (2 ^ S.cf.la) phi elems

/-- Places all tables, in their order. mats is the smallness test's list of matrices: the parts of
`as`, then ah, ao, bA and qa. nW is the planned length of the array of tables. g is what the lookup
has stored. Refuses if one of the tests that the head of this section lists fails. -/
def placeAll (S : Shape) (mats : Array Model.TMat) (nW : Nat) (g : Model.Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    PlaceM Tables := do
  let cf := S.cf
  let gSo := S.fillO * S.T / 2 ^ cf.la
  let gSq := S.fillQ * S.T / 2 ^ cf.la
  let mb := 2 ^ cf.lmb
  let iAO := cf.NAs + 1
  let iBA := cf.NAs + 2
  let iQA := cf.NAs + 3
  let ptM := pointM S d
  let ptD := pointD S d
  let riE := d.scE.r.extract cf.lgk (cf.lgk + cf.lt)
  Model.testAs "internal-a-merged-point" (mergedPlanes cf.lmS g.zx planes)
  let tA ← addAs S mats fun _ => lastN g.zx cf.lmS
  let tVM ← addAs S mats fun _ => lastN ptM cf.lmS
  let tVD ← addAs S mats fun _ => lastN ptD cf.lmS
  let tM ← scores.mapM fun k => addRow S mats fun _ => tok S k.wI k.zi
  let hW ← addRow S mats fun _ => Model.eqTab d.ziW
  let hX ← addRow S mats fun _ => Model.eqTab d.ziX
  let hE ← addRow S mats fun _ => Model.eqTab riE
  let hT ← addRow S mats fun _ => Model.eqTab x.ti
  let hPi ← addRow S mats fun _ => Model.eqTab (x.pi S)
  let hR2 ← addRow S mats fun _ => Model.eqTab (x.ri2 S)
  Model.testAs "internal-a-merged-point" (mergedTokens S g.zx d)
  let tO ← addLong S mats iAO d.zcW (fun _ => Model.eqTab d.ziW) gSo
  let tQK ← scores.mapM fun k => do
    let rcK := lastCoords k.sc.r cf.ldh
    let tQ ← addLong S mats iQA rcK (fun _ => tok S (scoreTiles S k).1 k.zi) gSq
    let tK ← addLong S mats iQA rcK (fun _ => tok S (scoreTiles S k).2 k.zj) gSq
    pure (tQ, tK)
  let qO ← addLong S mats iQA d.zcW (fun _ => Model.eqTab riE) gSq
  let qVM ← addLong S mats iQA d.zcW (fun _ => tok S d.wJv (lastCoords d.vpm.r cf.lB)) gSq
  let qVD ← addLong S mats iQA d.zcW
    (fun _ => tok S (Model.eqTab (d.vpd.r.extract cf.lgk (cf.lgk + S.lnT)))
      (lastCoords d.vpd.r cf.lB)) gSq
  let qF ← addLong S mats iQA (x.rc S) (fun _ => Model.eqTab (x.ri S)) gSq
  let qKx ← addLong S mats iQA (x.rc S) (fun _ => Model.eqTab (x.pj S)) gSq
  -- phiB returns nothing exactly when planeCols refuses. That is tested here, on public numbers, so
  -- getD never takes its default.
  Model.mustAs "forest-planes" (Model.Forest.planeCols g.shape cf.lmb).toBool
  let phiB0 ← PlaceM.weights mb fun _ => (Model.Forest.phiB g cf.lmb 0).getD #[]
  let tBit0 ← add mats iBA mb phiB0 S.kbA
  let phiB1 ← PlaceM.weights mb fun _ => (Model.Forest.phiB g cf.lmb 1).getD #[]
  let tBit1 ← add mats iBA mb phiB1 S.kbA
  let tPin ← add mats iBA mb (← PlaceM.weights mb fun _ => Model.Forest.phiP cf.lmb) S.kbA
  let t ← PlaceM.placed
  Model.mustAs "internal-af-W-length" (t.next == nW)
  let score : Array ScoreTables := (tM.zip tQK).map fun y => ⟨y.1, y.2.1, y.2.2⟩
  pure {
    ptM := ptM, ptD := ptD, tA := tA, tVM := tVM, tVD := tVD, score := score,
    hW := hW, hX := hX, hE := hE, hT := hT, hPi := hPi, hR2 := hR2, tO := tO,
    qO := qO, qVM := qVM, qVD := qVD, qF := qF, qKx := qKx,
    tBit0 := tBit0, tBit1 := tBit1, tPin := tPin,
    tabLen := t.tabLen, funs := t.funs }

/-- The tables of part 3: places all tables from the array's entry 0 on. Returns each table's first
entry, the lengths, and the list for the smallness test. It is in the type Blk and closes no
round. -/
def tables (S : Shape) (mats : Array Model.TMat) (nW : Nat) (g : Model.Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    Blk Tables := do
  pure (← placeAll S mats nW g planes scores d x {}).1

/-- The names under which this file refuses. The C++ verifier puts the sub-proof's prefix before
internal-a-table-length and internal-a-merged-point. Here they have no prefix. -/
def tablesNames : List String :=
  ["internal-a-table-length", "plan-tensor-layout", "internal-a-merged-point", "forest-planes",
   "internal-af-W-length"]

end OnBytes.Attention
