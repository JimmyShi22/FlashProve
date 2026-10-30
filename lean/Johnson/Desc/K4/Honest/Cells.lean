-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Cells.lean: cells, reads, and the value of a form.

WHAT IT DOES NOT SHOW. Nothing here says that the entries made here are what a verifier's smallness
test asks of the reads, nor that a form's value is what the form is meant to stand for: there is no
law, and the tests of this file hold three small tools alone (corners; weights that are 0 at most
rows; wtsFit at two families). The rule of an entry is the format's
(docs/format/11-2-feed-forward-segment.md, "The parts of U3, and the two reads"); it is typed here
once more, so that it can be evaluated entry by entry. The library states the same rule as a
proposition, the law of the reads (FunRead, ReadsAll: OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean;
readOf, reads_meet: Johnson/Meaning/PlanesLaw.lean): NO THEOREM TIES THE FUNCTIONS OF THIS FILE TO
THAT LAW.

WHAT IT DEFINES. The way from the cells of a feed-forward segment to the entries of its reads, and
from these to the value of a linear form of the verifier. Definitions with code. No theorem.

The verifier's claims on a layers' sub-proof are linear forms (OnBytes.Model.Aff) in hidden scalars
and in entries of one committed vector, the reads (U3). The reads are cut into families of tables: a
family belongs to a matrix of cells and a named point, and its entry number col nb + bk, within a
part of the matrix, is the sum over r < L of phi[r] times the cell in row bk L + r and column col,
where phi are public weights made of the point, L is their number and nb the number of runs of L
rows. Which families there are and in which order is taken from the verifier's own functions
(tableAsks, layTables: OnBytes/Model/LayerForms.lean), and so are a family's weights at a point in
general (phiOf: OnBytes/Model/Layer.lean). TWO THINGS ARE TYPED ANEW HERE: the walk over a matrix's
parts (famPart, after layParts), and the weights where a point's token coordinates are a corner
(fewOf, after longPhi and eqTab; held against both by tests below, at small numbers).

  1  bitsOf, cornerOf, fewOf   a corner of the cube as a point; the corner's number of such a point;
                            the few rows that have a weight where a point's token coordinates
                            are a corner
  2  famCell                the cell that an entry of a family weighs by phi[r]
  3  Reads, wtsFit, readsAt   THE HONEST READS, ENTRY BY ENTRY, at any list of named points; does a
                            family have its weights there
     readsHeard             the same at the points that the challenges heard so far name
  4  valAff, affFits, valAff?   a form's value on the reads and on given values of the hidden
                            scalars; do all its entries have their weights
  5  readsOf                the reads as one array, of the verifier's finished list of tables
  6  featAt, limbAt, tensorAt, tensorOf, streamLimb   a tensor's limb at a token, straight from the
                            cells

Why points by name. With a family's point laid at the bits of a token's number t, the weights are 1
at t and 0 elsewhere, and an entry of a short table is one cell. So a form of the verifier, valued
on the reads at such a corner, is the form's meaning at token t; valued at the sampled point it is
what the claim speaks of. Where the token coordinates of a point are a corner, readsAt reads the
cells of that token alone: one for a short table; for a long one at most 2^ls, one for each feature
of the block (one alone if the block's coordinates are a corner too).

Limits. A FAMILY WHOSE POINT IS NOT IN THE LIST, OR HAS ANOTHER LENGTH THAN THE KIND OF TABLE ASKS,
READS 0 in Reads.u3; so does a family for which the verifier's function gives another number of
weights than L (two of the three tables on the lookup's planes, while the lookup's two points on the
planes are not laid), and so does an entry beyond the last family. NOT SO AT A CORNER: there the
verifier's function is not asked, and a family whose L is another number than its point gives
weights reads cells, not 0; Reads.has is false there too. By reading, no layout that the verifier's
own function makes has such a family (T = 2^lt, ls + lt = la). Such a 0 cannot be told from an
honest 0, so Reads.has says whether an entry's family has its L weights, and valAff? yields nothing
for a form that names an entry without. A test that is meant to hold a claim uses valAff?. Reads.has
IS A TEST ON NAMES, LENGTHS AND PUBLIC NUMBERS (wtsFit): it reads no coordinate of a point, at a
family with a named point; at the three families on the lookup's planes the verifier's own function
is asked. THAT THE WEIGHTS ARE THERE WHEREVER IT IS TRUE is by reading, and by a test below at two
families and small numbers: no law.
In valAff an entry of another array than the reads counts as 0. A form names an entry of the reads
by a virtual row and an index in it; valAff takes that for entry number row K3 + index, as the
verifier's U3at lays it. Item 6 types the placement of features by the format's rule ("Tensors and
cells"); no law here holds it against items 2 and 3. Cells are the program's words; a word that is
not below the field's prime is not looked for. FOUR PADDINGS HERE READ PUBLIC DATA ALONE: a matrix
of a number beyond the segment's list counts as one of 0 rows and 0 columns (famPart, famCell,
famsAt, readsOf); a kind of matrix beyond the layout's two lists has 0 columns and parts of 0 rows
(featAt); a name that the layout lacks gives a tensor without a limb (tensorOf); a weight that a
table lacks counts as 0 (readsOf, as the law of the reads has it: FunRead): so where the verifier's
function gives fewer weights than a table has rows, readsOf sums the rows that have one, where
Reads.u3 reads 0.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (Aff HFun Forest.Heard TenAt tenCell ofNat eqTab longPhi)
open OnBytes.Model.Layer (Lay Ten Env TableAsk matIx phiOf)

/-! ## 1 Corners -/

/-- The corner number x of the cube in n variables as a point, the coordinate of the highest bit
first. -/
def bitsOf (n x : Nat) : Array E :=
  (Array.range n).map fun k => if x.testBit (n - 1 - k) then oneE else zeroE

/-- The number of the corner at which a point lies, the first coordinate being the highest bit;
nothing if some coordinate is neither 0 nor 1. -/
def cornerOf (z : Array E) : Option Nat :=
  z.foldl
    (fun (s : Option Nat) c =>
      s.bind fun x =>
        if c == zeroE then some (2 * x) else if c == oneE then some (2 * x + 1) else none)
    (some 0)

/-- **The rows of a run that have a weight, where a point's token coordinates are a corner**: each
with its weight. lng: the table is long: the point has ls coordinates of a feature's low bits in
front of the lt of the token, and the row of (c2, t) is c2 2^lt + t (blockRows,
OnBytes/Model/Tensors.lean). Nothing if the token coordinates are no corner. -/
def fewOf (lng : Bool) (ls lt : Nat) (p : Array E) : Option (Array (Nat × E)) :=
  let lo := if lng then ls else 0
  (cornerOf (p.extract lo (lo + lt))).map fun t =>
    ((eqTab (p.extract 0 lo)).toList.zipIdx.filterMap fun x =>
      if x.1 == zeroE then none else some (x.2 * 2 ^ lt + t, x.1)).toArray

/-- Weights as an array of n members, of the rows that have one. -/
def spread (n : Nat) (rows : Array (Nat × E)) : Array E :=
  rows.foldl (fun a x => a.setIfInBounds x.1 x.2) (Array.replicate n zeroE)

#guard cornerOf (bitsOf 5 19) == some 19
#guard cornerOf (bitsOf 0 0) == some 0
#guard bitsOf 3 4 == #[oneE, zeroE, zeroE]
#guard cornerOf #[oneE, ofNat 2] == none
-- the few rows are the verifier's weights: a long table at half a corner and at a whole one; a
-- short table; and no answer where a token coordinate is no bit
#guard (fewOf true 2 3 (#[ofNat 5, ofNat 7] ++ bitsOf 3 6)).map (spread 32) ==
  some (longPhi (#[ofNat 5, ofNat 7] ++ bitsOf 3 6) 2 3)
#guard (fewOf true 2 3 (#[ofNat 5, ofNat 7] ++ bitsOf 3 6)).map (·.size) == some 4
#guard fewOf true 2 3 (bitsOf 5 22) == some #[(22, oneE)]
#guard (fewOf false 2 3 (bitsOf 3 6)).map (spread 8) == some (eqTab (bitsOf 3 6))
#guard fewOf true 2 3 (bitsOf 4 9 ++ #[ofNat 3]) == none

/-! ## 2 The cell behind an entry -/

/-- The part of a family that holds entry number i, and the entry's number inside that part. The
parts lie one after the other; a part's table has one entry for each column and each run of L rows
(layParts, OnBytes/Model/LayerForms.lean). The argument after L counts the parts still to pass. M:
the number of the matrix at hand. Beyond the last part: the matrix after it. -/
def famPart (mats : Array (Nat × Nat)) (L : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, M, i => (M, i)
  | n + 1, M, i =>
    let mk := mats.getD M (0, 0)
    let size := mk.2 * (mk.1 / L)
    if i < size then (M, i) else famPart mats L n (M + 1) (i - size)

/-- **The cell that entry number i of family a weighs by phi[r]**: the matrix's number in the
segment's list, the row, the column. mats: the rows and the columns of each matrix. -/
def famCell (mats : Array (Nat × Nat)) (a : TableAsk) (i r : Nat) : Nat × Nat × Nat :=
  let x := famPart mats a.L a.parts a.M0 i
  let nb := (mats.getD x.1 (0, 0)).1 / a.L
  (x.1, x.2 % nb * a.L + r, x.2 / nb)

/-! ## 3 The honest reads, entry by entry -/

/-- The weights of a family, as far as a list of points gives them. -/
inductive Wts where
  /-- the rows of a run that have a weight, each with it; every other row has the weight 0 -/
  | few (rows : Array (Nat × E))
  /-- the verifier's own weights, made when they are first asked for; nothing if the verifier's
  function gives none, or not as many as an entry has rows -/
  | whole (phi : Thunk (Option (Array E)))

/-- A family with its place in the reads and its weights. -/
structure Fam where
  ask : TableAsk
  first : Nat
  len : Nat
  wts : Wts
  /-- the family has its weights, as many as an entry has rows (`wtsFit`); asked when it is first
  read -/
  fit : Thunk Bool

/-- **The reads, as two functions of an entry's number**: the committed vector U3 of a layers'
sub-proof as an honest prover fills it, at some list of points. -/
structure Reads where
  /-- entry number e; 0 where the family's weights lack or no family holds e. NOT TO BE READ WHERE
  has e IS FALSE -/
  u3 : Nat → E
  /-- the entry lies in a family that has its weights, as many as an entry has rows (`wtsFit`) -/
  has : Nat → Bool

/-- The weights of family a at the points pt. The three families on the matrix of the lookup's
planes have no named point: the weights of two come from what the lookup has sampled, those of the
third are public constants. -/
def wtsOf (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E)) (a : TableAsk) : Wts :=
  let few : Option (Array (Nat × E)) :=
    if a.point.isEmpty then none
    else (pt.find? fun p => p.1 == a.point).bind fun p =>
      if p.2.size == (if a.lng then y.h.la else y.h.lt) then fewOf a.lng y.ls y.h.lt p.2 else none
  match few with
  | some rows => .few rows
  | none =>
    .whole (Thunk.mk fun _ =>
      (phiOf y fo pt a).bind fun phi => if phi.size == a.L then some phi else none)

/-- **Family a has its weights at the points pt, as many as an entry has rows: A TEST ON NAMES,
LENGTHS AND PUBLIC NUMBERS.** At a family with a named point it reads no coordinate of the point: so
it gives one answer whether or not the point's token coordinates are a corner, that is, on both
roads of `wtsOf`. A family with a named point: the point is in the list; it has the length that the
kind of table asks, la for a long table and lt for a short one; and weights made of a point of that
length are a.L in number: 2 ^ ls times 2 ^ lt, with ls + lt = la, for a long table; 2 ^ lt for a
short one. A POINT THAT IS NOT IN THE LIST ANSWERS FALSE: so does a point that is not yet whole,
which `namedPts` leaves out (Johnson/Desc/K4/Honest/Front.lean). The three families on the matrix of
the lookup's planes have no named point: there the verifier's own function is asked (`phiOf`). By
reading, whether that returns hangs on the lookup's public numbers, and how many weights it returns
on these and on the lengths of the lookup's two points on the planes. -/
def wtsFit (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E)) (a : TableAsk) : Bool :=
  if a.point.isEmpty then (phiOf y fo pt a).any fun phi => phi.size == a.L
  else
    (pt.find? fun p => p.1 == a.point).any fun p =>
      if a.lng then p.2.size == y.h.la && y.ls + y.h.lt == y.h.la && a.L == 2 ^ y.h.la
      else p.2.size == y.h.lt && a.L == 2 ^ y.h.lt

namespace CellsTest

/-- A layout of which the test reads three numbers: ls = 2, lt = 3, la = 5. -/
def lay : Lay := { h := { (default : Model.Layer.Shape) with la := 5, lt := 3 }, ls := 2 }

/-- A long family at the point Z. -/
def long : TableAsk := ⟨"af@Z", 0, 1, 32, "Z", true⟩
/-- A short family at the point zt. -/
def short : TableAsk := ⟨"ad@zt", 0, 1, 8, "zt", false⟩

/-- The weights are there, on whichever road `wtsOf` takes. -/
def there (pt : List (String × Array E)) (a : TableAsk) : Bool :=
  match wtsOf lay default pt a with
  | .few _ => true
  | .whole phi => phi.get.isSome

/-- The road is that of the few rows. -/
def few (pt : List (String × Array E)) (a : TableAsk) : Bool :=
  match wtsOf lay default pt a with
  | .few _ => true
  | .whole _ => false

/-- The first of four lists of points: each point of the right length, at a corner. -/
def atCorner : List (String × Array E) := [("Z", bitsOf 5 22), ("zt", bitsOf 3 6)]
/-- Each point of the right length, beside a corner: a token coordinate is no bit. -/
def beside : List (String × Array E) :=
  [("Z", bitsOf 4 9 ++ #[ofNat 3]), ("zt", #[ofNat 5, ofNat 7, ofNat 3])]
/-- At a corner, each point a coordinate short. -/
def cornerShort : List (String × Array E) := [("Z", bitsOf 4 9), ("zt", bitsOf 2 2)]
/-- Beside a corner, each point a coordinate short. -/
def besideShort : List (String × Array E) :=
  [("Z", bitsOf 3 6 ++ #[ofNat 3]), ("zt", #[ofNat 5, ofNat 7])]

-- the two lists take the two roads
#guard few atCorner long && few atCorner short && !few beside long && !few beside short
-- ONE ANSWER ON BOTH ROADS: true at a point of the right length, and the weights are there
#guard [atCorner, beside].all fun pt => [long, short].all fun a => wtsFit lay default pt a
#guard [atCorner, beside].all fun pt => [long, short].all fun a => there pt a
-- negative tests: a point a coordinate short, at a corner and beside one
#guard [cornerShort, besideShort].all fun pt => [long, short].all fun a => !wtsFit lay default pt a
-- negative tests: the point is not in the list; ls + lt is not la; another number of rows
#guard !wtsFit lay default [("zt", bitsOf 5 22)] long && !wtsFit lay default [] short
#guard !wtsFit { lay with ls := 1 } default atCorner long
#guard !wtsFit lay default atCorner { long with L := 16 }
#guard !wtsFit lay default atCorner { short with L := 16 }

end CellsTest

/-- The families of a place's reads, in their order, with their weights at the points pt. -/
def famsAt (Q : K4Pub) (fo : Forest.Heard) (pt : List (String × Array E)) : Option (Array Fam) :=
  (laidOf Q).map fun laid =>
    let mats := matsOf Q
    (laid.map fun x =>
      let len := x.2.foldl
        (fun s m => let mk := mats.getD m.1 (0, 0); s + mk.2 * (mk.1 / x.1.L)) 0
      ({ ask := x.1, first := (x.2.head?.map (·.2)).getD 0, len,
         wts := wtsOf Q.P.y fo pt x.1
         fit := Thunk.mk fun _ => wtsFit Q.P.y fo pt x.1 } : Fam)).toArray

/-- Entry number i of a family. -/
def famEntry (mats : Array (Nat × Nat)) (cell : Nat → Nat → Nat → F) (f : Fam) (i : Nat) : E :=
  let c := famCell mats f.ask i 0
  match f.wts with
  | .few rows => rows.foldl (fun s x => maddS s (cell c.1 (c.2.1 + x.1) c.2.2) x.2) zeroE
  | .whole phi =>
    match phi.get with
    | none => zeroE
    | some phi =>
      (List.range f.ask.L).foldl
        (fun s r => maddS s (cell c.1 (c.2.1 + r) c.2.2) (phi.getD r zeroE)) zeroE

/-- **The honest reads at a list of named points.** fo: what the lookup in front has sampled. The
families are laid once, when this function is called; a family's whole weights are made when an
entry of it is first asked for, and an entry is reckoned each time it is asked for.
None where the verifier's own laying of the tables returns none. -/
def readsAt (Q : K4Pub) (w : K4In) (fo : Forest.Heard) (pt : List (String × Array E)) :
    Option Reads :=
  (famsAt Q fo pt).map fun fams =>
    let mats := matsOf Q
    let find (e : Nat) : Option Fam := fams.find? fun f => f.first ≤ e && e < f.first + f.len
    { u3 := fun e =>
        match find e with
        | some f => famEntry mats w.cell f (e - f.first)
        | none => zeroE
      has := fun e =>
        match find e with
        | some f => f.fit.get
        | none => false }

/-! ## 4 A form's value -/

/-- **The value of a form**: the constant, each hidden scalar at slot j, each entry of the reads at
R.u3. An entry of another array counts as 0. -/
def valAff (v : Env) (R : Reads) (slot : Nat → E) (a : Aff) : E :=
  let s := a.slots.foldl (fun s x => maddE s x.2 (slot x.1)) a.const
  a.ents.foldl
    (fun s x => if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s) s

/-- **The honest reads, of the challenges heard**: `readsAt` at the points that K4's rounds name,
each found by its round's number (`ptsOf`, `namedPts`: Johnson/Desc/K4/Honest/Front.lean). heard:
all challenges heard so far in the first chain. By reading, behind K4's last round every point that
`namedPts` lists is whole; a family whose point is not yet whole reads 0, and `Reads.has` says so.
The two tables of bits on the lookup's own matrix take their weights from what `K4In.look` returns
(shape, zb0, zb1). NOT ALL POINTS ARE OF K4's ROUNDS: Z, zt and the front of Y are cut from the zx
that `K4In.look` returns, and are whole only if that is. -/
def readsHeard (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) : Option Reads :=
  let p := ptsOf Q w heard
  readsAt Q w p.fo (namedPts Q p)

/-- Every entry that a form names, whatever its coefficient, is an entry of the reads whose family
has its weights in R. -/
def affFits (v : Env) (R : Reads) (a : Aff) : Bool :=
  a.ents.all fun x => x.tree == v.iU3 && R.has (x.row * v.K3 + x.idx)

/-- The value of a form; nothing if it names an entry of another array than the reads, or an entry
of the reads whose family has no weights in R (`affFits`). -/
def valAff? (v : Env) (R : Reads) (slot : Nat → E) (a : Aff) : Option E :=
  if affFits v R a then some (valAff v R slot a) else none

/-! ## 5 The reads as one array -/

/-- **The reads as an array of n entries**, of the verifier's finished list of tables (funsOf,
OnBytes/Model/Layer.lean): entry f.start + col nb + bk is the sum over r of f.phi[r] times the cell
in row bk f.len + r and column col of matrix f.mat. It reckons every entry: its cost is the number
of all cells of a matrix for each table on it. -/
def readsOf (mats : Array (Nat × Nat)) (funs : Array HFun) (n : Nat)
    (cell : Nat → Nat → Nat → F) : Array E :=
  funs.foldl
    (fun u f =>
      let mk := mats.getD f.mat (0, 0)
      let nb := mk.1 / f.len
      (List.range (mk.2 * nb)).foldl
        (fun u e =>
          u.setIfInBounds (f.start + e)
            ((List.range f.len).foldl
              (fun s r => maddS s (cell f.mat (e % nb * f.len + r) (e / nb)) (f.phi.getD r zeroE))
              zeroE))
        u)
    (Array.replicate n zeroE)

/-! ## 6 Tensors, straight from the cells -/

/-- **Where a feature's cell for token t lies**: the matrix's number in the segment's list, the row,
the column. kind: 0 af, 1 ad, 2 ar, 3 qa (as Ten.mat counts), 4 the stream that leaves the group,
5 the stream that enters it. A matrix in parts of m rows and k columns holds fr = m / T features in
a column: feature ft is in part ft / (k fr), column ft / fr mod k, and its cell for token t in row
(ft mod fr) T + t. -/
def featAt (y : Lay) (kind ft t : Nat) : Nat × Nat × Nat :=
  let ix := matIx y
  let s : Nat × Nat × Nat :=
    if kind == 4 then (ix.iXO, y.kxb, y.mxb)
    else if kind == 5 then (ix.iXI, y.kxb, y.mxb)
    else
      (if kind == 0 then ix.iAF else if kind == 1 then ix.iAD else if kind == 2 then ix.iAR
        else ix.iQA, y.kcol.getD kind 0, y.mrow.getD kind 0)
  let fr := s.2.2 / y.T
  (s.1 + ft / (s.2.1 * fr), ft % fr * y.T + t, ft / fr % s.2.1)

/-- The cell of feature ft of a matrix for token t. -/
def featCell (y : Lay) (cell : Nat → Nat → Nat → F) (kind ft t : Nat) : F :=
  let c := featAt y kind ft t
  cell c.1 c.2.1 c.2.2

/-- Limb lb of tensor X at instance ix, feature j and token t. -/
def limbAt (y : Lay) (cell : Nat → Nat → Nat → F) (X : Ten) (lb ix j t : Nat) : F :=
  featCell y cell X.mat (tenCell X.place lb ix j) t

/-- Tensor X at instance ix, feature j and token t: the sum over its limbs of 256^lb times the
limb, in the field. -/
def tensorAt (y : Lay) (cell : Nat → Nat → Nat → F) (X : Ten) (ix j t : Nat) : E :=
  (List.range X.nl).foldl
    (fun s lb => maddS s (limbAt y cell X lb ix j t) (ofNat (256 ^ lb))) zeroE

/-- The tensor with a name; a tensor without a limb if the layout has none of that name. The names
are the layout's (tensorAsks, OnBytes/Model/LayerLayout.lean). -/
def tensorOf (y : Lay) (name : String) : Ten := (y.T_ name).getD default

/-- Limb lb of the residual stream number sg of the group (0 enters the group, 2 Lam leaves it; the
others are instances of the tensor xs) at feature j and token t. xs: that tensor
(tensorOf y "xs"): an argument, so that a loop over many cells looks it up once. -/
def streamLimb (y : Lay) (cell : Nat → Nat → Nat → F) (xs : Ten) (sg lb j t : Nat) : F :=
  if sg == 0 then featCell y cell 5 (tenCell y.xb lb 0 j) t
  else if sg == y.NW * y.Lam then featCell y cell 4 (tenCell y.xb lb 0 j) t
  else limbAt y cell xs lb (sg - 1) j t

end OnBytes.Desc.First.K4.Honest
