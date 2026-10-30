-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Tensor.lean: coefficient vectors in structured form.

The C++ counterparts are blocks/iop/tensor.h (Tensor, Form) and blocks/iop/foldeq.h (tensor_below,
VectorLay). Not taken over from tensor.h, among other things: what only a prover's engine uses (held
factors, engine terms, hints), and the frozen parts of a Form, which change no vector and serve
speed only. F is the base field and E its cubic extension (OnBytes/Field/Ext.lean).

A linear claim on a committed vector needs a vector of coefficients, which can have 2^30 entries. So
a verifier keeps a short description and changes it step by step. Outside the tests a Form is
written out only in Form.dot, for the last step of a proximity test (baseVerify in
OnBytes/Iop/Prox.lean), and a single Tensor only in addTermTo (OnBytes/Iop/Ground.lean).

Indices. An index j below 2^n has the bits j_0 (the lowest) to j_(n-1). Variable t belongs to
bit t. A table of 2^k rows of length l is the vector that has the entry (row b, place c) at the
index b + 2^k c. So the k lowest variables give the number of the row.

A tensor on n variables is the vector v[j] = scalar * prod_t (if bit t of j is 1 then hi t else
lo t). Three uses:
 - the equality vector at a point z: lo t = 1 - z t, hi t = z t;
 - a row of a code's generator matrix: lo t = 1, hi t = x^(2^t) for the row's point x, so x^j at j;
 - the choice of an aligned block of rows: (lo, hi) = (1, 0) or (0, 1) on the row variables above
   the block's own.
A tensor may have one more factor that is no product: a slice of a vector that is written out. Some
of the variables, the dense ones, give the index within the slice.

A form is a whole coefficient vector: a sum of tensors and of single entries.

Fixing the k low variables at g: entry p becomes the sum over b < 2^k of eq(b, g) v[b + 2^k p], with
eq(., g) the equality vector at g. That is what a fold does to a coefficient vector.

Main definitions: Tensor, Tensor.eq, Tensor.product, Tensor.insertChoice, Tensor.entry,
Tensor.foldedSlice, Tensor.fixLow, Tensor.addTo, Tensor.dotInF, tensorBelow, VectorLay, Form,
Form.addForm, Form.fixLowPlain, Form.fixLow, Form.fits, Form.writeOut, Form.dotPlain, Form.dot.

What this file does not do. Every function is total, and most reject nothing. An index beyond the
end of an array reads 0. If a point has more coordinates than a tensor has variables, the tensor
ignores the extra coordinates. A single entry of a form does not: Form.fixLow multiplies it by x or
1 - x for every coordinate x of the point (eqWeight). No function here compares the number of
coordinates with the number of variables. Code that receives a form from a caller should first test
it with Form.fits, which also tests every tensor with Tensor.ok. Three functions return none for
some inputs: tensorBelow for a cut that it cannot make, and fStep and Tensor.dotInF for a pair or a
tensor that does not have the form that they serve.

Plain and fast. Two functions are written twice. The plain ones, fixLowPlain and dotPlain, say what
the fast ones, Form.fixLow and Form.dot, mean. Outside the tests the other files run only the fast
ones. A reading of E is a map to a commutative ring that respects the program's arithmetic
(Model.Reading, OnBytes/Model/HideLaws.lean). Proved: under any reading the two of a pair give the
same sum. OnBytes/Iop/FixLaws.lean (Form.fixLow_val, Form.fixLowPlain_val), if every tensor is in
order (Tensor.ok) and has at least as many variables as are fixed; OnBytes/Iop/DotLaws.lean
(Form.dot_val, Form.dotPlain_val), if every tensor has the given number of variables. Not proved:
that the two return the same machine words. OnBytes/Iop/TestTensor.lean compares small examples.

No theorem is stated here. Laws on these functions: OnBytes/Iop/TensorLaws.lean (the entries under
scale, insertChoice, add, addEntry and addForm), OnBytes/Iop/SpreadLaws.lean (Tensor.addTo_val),
OnBytes/Iop/FixLaws.lean and OnBytes/Iop/DotLaws.lean.
-/
import OnBytes.Field.Mle
import Std.Data.HashMap

namespace OnBytes

/-! ## Tensors -/

/-- A vector of product form, perhaps with one factor that is written out. -/
structure Tensor where
  /-- a factor of every entry -/
  scalar : E := oneE
  /-- for each variable, the lowest first, the pair (lo, hi); lo and hi are the pair's halves -/
  pairs : List (E × E) := []
  /-- the dense variables: bit i of the index within the slice is bit number denseVars[i] of the
  vector's index. A dense variable has the pair (1, 1). -/
  denseVars : List Nat := []
  /-- the vector of which the written-out factor is a slice -/
  values : Array E := #[]
  /-- where the slice begins in values -/
  first : Nat := 0
  deriving Inhabited

/-- True if no number occurs twice in the list. -/
def distinctNats : List Nat → Bool
  | [] => true
  | a :: l => !l.contains a && distinctNats l

/-- choicePairs count value: count pairs, (0, 1) for a bit 1 of value and (1, 0) for a bit 0, the
lowest bit first. Such a variable picks a bit: the vector is 0 wherever the index has the other. -/
def choicePairs : Nat → Nat → List (E × E)
  | 0, _ => []
  | n + 1, value =>
    (if value % 2 == 1 then (zeroE, oneE) else (oneE, zeroE)) ::
      choicePairs n (value / 2)

/-- denseIndex ds i j: the index within a slice that belongs to the index j of the vector. ds is
what is left of the dense variables, and its first element gives bit number i of the result. -/
def denseIndex : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | d :: ds, i, j => (j / 2 ^ d % 2) * 2 ^ i + denseIndex ds (i + 1) j

/-- r times one half of each pair: hi if the matching bit of j is 1, else lo. Lowest bit first. -/
def pairsAt : List (E × E) → Nat → E → E
  | [], _, r => r
  | p :: ps, j, r => pairsAt ps (j / 2) (mulE r (if j % 2 == 1 then p.2 else p.1))

/-- fixPairs pairs g s: fixes one variable after the other at the coordinates of g, as long as both
lists last. Returns s times the factors lo + x (hi - lo), and the pairs that are left. -/
def fixPairs : List (E × E) → List E → E → E × List (E × E)
  | p :: ps, x :: xs, s =>
    fixPairs ps xs (mulE s (addE p.1 (mulE x (subE p.2 p.1))))
  | ps, _, s => (s, ps)

/-- Folds bit number i out of the index of a stretch of a vector at x. The stretch has size entries
and begins at entry start of a. Two entries u, w whose indices differ in that bit only (0 at u, 1
at w) become u + (w - u) x. The lower bits keep their places, the higher bits move down by one. -/
def foldBit (a : Array E) (start size i : Nat) (x : E) : Array E :=
  let half := 2 ^ i
  Nat.fold (size / 2)
    (fun idx _ (out : Array E) =>
      let at0 := start + idx % half + 2 * half * (idx / half)
      out.push (foldPairE (a.getD at0 zeroE) (a.getD (at0 + half) zeroE) x))
    (Array.mkEmpty (size / 2))

/-- s p, without a product where p is 1. -/
@[inline] def timesOne (s p : E) : E := if p == oneE then s else mulE s p

namespace Tensor

/-- The number of variables. -/
def vars (v : Tensor) : Nat := v.pairs.length

/-- The equality vector at the point z, times scalar. -/
def eq (z : List E) (scalar : E := oneE) : Tensor :=
  { scalar := scalar, pairs := z.map fun x => (subE oneE x, x) }

/-- The vector whose entry j is scalar times the product of f[t] over the bits t that are set
in j. -/
def product (f : List F) (scalar : E := oneE) : Tensor :=
  { scalar := scalar, pairs := f.map fun x => (oneE, ofF x) }

/-- One more variable, above the others, with the pair (l, h). -/
def push (v : Tensor) (l h : E) : Tensor := { v with pairs := v.pairs ++ [(l, h)] }

/-- Appends count dense variables. They become the next higher bits of the slice's index. -/
def pushDense (v : Tensor) (count : Nat) : Tensor :=
  { v with
    pairs := v.pairs ++ List.replicate count (oneE, oneE)
    denseVars := v.denseVars ++ (List.range count).map (· + v.vars) }

/-- Names the vector of which the written-out factor is the slice that begins at first. Tests
nothing: Tensor.ok makes the tests of dense_check (tensor.h), which set_values calls there. -/
def setValues (v : Tensor) (values : Array E) (first : Nat) : Tensor :=
  { v with values := values, first := first }

/-- Replaces the pair of variable t by (l, h). Nothing changes if there is no variable t. -/
def setPair (v : Tensor) (t : Nat) (l h : E) : Tensor := { v with pairs := v.pairs.set t (l, h) }

/-- Moves the first count variables after the others, so that variable number count becomes
variable 0. The dense variables are not renumbered: the caller must do that. -/
def rotate (v : Tensor) (count : Nat) : Tensor :=
  { v with pairs := v.pairs.drop count ++ v.pairs.take count }

/-- The conditions on a tensor: it has at most 63 variables (the bound of tensor.h, which keeps an
index and the picked bits in 64-bit words); the slice is inside its vector; each dense variable
exists, has the pair (1, 1) and is named once. -/
def ok (v : Tensor) : Bool :=
  decide (v.vars ≤ 63) &&
  (v.denseVars.isEmpty || decide (v.first + 2 ^ v.denseVars.length ≤ v.values.size)) &&
  (v.denseVars.all fun d => v.pairs[d]? == some (oneE, oneE)) &&
  distinctNats v.denseVars

/-- Every entry times x. -/
def scale (v : Tensor) (x : E) : Tensor := { v with scalar := mulE v.scalar x }

/-- Inserts, before variable pos, count variables that pick the low count bits of value. -/
def insertChoice (v : Tensor) (pos count value : Nat) : Tensor :=
  { v with
    pairs := v.pairs.take pos ++ choicePairs count value ++ v.pairs.drop pos
    denseVars := v.denseVars.map fun d => if pos ≤ d then d + count else d }

/-- The entry at index j. Bits of j above the variables are not looked at. -/
def entry (v : Tensor) (j : Nat) : E :=
  let r := pairsAt v.pairs j v.scalar
  if v.denseVars.isEmpty then r
  else mulE r (v.values.getD (v.first + denseIndex v.denseVars 0 j) zeroE)

/-- The slice after every dense variable d below the length of g is fixed at g[d]. The highest bit
of the slice's index is folded first, so that the lower bits keep their places. -/
def foldedSlice (v : Tensor) (g : List E) : Array E :=
  let n := v.denseVars.length
  -- the loop's state: the vector that holds the slice, where the slice begins in it, and its size
  let s := (List.range n).reverse.foldl
    (fun (s : Array E × Nat × Nat) i =>
      match v.denseVars[i]? with
      | some d =>
        if d < g.length then (foldBit s.1 s.2.1 s.2.2 i (g.getD d zeroE), 0, s.2.2 / 2) else s
      | none => s)
    (v.values, v.first, 2 ^ n)
  if s.2.1 == 0 && s.1.size == s.2.2 then s.1 else s.1.extract s.2.1 (s.2.1 + s.2.2)

/-- True if one of the lowest count variables is dense, so that fixing them folds the slice. -/
def sliceIsCut (v : Tensor) (count : Nat) : Bool := v.denseVars.any (· < count)

/-- Fixes the lowest variables at the coordinates of g, for a tensor whose slice is cut. slice is
the folded slice (foldedSlice). -/
def fixLowWith (v : Tensor) (g : List E) (slice : Array E) : Tensor :=
  let sp := fixPairs v.pairs g v.scalar
  let dv := (v.denseVars.filter (g.length ≤ ·)).map (· - g.length)
  if dv.isEmpty then { scalar := mulE sp.1 (slice.getD 0 zeroE), pairs := sp.2 }
  else { scalar := sp.1, pairs := sp.2, denseVars := dv, values := slice, first := 0 }

/-- Fixes the lowest variables at the coordinates of g, as many as g has. Dense variables among
them are folded out of the slice. -/
def fixLow (v : Tensor) (g : List E) : Tensor :=
  if v.sliceIsCut g.length then v.fixLowWith g (v.foldedSlice g)
  else
    let sp := fixPairs v.pairs g v.scalar
    { v with scalar := sp.1, pairs := sp.2, denseVars := v.denseVars.map (· - g.length) }

/-- A short key for the table of folded slices: where the slice begins, its dense variables, and the
coordinates of four of its entries. Different slices can have one key; sameSlice decides. -/
def sliceKey (v : Tensor) : Nat × List Nat × List F :=
  let n := 2 ^ v.denseVars.length
  (v.first, v.denseVars, [0, n / 3, n / 2, n - 1].flatMap fun i =>
    let x := v.values.getD (v.first + i) zeroE
    [x.c0, x.c1, x.c2])

/-- True if the slices of v and w, which begin at the same place and have the same dense variables,
hold the same entries. -/
def sameSlice (v w : Tensor) : Bool :=
  Nat.all (2 ^ v.denseVars.length) fun i _ =>
    v.values.getD (v.first + i) zeroE == w.values.getD (v.first + i) zeroE

/-- The multilinear extension at a point x that has one coordinate for each variable:
the sum over j of eq(j, x) v[j]. -/
def mle (v : Tensor) (x : List E) : E := (v.fixLow x).scalar

/-- Adds to out, at the indices off, .., off + w - 1, s times the products of the pairs' halves,
times the written-out factor of v if it has one. The pairs come from the highest variable down, and
w is 2 to their number. A half whose factor is 0 is not visited, so a variable that picks a bit
costs nothing. An index beyond the end of out is passed over. -/
def spreadTo (v : Tensor) : List (E × E) → Nat → Nat → E → Array E → Array E
  | [], _, off, s, out =>
    out.modify off fun y =>
      addE y (if v.denseVars.isEmpty then s
        else mulE s (v.values.getD (v.first + denseIndex v.denseVars 0 off) zeroE))
  | p :: ps, w, off, s, out =>
    let out1 := if isZeroE p.1 then out else spreadTo v ps (w / 2) off (timesOne s p.1) out
    if isZeroE p.2 then out1 else spreadTo v ps (w / 2) (off + w / 2) (timesOne s p.2) out1

/-- Adds all entries to out. An entry beyond the end of out is dropped. A tensor with the scalar 0
costs nothing. What the result reads as: OnBytes/Iop/SpreadLaws.lean, Tensor.addTo_val. -/
def addTo (v : Tensor) (out : Array E) : Array E :=
  if isZeroE v.scalar then out else spreadTo v v.pairs.reverse (2 ^ v.vars) 0 v.scalar out

/-- The factor on the count variables from variable start on, written out: 2^count products of
their pairs, without the scalar and without the written-out factor. -/
def part (v : Tensor) (start count : Nat) : Array E :=
  ({ pairs := (v.pairs.drop start).take count } : Tensor).addTo
    (Array.replicate (2 ^ count) zeroE)

end Tensor

/-! ## The inner product with a written-out vector, for tensors over the base field -/

/-- A pair of elements of the base field, as dotSteps reads it. -/
inductive FStep where
  /-- the pair (1, 0) -/
  | low
  /-- the pair (0, h) -/
  | high (h : F)
  /-- the pair (1, h) -/
  | both (h : F)

/-- The pair as an FStep, if it has one of the three forms. -/
def fStep (p : E × E) : Option FStep :=
  if !(p.1.c1 == 0 && p.1.c2 == 0 && p.2.c1 == 0 && p.2.c2 == 0) then none
  else if p.1.c0 == 1 then some (if p.2.c0 == 0 then .low else .both p.2.c0)
  else if p.1.c0 == 0 then some (.high p.2.c0)
  else none

/-- Coordinate number c of an element of E; the last one for c above 1. -/
def coordE (c : Nat) (x : E) : F :=
  match c with
  | 0 => x.c0
  | 1 => x.c1
  | _ => x.c2

/-- The sum over j of (the product of the steps' halves that the bits of j pick) times coordinate c
of a[offset + j]. The first step belongs to the highest bit of j, which has the weight w. A factor h
multiplies the whole sum over its half of the indices once, not each term. Arithmetic is in F. -/
def dotSteps (a : Array E) (c : Nat) : List FStep → Nat → Nat → F
  | [], _, offset => coordE c (a.getD offset zeroE)
  | .low :: ps, w, offset => dotSteps a c ps (w / 2) offset
  | .high h :: ps, w, offset => mulF h (dotSteps a c ps (w / 2) (offset + w))
  | .both h :: ps, w, offset =>
    addF (dotSteps a c ps (w / 2) offset) (mulF h (dotSteps a c ps (w / 2) (offset + w)))

/-- The sum over j of v[j] a[j], for a tensor without a written-out factor whose pairs all have one
of the forms of FStep, as the rows of a generator matrix have. Returns none for any other tensor.
Entries that a lacks count as 0. -/
def Tensor.dotInF (v : Tensor) (a : Array E) : Option E :=
  if !v.denseVars.isEmpty then none
  else
    (v.pairs.mapM fStep).map fun steps =>
      let r := steps.reverse
      let w := 2 ^ (v.vars - 1)
      mulE v.scalar (E.mk3 (dotSteps a 0 r w 0) (dotSteps a 1 r w 0) (dotSteps a 2 r w 0))

/-! ## A tensor cut below a length -/

/-- denseNumber ds i start count d: the number that the bits of d give on the variables start, ..,
start + count - 1. ds is what is left of the dense variables, and its first element belongs to bit
number i of d, an index within the slice. Dense variables outside the range do not count. -/
def denseNumber : List Nat → Nat → Nat → Nat → Nat → Nat
  | [], _, _, _, _ => 0
  | x :: xs, i, start, count, d =>
    (if start ≤ x && x < start + count then (d / 2 ^ i % 2) * 2 ^ (x - start) else 0) +
      denseNumber xs (i + 1) start count d

/-- Tensors whose sum is v, but with 0 at every index whose bits start, .., start + count - 1 give a
number m that is not below len. m is below len exactly if len has a 1 at the highest bit where the
two differ. So there is one summand for each bit of len that is 1. If these variables are all dense
there is one summand in all: v with a copy of its slice in which those entries are 0.
Two short cuts come first: the result is [v] if m is below len at every entry of v that can be
nonzero, and [] if it is so at none.
Returns none if v lacks one of these variables, if len is above 2^count, or if no short cut applies
and only some of these variables are dense. -/
def tensorBelow (v : Tensor) (start count len : Nat) : Option (List Tensor) :=
  if v.vars < start + count || 2 ^ count < len then none
  else if len == 2 ^ count then some [v]
  else
    let written := fun t => v.denseVars.contains (start + t)
    let pair := fun t => v.pairs.getD (start + t) (zeroE, zeroE)
    -- the least and the greatest number that the index of a nonzero entry can give
    let least := (List.range count).foldl
      (fun s t => if !written t && isZeroE (pair t).1 then s + 2 ^ t else s) 0
    let most := (List.range count).foldl
      (fun s t => if written t || !isZeroE (pair t).2 then s + 2 ^ t else s) 0
    if most < len then some [v]
    else if len ≤ least then some []
    else
      let dense := (v.denseVars.filter fun d => start ≤ d && d < start + count).length
      if dense == 0 then
        some (((List.range count).filter fun q => len.testBit q).map fun q =>
          { v with
            pairs := v.pairs.mapIdx fun i p =>
              if i < start + q || start + count ≤ i then p
              else if i == start + q then (p.1, zeroE)
              else if len.testBit (i - start) then (zeroE, p.2)
              else (p.1, zeroE) })
      else if dense == count then
        some [{ v with
          values := Array.ofFn (n := 2 ^ v.denseVars.length) fun d =>
            if denseNumber v.denseVars 0 start count d.val < len then
              v.values.getD (v.first + d.val) zeroE
            else zeroE
          first := 0 }]
      else none

/-! ## How a vector lies in a table -/

/-- How a vector is laid out in the main table of an oracle message with 2^rowBits rows of
2^placeBits places. The rows are the real rows, which were sent, filled up to a power of two
(vectorLay in OnBytes/Iop/Foldeq.lean).
 - rowsHigh false: entry j of the vector is entry j of the table, so it is in row
   j mod 2^rowBits. Already the first entries use all rows, so the number of real rows must be a
   power of two. This file does not test that. If it is not, vectorRoom in Foldeq.lean returns 0.
 - rowsHigh true: a row holds 2^placeBits consecutive entries, so entry j is in row
   j div 2^placeBits. A vector of any length then takes only the rows that it needs.
In both ways the bits of j are the bits of the table's index, in the same or in another order. So a
tensor on the vector is again a tensor on the table (onTable). -/
structure VectorLay where
  /-- the table has 2^rowBits rows -/
  rowBits : Nat := 0
  /-- a row has 2^placeBits places -/
  placeBits : Nat := 0
  /-- which of the two ways -/
  rowsHigh : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace VectorLay

/-- The number of the table's variables. -/
def bits (l : VectorLay) : Nat := l.rowBits + l.placeBits

/-- The index in the table of the vector's entry j. -/
def index (l : VectorLay) (j : Nat) : Nat :=
  if l.rowsHigh then j / 2 ^ l.placeBits + (j % 2 ^ l.placeBits) * 2 ^ l.rowBits else j

/-- The number of the vector's entry that is at an index of the table. -/
def entryAt (l : VectorLay) (index : Nat) : Nat :=
  if l.rowsHigh then index / 2 ^ l.rowBits + (index % 2 ^ l.rowBits) * 2 ^ l.placeBits else index

/-- Takes a tensor v on the low bits of a vector's index j, which counts as 0 wherever a higher bit
of j is 1, and returns the same vector as a tensor on the table's index. If v has more variables
than the table, on_table in foldeq.h ends the process. Here v keeps them all, and the caller must
compare the result's number of variables with the table's. -/
def onTable (l : VectorLay) (v : Tensor) : Tensor :=
  let w := v.insertChoice v.vars (l.bits - v.vars) 0
  if l.rowsHigh then
    { w.rotate l.placeBits with
      denseVars := w.denseVars.map fun d =>
        if l.placeBits ≤ d then d - l.placeBits else d + l.rowBits }
  else w

end VectorLay

/-! ## Forms -/

/-- A coefficient vector: the sum of the tensors, which all have the same number of variables,
and of the single entries (index, coefficient). An index may come more than once. The order of
the parts has no meaning. -/
structure Form where
  /-- the tensors -/
  tensors : List Tensor := []
  /-- the single entries: index and coefficient -/
  entries : List (Nat × E) := []
  deriving Inhabited

/-- Adds up the entries that have the same index into one entry. In the result the indices
increase. -/
def mergeEntries (l : List (Nat × E)) : List (Nat × E) :=
  ((l.mergeSort fun a b => a.1 ≤ b.1).foldl
    (fun acc a =>
      match acc with
      | b :: r => if a.1 == b.1 then (b.1, addE b.2 a.2) :: r else a :: acc
      | [] => [a])
    []).reverse

namespace Form

/-- True if the form has no part. -/
def isEmpty (f : Form) : Bool := f.tensors.isEmpty && f.entries.isEmpty

/-- The form that is one tensor. -/
def ofTensor (v : Tensor) : Form := { tensors := [v] }

/-- f + v. -/
def add (f : Form) (v : Tensor) : Form := { f with tensors := v :: f.tensors }

/-- f + c at the index. -/
def addEntry (f : Form) (index : Nat) (c : E) : Form :=
  { f with entries := (index, c) :: f.entries }

/-- x f. -/
def scale (f : Form) (x : E) : Form where
  tensors := f.tensors.map (·.scale x)
  entries := f.entries.map fun e => (e.1, mulE e.2 x)

/-- f + other. -/
def plus (f other : Form) : Form where
  tensors := other.tensors ++ f.tensors
  entries := other.entries ++ f.entries

/-- f + x other. -/
def addForm (f other : Form) (x : E) : Form := f.plus (other.scale x)

/-- The entry at index j. -/
def entry (f : Form) (j : Nat) : E :=
  let a := f.tensors.foldl (fun r v => addE r (v.entry j)) zeroE
  f.entries.foldl (fun r e => if e.1 == j then addE r e.2 else r) a

/-- Whether every part fits a vector of 2^vars entries, and every tensor is in order. -/
def fits (f : Form) (vars : Nat) : Bool :=
  (f.tensors.all fun v => v.vars == vars && v.ok) && f.entries.all fun e => decide (e.1 < 2 ^ vars)

/-- Fixes the lowest variables at the coordinates of g, as many as g has, and multiplies
everything by times. A single entry moves to the index that its higher bits give, with the weight
that g gives to its low bits. Each tensor is fixed by itself. This is the meaning of fixLow. -/
def fixLowPlain (f : Form) (g : List E) (times : E := oneE) : Form where
  tensors := f.tensors.map fun v => (v.scale times).fixLow g
  entries := mergeEntries (f.entries.map fun e =>
    (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times))

/-- The slices that one call of fixLow has folded so far: under a slice's key, the first tensor
with that key and its folded slice. -/
abbrev FoldedSlices : Type := Std.HashMap (Nat × List Nat × List F) (Tensor × Array E)

/-- One step of Form.fixLow, on the tensor v. s: the tensors done, the last first, and the slices
folded so far. A slice that is among those is not folded again but shared. That is right
because a folded slice depends only on the slice's entries, on its dense variables and on g, and not
on the tensor's scalar and pairs. Two slices count as the same if they begin at the same place, have
the same dense variables and hold the same entries. The table takes a key only once: a slice whose
key is taken by another slice is folded by itself and shared with nobody. -/
def fixLowShared (g : List E) (s : List Tensor × FoldedSlices) (v : Tensor) :
    List Tensor × FoldedSlices :=
  if v.sliceIsCut g.length then
    match s.2[v.sliceKey]? with
    | some c => (v.fixLowWith g (if v.sameSlice c.1 then c.2 else v.foldedSlice g) :: s.1, s.2)
    | none =>
      let slice := v.foldedSlice g
      (v.fixLowWith g slice :: s.1, s.2.insertIfNew v.sliceKey (v, slice))
  else (v.fixLow g :: s.1, s.2)

/-- fixLowPlain with less work and memory: a written-out slice that several tensors hold is folded
once, but for the case of equal keys that fixLowShared names. If all tensors of f are in order and
have at least as many variables as g has coordinates, both read as the same sum under any reading
of E (OnBytes/Iop/FixLaws.lean, Form.fixLow_val). -/
def fixLow (f : Form) (g : List E) (times : E := oneE) : Form where
  tensors := (f.tensors.foldl (fun s v => fixLowShared g s (v.scale times)) ([], {})).1.reverse
  entries := mergeEntries (f.entries.map fun e =>
    (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times))

/-- The multilinear extension at a point x that has one coordinate for each variable. -/
def mle (f : Form) (x : List E) : E := (f.fixLow x).entry 0

/-- Inserts, before variable pos, count variables that pick the low count bits of value. -/
def insertChoice (f : Form) (pos count value : Nat) : Form where
  tensors := f.tensors.map (·.insertChoice pos count value)
  entries := f.entries.map fun e =>
    (e.1 % 2 ^ pos + (value % 2 ^ count) * 2 ^ pos + (e.1 / 2 ^ pos) * 2 ^ (pos + count), e.2)

/-- Adds all entries to out. An entry beyond the end of out is dropped. -/
def addTo (f : Form) (out : Array E) : Array E :=
  f.entries.foldl (fun o e => o.modify e.1 fun y => addE y e.2)
    (f.tensors.foldl (fun o v => v.addTo o) out)

/-- The vector written out: 2^vars entries. -/
def writeOut (f : Form) (vars : Nat) : Array E := f.addTo (Array.replicate (2 ^ vars) zeroE)

/-- The sum over j of f[j] a[j], for a form on vars variables: the form is written out and
multiplied entry by entry. Entries that a lacks count as 0. This is the meaning of dot. -/
def dotPlain (f : Form) (vars : Nat) (a : Array E) : E :=
  let w := f.writeOut vars
  Nat.fold (min w.size a.size)
    (fun j _ r => maddE r (w.getD j zeroE) (a.getD j zeroE)) zeroE

/-- A faster dotPlain. If all tensors of f have vars variables, both read as the same sum under any
reading of E in a commutative ring (OnBytes/Iop/DotLaws.lean, Form.dot_val). A tensor with the
scalar 0 is passed over. A tensor that Tensor.dotInF serves is not written out, if it has vars
variables and a has at most 2^vars entries. The other parts are handed to dotPlain. -/
def dot (f : Form) (vars : Nat) (a : Array E) : E :=
  let s := f.tensors.foldl
    (fun (s : E × List Tensor) v =>
      if isZeroE v.scalar then s
      else if a.size ≤ 2 ^ vars && v.vars == vars then
        match v.dotInF a with
        | some d => (addE s.1 d, s.2)
        | none => (s.1, v :: s.2)
      else (s.1, v :: s.2))
    (zeroE, [])
  addE s.1 (dotPlain { tensors := s.2, entries := f.entries } vars a)

end Form

end OnBytes
