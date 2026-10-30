-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/FormF.lean: how a matrix of the smallness test is packed into symbols.

The smallness test of a sub-proof speaks of integer matrices; the docstring of HTailF2 in
OnBytes/Model/Tail.lean says what the test is. A matrix with m rows of cells and k columns is not
committed cell by cell. Three cells of one column, from the rows 3 i, 3 i + 1 and 3 i + 2, are
packed into one field element, a symbol: cell 0 + B * cell 1 + B^2 * cell 2, with the radix
B = 2^20. The symbols of one matrix form an array of ceil(m / 3) rows and k columns.

This file holds
 - the constants of the packing, and three theorems: inequalities that tie them to the prime
   p = 2^64 - 2^32 + 1 and to beta = 2^lbz = 2^17 (lbz: OnBytes/Model/Frame.lean). beta bounds the
   random combinations in the smallness test. The bound that the test is meant to give for a single
   cell is 2 beta; no theorem in this file says that the test gives it;
 - the shape of a symbol array (ShP);
 - the record of the position of a matrix that one sub-proof commits to and another one reads
   (PlaceF), and the comparison of two such records (samePlaceF);
 - the two weight vectors of the tie, the equation that links a matrix's symbols to the random
   combinations of its cells (tieLeft, tieRight);
 - two loops over numbers (allFrom, allBelow);
 - the equality weight of one index as a plain product (eqPlainF), and equality weights at
   consecutive indices (EqRun). In the program only the self-tests of OnBytes/Model/Tail.lean use
   these two; they compute weights a second way.

The file follows verifier/src/vf_smallness_packing.h of the C++ verifier and keeps its names where
it can, with the constants in lower case. A docstring says where a definition
follows another C++ file, and which C++ fields, arguments and routines have no counterpart.
radixPower, allFrom, allBelow, EqRun.allLoop and EqRun.all have no routine of their own in the C++.

What this file does not claim. It states no theorem on the functions. The three theorems are
inequalities between constants.
-/
import OnBytes.Model.Frame

namespace OnBytes.Model

/-! ## Constants -/

/-- The binary logarithm of the radix B. -/
def lrad : Nat := 20

/-- The number of cell rows in one symbol: the rows 3 i, 3 i + 1, 3 i + 2 of one column. Three and
not four: four cells strictly between -2 beta and 2 beta can be chosen in (4 beta - 1)^4 ways, about
2^76, which is more than the field has elements, so two choices would share a symbol. -/
def lanes : Nat := 3

/-- The largest number of columns that a matrix of the smallness test may have. shapeF
(OnBytes/Model/Tail.lean) refuses a matrix with more columns, or with none, under hid-k-range. -/
def kcap : Nat := 8191

/-- The radix B by which the cells of a symbol are packed. -/
def radb : Nat := 2 ^ lrad

/-- B >= 4 beta - 1. Two cells that are below 2 beta in absolute value differ by at most
4 beta - 2, which is below the radix. -/
theorem radix_holds_a_cell : 4 * 2 ^ lbz - 1 ≤ radb := by decide

/-- (4 beta - 2) (1 + B + B^2) < p. Take two symbols, each packed from three cells that are below
2 beta in absolute value. As integers they differ by less than the prime, so the difference does not
wrap around in the field. This inequality and radix_holds_a_cell are why a symbol has at most one
reading as three such cells. That is proved, for these constants, in
OnBytes/Model/FormFLaws.lean. -/
theorem symbol_below_prime :
    (4 * 2 ^ lbz - 2) * (1 + radb + radb * radb) < pW.toNat := by decide

/-- (kcap + 1) * 2^21 <= beta^2. Only this inequality is proved. What it is for: let Z be a random
combination of the k cells of a row of an honest prover's matrix: the sum of the cells, each times
an entry of the drawn matrix. If the drawn bits are uniform, an entry is 0 with probability 1/2 and
1 or -1 with probability 1/4 each (drawMatrixF, OnBytes/Model/Tail.lean). The C++ source relies on
the tail bound P(|Z| >= beta) <= 2 exp(-beta^2 / (2^14 k)), as vf_smallness_packing.h states it for
cells that are signed bytes; it is not proved here. With k <= kcap + 1 the exponent is at least 2^7,
so an honest prover fails the bound beta with probability at most 2 exp(-2^7). This concerns
completeness, not soundness. -/
theorem columns_fit_bound : (kcap + 1) * 2 ^ 21 ≤ 2 ^ (2 * lbz) := by decide

/-! ## The shape of a symbol array -/

/-- The shape of the symbol array of one matrix. In every symbol array of a sub-proof one row of the
array holds one row of symbols (J = 1), and the array has no further row or column: cJ = 0, Rd = 0,
R = Rr = mS and K1 = Kc = k (ShP.of). A place is a column of the array; with J = 1 it is also the
matrix's column. The fields cJ, R, Rd, Rr, K1 and Kc are kept because the C++ record has them:
samePlaceF compares whole shapes, powersF refuses another J, Rd, R or Rr, and tieShapeHeld also
another K1 or Kc (both in OnBytes/Model/Tail.lean). Fields of the C++ record that stay 0 in the
programs (w, ln, n, t, mk, P2) have no counterpart. -/
structure ShP where
  /-- the matrix's rows of cells -/
  m : Nat := 0
  /-- the matrix's columns -/
  k : Nat := 0
  /-- the rows of symbols, ceil(m / 3) -/
  mS : Nat := 0
  /-- the rows of symbols that one row of the array holds -/
  J : Nat := 0
  /-- the binary logarithm of J -/
  cJ : Nat := 0
  /-- clog2 mS: the bits needed to number the rows of symbols -/
  aX : Nat := 0
  /-- 1 + the number of sub-proofs that read the array besides its owner -/
  a : Nat := 0
  /-- the array's rows that hold symbols -/
  R : Nat := 0
  /-- the array's rows that hold no symbol; they follow the others -/
  Rd : Nat := 0
  /-- all the array's rows: R + Rd, by the comment on ShP in verifier/src/vf_smallness_packing.h -/
  Rr : Nat := 0
  /-- the places of a row that hold symbols -/
  K1 : Nat := 0
  /-- the array's columns -/
  Kc : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The shape of the symbol array of a matrix with m rows of cells and k columns: one row of symbols
in each row of the array. ShP.of is the part of the C++ routine t2AddP (vf_subproof_segment.h)
that fills in a shape. -/
def ShP.of (m k a : Nat) : ShP :=
  let mS := (m + 2) / 3
  { m := m, k := k, mS := mS, J := 1, cJ := 0, aX := clog2 mS, a := a,
    R := mS, Rd := 0, Rr := mS, K1 := k, Kc := k }

/-! ## Where a shared matrix lies -/

/-- The position of a matrix that one sub-proof (its owner) commits to and another reads. Owner and
reader each fill in such a record from their own numbers. In the C++ record off starts at the
largest 64-bit number; here it starts at 0, which is also the value that is filled in
(HTailF2.declared, OnBytes/Model/Tail.lean). The field w of the C++ record PlaceF, which stays 0
in the programs, has no counterpart. -/
structure PlaceF where
  /-- the owner's number among the sub-proofs -/
  owner : Option Nat := none
  /-- the array's number among the owner's symbol arrays -/
  rootIndex : Option Nat := none
  /-- the shape of the symbol array -/
  sh : Option ShP := none
  /-- the matrix's first column in the array, its number of columns, its number of rows of cells -/
  matrix : Option (Nat × Nat × Nat) := none
  /-- the security level, in bits, for which the sub-proof's shapes are made: the level in the
  statement minus the bits of proof of work done before positions are drawn -/
  hb : Nat := 0
  /-- the rows of symbols -/
  mS : Nat := 0
  /-- the cell rows in a symbol -/
  lanes : Nat := 0
  /-- the rows of symbols for which the array has room -/
  padRows : Nat := 0
  /-- the rows of symbols in one row of the array -/
  J : Nat := 0
  /-- the array's columns -/
  K : Nat := 0
  /-- the first place of the matrix in a row -/
  off : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- True if the four optional fields are filled in and hb is not 0. The other fields are not looked
at. -/
def PlaceF.whole (p : PlaceF) : Bool :=
  p.owner.isSome && p.rootIndex.isSome && p.sh.isSome && p.matrix.isSome && p.hb != 0

/-- Compares the owner's record o with a reader's record r. Returns the label of the first part in
which they differ, and also "P3" if the owner's columns run past the owner's array. Returns the
empty string if all agree. It is meant for an owner's record that is whole (PlaceF.whole). The
labels are the C++ verifier's (samePlaceF), which appends them to its names
internal-g-owner-place-, internal-a-owner-place- and internal-h-owner-place-. What is compared is
where the matrix lies, not what lies inside it. Which feature holds an entry of a tensor, whether
owner and reader list the same tensors, and which row of a block holds a token are the matter of
tenCell and blockRow (OnBytes/Model/Tensors.lean) and of tensorsAgree
(OnBytes/Model/LayerLayout.lean). -/
def samePlaceF (o r : PlaceF) : String :=
  let past : Bool :=
    match o.matrix with
    | some (col0, k, _) => decide (o.K < col0 + k)
    | none => false
  if o.owner != r.owner then "P0"
  else if o.sh != r.sh then "P1"
  else if o.matrix.map (fun x => (x.1, x.2.1)) != r.matrix.map (fun x => (x.1, x.2.1)) || past then
    "P3"
  else if o.matrix.map (fun x => x.2.2) != r.matrix.map (fun x => x.2.2) then "P4"
  else if o.rootIndex != r.rootIndex then "P5"
  else if o.hb != r.hb then "P6"
  else if o.mS != r.mS || o.lanes != r.lanes || o.padRows != r.padRows || o.J != r.J ||
      o.K != r.K || o.off != r.off then "P9"
  else ""

/-! ## The tie -/

/-- B^l as an element of the base field, for l <= 3, where B^l is below the prime. It is called with
l < 3. For l > 3 the result would be wrong. -/
def radixPower (l : Nat) : F := UInt64.ofNat (radb ^ l)

/-- The left weights of the tie, one for each of the matrix's m rows of cells:
w[i] = rows[(i / 3) / J] * lo[(i / 3) % J] * B^(i % 3). rows: a weight for each of the array's Rr
rows. lo: a weight for each of the J rows of symbols in a row of the array. Returns none if a vector
has the wrong length (C++: internal-sym-point). tieLeft and tieRight are written for any J >= 1, as
in the C++. Nothing in the program calls them with J > 1; two guards of
OnBytes/Model/TestTreesConditions.lean evaluate them at J = 2. -/
def tieLeft (s : ShP) (rows lo : Array E) : Option (Array E) :=
  if rows.size != s.Rr || lo.size != s.J then none
  else
    some ((Array.range s.m).map fun i =>
      let iS := i / lanes
      let e := mulE (rows.getD (iS / s.J) zeroE) (lo.getD (iS % s.J) zeroE)
      scaleE (radixPower (i % lanes)) e)

/-- The right weights of the tie, one for each of the first J * k places of a row of the array:
w[c * J + x] = gam[c] * lo[x]. gam: a weight for each column of the matrix. Returns none if a
vector has the wrong length (C++: internal-sym-point). On J > 1 see tieLeft. The C++ placement
function placeP, with its record PlP, has no counterpart: the symbol in row iS of symbols and column
c of the matrix is in row iS / J of the array, at place c J + iS % J. The C++ tieRight calls placeP
(vf_smallness_packing.h); tieRight here writes the same order out as p / J and p % J. -/
def tieRight (s : ShP) (lo gam : Array E) : Option (Array E) :=
  if lo.size != s.J || gam.size != s.k then none
  else
    some ((Array.range (s.J * s.k)).map fun p =>
      mulE (gam.getD (p / s.J) zeroE) (lo.getD (p % s.J) zeroE))

/-! ## Loops over numbers -/

/-- True if p holds at i, i + 1, .., i + count - 1. It builds no list. -/
def allFrom (p : Nat → Bool) : (count i : Nat) → Bool
  | 0, _ => true
  | count + 1, i => p i && allFrom p count (i + 1)

/-- True if p holds at every number below n. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool := allFrom p n 0

/-! ## An equality weight as a plain product -/

/-- eq(z, idx): the product over the coordinates v of z[v] if the matching bit of idx is 1, and of
1 - z[v] if it is 0. Coordinate 0 belongs to the top bit of the |z| low bits of idx. -/
def eqPlainF (z : Array E) (idx : Nat) : E :=
  (List.range z.size).foldl
    (fun p v =>
      let x := z.getD v zeroE
      mulE p (if idx.testBit (z.size - 1 - v) then x else subE oneE x))
    oneE

/-! ## Equality weights at consecutive indices -/

/-- Equality weights eq(z, idx) at consecutive indices idx. pre[v] is the product of the factors of
the first v coordinates of z, so pre[|z|] is the weight. A step to the next index recomputes only
the products from the highest changed bit on: two products per step on average. C++:
UnscaledEqIterator (vf_smallness_packing.h) and EqRun (verifier/src/vf_subproof_segment.h). The
argument lead of EqRun, which no call in the C++ verifier sets, has no counterpart. -/
structure EqRun where
  /-- the point; coordinate 0 belongs to the top bit of the |z| low bits of an index -/
  z : Array E
  /-- the index -/
  idx : Nat
  /-- the products -/
  pre : Array E

namespace EqRun

/-- Recomputes pre[v + 1], .., pre[v + count] from pre[v]. -/
def fill (z : Array E) (idx : Nat) : (count v : Nat) → Array E → Array E
  | 0, _, pre => pre
  | count + 1, v, pre =>
    let x := z.getD v zeroE
    let factor := if idx.testBit (z.size - 1 - v) then x else subE oneE x
    fill z idx count (v + 1) (pre.set! (v + 1) (mulE (pre.getD v zeroE) factor))

/-- The run at the index idx. -/
def start (z : Array E) (idx : Nat) : EqRun :=
  { z := z, idx := idx, pre := fill z idx z.size 0 (Array.replicate (z.size + 1) oneE) }

/-- eq(z, idx). -/
def value (r : EqRun) : E := r.pre.getD r.z.size zeroE

/-- The run at the next index. -/
def next (r : EqRun) : EqRun :=
  let top := Nat.log2 (r.idx ^^^ (r.idx + 1))
  let v := if top ≥ r.z.size then 0 else r.z.size - 1 - top
  { r with idx := r.idx + 1, pre := fill r.z (r.idx + 1) (r.z.size - v) v r.pre }

/-- True if test i (eq(z, idx + i)) holds for i = done, .., done + count - 1, where r is at index
idx + done. -/
def allLoop (test : Nat → E → Bool) : (count done : Nat) → EqRun → Bool
  | 0, _, _ => true
  | count + 1, i, r => test i r.value && allLoop test count (i + 1) r.next

/-- True if test i (eq(z, first + i)) holds for every i below count. -/
def all (z : Array E) (first count : Nat) (test : Nat → E → Bool) : Bool :=
  allLoop test count 0 (start z first)

end EqRun

end OnBytes.Model
