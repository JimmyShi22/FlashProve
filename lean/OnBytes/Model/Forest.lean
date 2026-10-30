-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Forest.lean: the public numbers of a lookup on hidden values.

A sub-proof of the model argues for many statements of the kind "every key of this vector is a row
of that table". Each such statement is a call (Call, OnBytes/Model/Frame.lean). All calls of one
sub-proof are handled by one lookup argument. Its verifier is vf_lookup_argument.h in the C++
programs. This file holds the part of it that reads no proof. Piece, CallZ, padRun and placeZ follow
verifier/src/vf_lookup_helpers.h; only the smallness test uses them (OnBytes/Model/Tail.lean).

How the calls are combined. In an index written (x | y) the bits of x are the high bits. A point has
one coordinate for each bit of an index, and coordinate 0 belongs to the top bit.
 - Keys. Call c has 2^n_c keys. All key vectors are cut into trees of one size, 2^dT keys. The trees
   are numbered y = 0 to NT - 1, the largest call first. A key has the index (x | y): x, of dT
   bits, is its place in the tree, and y, of rK bits, is the tree. Numbers from NT up to 2^rK - 1
   are trees that hold only padding.
 - Table. Row (t | c): t, of kT bits, is a row of the table of call c, and c, of cK bits, is the
   number of the call in the list. A shorter table is repeated. Call c's keys and rows are moved by
   its shift, c times a drawn element (Forest.pad in OnBytes/Model/Look.lean). The numbers from NC
   on hold the last call's table once more, with the last call's shift; nothing is counted there.
 - Padding. Some places of a key vector hold no key of the statement. They hold one fixed row of
   their call's table, row t0. A tree that holds only padding belongs to no call; it holds call 0's
   padding row, moved by call 0's shift, which is 0. How many such places tree y has, for y below
   NT, is the public number pub[y].

Main definitions: Forest.names, Forest.Shape, Forest.shape, Forest.pubRun, Forest.pubAsk,
Forest.elems, Forest.lins, Forest.planeCols, Forest.orderForestRange, Piece, CallZ, placeZ.

What this file does not claim. It holds no theorem. That the numbers are those of the C++ source is
tested on examples in OnBytes/Model/TestForest.lean. Differences: see Forest.names and Shape.
-/
import OnBytes.Field.Word
import OnBytes.Model.Frame
import OnBytes.Model.Rounds

namespace OnBytes.Model

/-- The numbers 0 to count - 1 in descending order of key. Numbers with equal keys keep their
order. -/
def byFallingKey (count : Nat) (key : Nat → Nat) : List Nat :=
  let all := List.range count
  let top := all.foldl (fun m i => max m (key i)) 0
  (List.range (top + 1)).reverse.flatMap fun k => all.filter fun i => key i == k

namespace Forest

/-- The names of all refusals of this file. A function of this file that can refuse returns the name
under which the C++ verifier refuses, by a reading of the C++ source (tested on examples; no
theorem), with two differences. Where the C++ name ends in the name of a call, which comes from a
file, the name here ends before it. Where the C++ name begins with a sub-proof's prefix, as
internal-forest-pub does when forestPad calls forestPubAsk, the name here begins after it. In
this file all numbers are natural numbers. Its tests are made in the order of the C++ source. -/
def names : List String :=
  ["shape-pt-words", "forest-row-value", "hid-call-floor", "hid-planes", "forest-calls",
    "forest-depth", "forest-trees", "forest-keys", "no-wrap-pin-forest", "internal-forest-place",
    "internal-forest-pub", "pt-pub-forest", "forest-only-padding", "forest-planes"]

/-- The numbers of a group of calls. They follow from the calls and the cap on a tree's depth. One
member of the C++ record has no counterpart: b(y), which says which of its call's trees tree y is.
The C++ verifier does not call it. -/
structure Shape where
  /-- the calls in the order of the sub-proof's list -/
  calls : Array Call := #[]
  /-- a tree has 2^dT keys -/
  dT : Nat := 0
  /-- the largest table has 2^kT rows -/
  kT : Nat := 0
  /-- the number of trees that belong to a call -/
  NT : Nat := 0
  /-- the number of bits of a tree's number -/
  rK : Nat := 0
  /-- the number of calls -/
  NC : Nat := 0
  /-- the number of bits of a call's number -/
  cK : Nat := 0
  /-- call c has 2^iota[c] trees -/
  iota : Array Nat := #[]
  /-- the number of the first tree of call c -/
  first : Array Nat := #[]
  /-- the call to which tree y belongs, for y below NT -/
  callOf : Array Nat := #[]
  /-- the number of padding keys of tree y, for y below NT; the sub-proof fills it in -/
  pub : Array Nat := #[]
  deriving Inhabited

/-- The number of bits of a key's index. -/
def Shape.v (h : Shape) : Nat := h.dT + h.rK

/-- The number of bits of a table row's index. -/
def Shape.d (h : Shape) : Nat := h.kT + h.cK

/-- The number of keys in the trees that hold only padding. -/
def Shape.emptyKeys (h : Shape) : Nat := (2 ^ h.rK - h.NT) * 2 ^ h.dT

/-- The number of all padding keys: those that pub counts, and those in the trees that hold only
padding. -/
def Shape.padding (h : Shape) : Nat := h.pub.foldl (· + ·) h.emptyKeys

/-- The order in which the sumcheck of the last key level takes its mu = v - 1 variables. Variable
number i stands for bit i of the index. The bits above the low rK bits come first: the lowest nine
of them in three groups of three, each group from its top bit down, then the others from the top
down. The low rK bits, which number the tree, come last, from the top down. The list has mu members
if and only if mu - rK is at least 9. This is not tested here; Forest.shape tests it as dT at least
10 (forest-depth). -/
def orderForestRange (mu rK : Nat) : List Nat :=
  [2, 1, 0, 5, 4, 3, 8, 7, 6].map (rK + ·) ++
    ((List.range (mu - (rK + 9))).map (rK + 9 + ·)).reverse ++ (List.range rK).reverse

/-- The tests on one call: 2^5 to 2^16 rows, a flag (Call.fn) of at most 2, a padding row inside the
table, at most 2^62 keys, a written table of full length with values below the prime, at least 2^10
keys, 32 planes, and no row with a count of its own. The values must be below the prime because not
every routine reduces a value that it is given: ofF, for one, stores it as it is. -/
def callAsk (c : Call) : Except String Unit := do
  if c.k < 5 || c.k > 16 || c.fn > 2 || c.t0 ≥ 2 ^ c.k || c.n > 62 ||
      (c.tau.any fun t => t.size != 2 ^ c.k) then
    throw "shape-pt-words"
  if (c.tau.getD #[]).any fun x => !okF x then throw "forest-row-value"
  if c.n < 10 then throw "hid-call-floor"
  if c.kappa != 5 || !c.heavy.isEmpty then throw "hid-planes"

/-- The numbers of a group of calls, and the tests on them. lid is the cap on a tree's depth. The
field pub is left empty. -/
def shape (calls : Array Call) (lid : Nat) : Except String Shape := do
  for c in calls do callAsk c
  let NC := calls.size
  if NC < 1 || NC > 16 then throw "forest-calls"
  let cK := clog2 NC
  let dT := calls.foldl (fun m c => min m c.n) lid
  let kT := calls.foldl (fun m c => max m c.k) 0
  if dT < 10 then throw "forest-depth"
  let iota := calls.map fun c => c.n - dT
  let NT := iota.foldl (fun s i => s + 2 ^ i) 0
  if NT > 256 then throw "forest-trees"
  let rK := clog2 NT
  -- A count of 32 bits has room for all keys, and the sum of all counts stays below the prime.
  if dT + rK ≥ 32 then throw "forest-keys"
  if 2 ^ (kT + cK + 32) ≥ pW.toNat then throw "no-wrap-pin-forest"
  let mut first := Array.replicate NC 0
  let mut callOf := Array.replicate NT 0
  let mut free := 0
  let order := byFallingKey NC fun c => iota.getD c 0
  for c in order do
    let trees := 2 ^ iota.getD c 0
    if free % trees != 0 then throw "internal-forest-place"
    first := first.setIfInBounds c free
    for b in List.range trees do
      callOf := callOf.setIfInBounds (free + b) c
    free := free + trees
  if free != NT then throw "internal-forest-place"
  pure { calls, dT, kT, NT, rK, NC, cK, iota, first, callOf }

/-- No padding key in any tree: the value from which pubRun starts counting. -/
def noPub (h : Shape) : Array Nat := Array.replicate h.NT 0

/-- The loop of pubRun. base is the number of the call's first tree. Each step takes the places up
to the end of one tree. The argument after base bounds the number of steps. -/
def pubLoop (dT base : Nat) : Nat → Array Nat → Nat → Nat → Array Nat
  | 0, pub, _, _ => pub
  | steps + 1, pub, first, count =>
    if count = 0 then pub
    else
      let b := first / 2 ^ dT
      let take := min count ((b + 1) * 2 ^ dT - first)
      pubLoop dT base steps (pub.modify (base + b) (· + take)) (first + take) (count - take)

/-- Adds the padding places first to first + count - 1 of call c to pub. Place i is in tree
i / 2^dT of its call. pub has NT entries. -/
def pubRun (h : Shape) (pub : Array Nat) (c first count : Nat) : Except String (Array Nat) := do
  if pub.size != h.NT || c ≥ h.iota.size then throw "internal-forest-pub"
  let i := h.iota.getD c 0
  let places := 2 ^ (h.dT + i)
  if first > places || count > places - first then throw "internal-forest-pub"
  pure (pubLoop h.dT (h.first.getD c 0) (2 ^ i + 1) pub first count)

/-- The conditions on the numbers of padding keys. A tree of 2^dT places cannot hold more than 2^dT
of them. A call must keep at least one place for a key that is not padding; otherwise the lookup
would say nothing about it. One tree of a call that has several may be all padding. The layer,
attention, the head and the smallness test each test this where they fill the numbers in
(LayerLayout.lean, AttentionShape.lean, HeadLayout.lean, Tail.lean). Forest.pad
(OnBytes/Model/Look.lean) tests it again on the numbers that it is given. -/
def pubAsk (h : Shape) (pub : Array Nat) : Except String Unit := do
  if pub.size != h.NT || h.calls.size != h.NC then throw "internal-forest-pub"
  if pub.any fun x => decide (x > 2 ^ h.dT) then throw "pt-pub-forest"
  for c in List.range h.NC do
    let i := h.iota.getD c 0
    let base := h.first.getD c 0
    let padded := (List.range (2 ^ i)).foldl (fun s b => s + pub.getD (base + b) 0) 0
    if padded ≥ 2 ^ (h.dT + i) then throw "forest-only-padding"

/-- The number of scalars that the prover sends in the lookup: the tie's, the key levels', the table
levels', those of the sumcheck over the leaves (degree 2 in a variable of the rows, 1 in one of the
planes, no value shown), and those of the sumcheck that the bits are bits. The docstring of
Forest.pad (OnBytes/Model/Look.lean) explains these parts. -/
def elems (h : Shape) : Nat :=
  sumcheckSlots .eq2 0 3 3 + 30 * sumcheckSlots .eq2 0 2 3 +
    (List.range h.v).foldl (fun s mu => s + layerSlots mu) 0 +
    (List.range h.d).foldl (fun s l => s + layerSlots (5 + l)) 0 +
    (1 + 2 * h.d + 5) + sumcheckSlots .eq2 (5 + h.d) 1 2

/-- The number of linear claims that the lookup leaves and that read only mask entries. Three more
read the planes of the counts, and one more reads the key vectors. -/
def lins (h : Shape) : Nat := 31 + h.v + h.d + 1

/-- The number of columns of the matrix of 2^lm rows that holds the planes of the counts. Refuses
unless lm is from 5 to kT + 5. -/
def planeCols (h : Shape) (lm : Nat) : Except String Nat :=
  if lm < 5 || lm > h.kT + 5 then throw "forest-planes" else pure (h.NC * 2 ^ (h.kT + 5 - lm))

end Forest

/-- A rectangle of cells of one array whose values are keys of a call, Rp rows by Cp columns. placeZ
gives it a range of 2^b key places that begins at off; the cell in row r and column c of the
rectangle is key number off + r CP + c. -/
structure Piece where
  /-- the array that holds the rectangle, by its number in the sub-proof's list -/
  tree : Nat := 0
  /-- the virtual row of that array through which the claims read the rectangle, by its number in
  the array's list of virtual rows -/
  row : Nat := 0
  /-- the first row of the rectangle -/
  r0 : Nat := 0
  /-- the number of rows of the rectangle -/
  Rp : Nat := 0
  /-- the first column of the rectangle -/
  c0 : Nat := 0
  /-- the number of columns of the rectangle -/
  Cp : Nat := 0
  /-- Cp rounded up to a power of two -/
  CP : Nat := 0
  /-- the first key of the piece -/
  off : Nat := 0
  /-- the least a with Rp at most 2^a -/
  a : Nat := 0
  /-- a plus the binary logarithm of CP -/
  b : Nat := 0
  deriving Inhabited

/-- A call with the pieces that its keys are read from. -/
structure CallZ where
  /-- the call -/
  call : Call
  /-- its pieces -/
  pieces : Array Piece := #[]
  deriving Inhabited

/-- Adds one to pub[i mod 2^iota] for each key i from first to first + count - 1. -/
def padRun (iota : Nat) (pub : Array Nat) (first count : Nat) : Array Nat :=
  let whole := count / 2 ^ iota
  (List.range (count % 2 ^ iota)).foldl
    (fun p j => p.modify ((first + whole * 2 ^ iota + j) % 2 ^ iota) (· + 1))
    (pub.map (· + whole))

/-- Places the pieces of a call one after the other, the largest first, and makes the call: a range
table of 2^k rows and at least 2^10 keys. lid is the cap on a tree's depth. Key places that belong
to no cell are padding: the columns from Cp up to CP - 1 of each piece, and all places after the
last piece. No place in the rows from Rp up to 2^a - 1 of a piece is counted as padding, so the
number of rows of every piece must be a power of two. This is not tested here.

The call's field pub counts the padding by a different rule from that of Forest.Shape.pub: key i
counts under i mod 2^iota. The C++ routine fills it in, and so does this one; no function of the
verifier reads it. -/
def placeZ (pieces : Array Piece) (name : String) (k lid : Nat) : CallZ :=
  let sized := pieces.map fun p =>
    let a := clog2 p.Rp
    let w := clog2 p.Cp
    { p with a := a, CP := 2 ^ w, b := a + w }
  let (placed, off) := (byFallingKey sized.size fun i => ((sized[i]?).map (·.b)).getD 0).foldl
    (fun (s : Array Piece × Nat) i =>
      (s.1.modify i (fun p => { p with off := s.2 }), s.2 + 2 ^ ((sized[i]?).map (·.b)).getD 0))
    (sized, 0)
  let n := max 10 (clog2 off)
  let iota := n - lid
  let inPieces := placed.foldl
    (fun pub p =>
      if p.Cp < p.CP then
        (List.range p.Rp).foldl
          (fun q r => padRun iota q (p.off + r * p.CP + p.Cp) (p.CP - p.Cp)) pub
      else pub)
    (Array.replicate (2 ^ iota) 0)
  let pub := if off < 2 ^ n then padRun iota inPieces off (2 ^ n - off) else inPieces
  { call := { name := name, n := n, iota := iota, k := k, kappa := 5, pub := pub },
    pieces := placed }

end OnBytes.Model
