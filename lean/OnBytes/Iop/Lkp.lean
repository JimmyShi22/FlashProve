-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Lkp.lean: the verifier's part in the lookup argument by product trees.
C++ counterpart: blocks/iop/lkp.h (lkp_verify, lkp_run and the routines that they call).

The claim. Every entry of a vector of keys occurs in a public table of 2^d rows. The keys are never
sent: they are a function of vectors that the prover has sent. The prover has also sent, bit by bit,
how often each row of the table is used: bit j of the count of row t is at the index j + 2^mu t of
the vector of multiplicities. The bits number j of all rows are called plane j.

The idea. For a random alpha the product of alpha - key over all keys equals a public factor times
the product of (alpha - row)^count over all rows. Both sides are computed by trees of products. The
key tree has the leaves alpha - key. The table's tree has the leaves 1 + bit (alpha - 1 - row) and
one root for each plane: the product of alpha - row over the rows whose bit in that plane is set. A
claim on one level of a tree is reduced to a claim on the next level towards the leaves by one
zero-knowledge sumcheck (OnBytes/Iop/Psc.lean) and one draw (line, in the same file). Nothing of the
trees is sent.

The steps are listed at Lkp.run, the padding at Lkp.Padding, what is handed on at Lkp.Out. What the
types do not enforce and the caller owes (these whole at Lkp.verify; more at Public.readFrom):
 - everything in Public is bound by the hash chain's first query, or follows from values that are;
 - planesAt reads the real planes only;
 - a row is made of every claim on the keys.

The block is written in Blk (OnBytes/Iop/Ground.lean). Lkp.roundsOf states its rounds once more, as
a function of the public inputs and of one number of bits of work. Only tests call it.
Main definitions: Lkp.Public, Lkp.Public.ok, Lkp.roundsOf, Lkp.Keys, Lkp.Out, Lkp.verify,
Lkp.liveBlocks, Lkp.onBlock, Lkp.weightsOfBlock.

Not claimed here: soundness or hiding.
-/
import OnBytes.Iop.Psc
import OnBytes.Iop.Tensor

namespace OnBytes

namespace Lkp

/-! ## The public inputs -/

/-- A run of places of padding: the keys number first + 2^logStep i, for i below length, of one part
hold one row of the table, as the shift has moved it, and are not counted.

Padding. Some places of the key vector may be declared as padding. Such a place holds a named row of
the table and is not counted. The public factor is the product of alpha - row over these places. The
padding is stated once, as places (Public.padding, and the key blocks without a function). The
number of places, the factor and what is taken out of the claims on the keys are all computed from
that one statement. Why a row of the table and no free value: the right side of the idea's equation
is then a product of factors alpha - (a row), whatever the number of places. So a false number of
places can make an honest proof fail, or force more keys to be that row, but lets in no key that is
in no row. This is argued, not proved. -/
structure Padding where
  /-- the number of the part -/
  part : Nat := 0
  /-- the first place -/
  first : Nat := 0
  /-- the places are 2^logStep apart -/
  logStep : Nat := 0
  /-- how many places -/
  length : Nat := 0
  /-- the number of the row that they hold -/
  row : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The keys of a part whose numbers agree in their low g bits (g: Public.g) form one tree, and
these bits are the tree's number y: it is the part of the key tree below entry y of level g. A block
of 2^logTrees tree numbers, from first on, belongs to one function, or its trees hold only padding.
Key number y + 2^g x has the index (y - first) + 2^logTrees x in the function's own key vector. -/
structure KeyBlock where
  /-- the first tree number: a multiple of 2^logTrees -/
  first : Nat := 0
  /-- the block has 2^logTrees tree numbers -/
  logTrees : Nat := 0
  /-- the function's number; none: the block's trees hold only padding -/
  function : Option Nat := none
  /-- if function is none: the number of the row that every place of the block's trees holds -/
  paddingRow : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- A function's table as a piece of the whole table (h: Public.h). If h = 0 it is the block of
2^logRows rows from first on. If h > 0 the low h bits of a row's number name the piece, first is
that number, and the function's table is repeated along the piece. -/
structure TablePart where
  /-- the first row, or the piece's number -/
  first : Nat := 0
  /-- the function's table has 2^logRows rows -/
  logRows : Nat := 0
  /-- the function's number -/
  function : Nat := 0
  /-- the rows written out; empty: the range table 0, 1, 2 and so on -/
  rows : List E := []
  deriving Inhabited

/-- Everything public about one lookup. -/
structure Public where
  /-- part i of the keys has 2^(parts[i]) keys -/
  parts : List Nat
  /-- the table has 2^d rows -/
  d : Nat
  /-- a count has 2^mu places for bits -/
  mu : Nat
  /-- how many of the 2^mu places for bits (the planes) are real; 0: all, and all is written in no
  other way. The others are public zeros: nothing is sent for them, and the root of each is the
  public value 1. -/
  live : Nat := 0
  /-- the low h bits of a row's number name its piece of the table; 0: the pieces are blocks of rows
  (TablePart) -/
  h : Nat := 0
  /-- the low g bits of a key's number are its tree's number (KeyBlock) -/
  g : Nat := 0
  /-- whether function number n has its keys and rows moved by n theta -/
  shifted : Bool := false
  /-- the numbers of all oracle messages from which keys and multiplicities are read. They must be
  fixed before theta and alpha are drawn. Tested here: the sample of each has been answered
  (verify), and the block's own rows read the main tables of these messages only (leave). Not tested
  here, the caller's duty: that the caller's rows on the keys read no other message, and that a
  message whose sample was answered in another chain has its root in this chain's first query. -/
  readFrom : List Nat
  /-- the blocks of tree numbers -/
  keys : List KeyBlock
  /-- the pieces of the table -/
  tables : List TablePart
  /-- the runs of padding inside the functions' trees -/
  padding : List Padding := []
  /-- the variables that the first rounds of each part's last key level bind, in that order; the
  others follow from the highest down -/
  lastKeyLevelOrder : List Nat := []
  deriving Inhabited

/-- The number of real planes of bits. -/
def Public.planes (S : Public) : Nat := if S.live == 0 then 2 ^ S.mu else S.live

/-- The number of all keys, padding counted. -/
def Public.allKeys (S : Public) : Nat := (S.parts.map fun x => 2 ^ x).sum

/-- The logarithm of the number of keys of the first part. -/
def Public.firstBits (S : Public) : Nat := S.parts.headD 0

/-- True if p holds for every two members of the list, the earlier one first. -/
def allPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (p a) && allPairs p l

/-- Two aligned blocks, given by first number and size in bits, have a number in common. -/
def meet (a aBits b bBits : Nat) : Bool := a / 2 ^ max aBits bBits == b / 2 ^ max aBits bBits

/-- The tree number of key number i lies in the block. -/
def KeyBlock.holds (b : KeyBlock) (g i : Nat) : Bool :=
  i % 2 ^ g / 2 ^ b.logTrees == b.first / 2 ^ b.logTrees

/-- The sum of the lengths of the runs that q picks. -/
def paddedBy (S : Public) (q : Padding → Bool) : Nat := ((S.padding.filter q).map (·.length)).sum

/-- The lookup, one of its parts, or one function's block of trees holds nothing but padding. Meant
for inputs that have passed keysOK and paddingOK: the runs then do not meet, so their lengths add up
to the number of places. Blocks of trees are looked at only if there is one part: sizesOK allows
tree numbers in no other case. Why Public.ok refuses such inputs: a place of padding is not read, so
what the block says about these keys would be empty, and a yes would say nothing of what was sent
there. Whether the right places are declared as padding no test of form can know: the caller derives
them. -/
def Public.onlyPadding (S : Public) : Bool :=
  S.keys.all (·.function.isNone) ||
  ((List.range S.parts.length).any fun i =>
    decide (2 ^ S.parts.getD i 0 ≤ paddedBy S fun p => p.part == i)) ||
  (S.parts.length == 1 && S.keys.any fun b =>
    b.function.isSome &&
    decide (2 ^ (S.firstBits - S.g + b.logTrees) ≤ paddedBy S fun p => b.holds S.g p.first))

/-- Two runs of padding have a place in common. -/
def Padding.meets (a b : Padding) : Bool :=
  let fine := if a.logStep ≤ b.logStep then a else b
  let coarse := if a.logStep ≤ b.logStep then b else a
  if fine.part != coarse.part ||
      fine.first % 2 ^ fine.logStep != coarse.first % 2 ^ fine.logStep then false
  else
    let low := fine.first
    let high := fine.first + (fine.length - 1) * 2 ^ fine.logStep
    let skip :=
      if low ≤ coarse.first then 0
      else (low - coarse.first + 2 ^ coarse.logStep - 1) / 2 ^ coarse.logStep
    decide (skip < coarse.length) && decide (coarse.first + skip * 2 ^ coarse.logStep ≤ high)

/-- The conditions on the sizes. Some message is read, and there is a part. There are 2, 4, .. or 64
places for planes, and at least 2 and fewer than 64 planes are real. Every part has at least 2 keys,
and all keys together are fewer than 2^planes, so that every count fits its bits. d + planes is
below 64: the sum of all counts is then below 2^63 and, read in the base field, cannot wrap around,
since the field's prime has 64 bits. So the row on the sum of the counts (step 7 at Lkp.run) speaks
of integers. Keys in several parts are served for one function and without tree numbers only. A
tree's number has no more bits than a key's. -/
def Public.sizesOK (S : Public) : Bool :=
  !S.readFrom.isEmpty && !S.parts.isEmpty &&
  decide (1 ≤ S.mu) && decide (S.mu ≤ 6) && decide (S.live < 2 ^ S.mu) &&
  decide (2 ≤ S.planes) && decide (S.planes < 64) &&
  (S.parts.all fun x => decide (1 ≤ x) && decide (x < S.planes)) &&
  decide (S.allKeys < 2 ^ S.planes) &&
  decide (S.d < 64) && decide (S.d + S.planes < 64) &&
  (decide (S.parts.length ≤ 1) || (S.g == 0 && !S.shifted)) &&
  decide (S.g ≤ S.firstBits)

/-- The conditions on the blocks of tree numbers: each is aligned, no two meet, and together they
cover all 2^g tree numbers; a block without a function names a row of the table. Without the shift
every block and every piece of the table belongs to function 0: the table is then one set of rows,
and a key of one function could lie in another function's table. -/
def Public.keysOK (S : Public) : Bool :=
  (S.keys.all fun b =>
    decide (b.logTrees ≤ S.g) && b.first % 2 ^ b.logTrees == 0 && decide (b.first < 2 ^ S.g) &&
    (b.function.isSome || decide (b.paddingRow < 2 ^ S.d))) &&
  allPairs (fun a b => !meet a.first a.logTrees b.first b.logTrees) S.keys &&
  (S.keys.map fun b => 2 ^ b.logTrees).sum == 2 ^ S.g &&
  (S.shifted ||
    ((S.keys.all fun b => b.function.getD 0 == 0) && S.tables.all fun t => t.function == 0))

/-- The conditions on the pieces of the table: they cover all rows, each row once, and a table that
is written out has 2^logRows rows. If h > 0 there is one piece for each number, in the order of the
numbers. -/
def Public.tablesOK (S : Public) : Bool :=
  decide (S.h ≤ S.d) &&
  (S.tables.all fun t => t.rows.isEmpty || t.rows.length == 2 ^ t.logRows) &&
  (if S.h != 0 then
    ((List.range S.tables.length).zip S.tables).all (fun p =>
      p.2.first == p.1 && decide (p.2.logRows ≤ S.d - S.h)) &&
    S.tables.length * 2 ^ (S.d - S.h) == 2 ^ S.d
  else
    (S.tables.all fun t =>
      decide (t.logRows ≤ S.d) && t.first % 2 ^ t.logRows == 0 && decide (t.first < 2 ^ S.d)) &&
    allPairs (fun a b => !meet a.first a.logRows b.first b.logRows) S.tables &&
    (S.tables.map fun t => 2 ^ t.logRows).sum == 2 ^ S.d)

/-- The conditions on the runs of padding: there are at most 4096; each lies in its part and in one
tree of a function, and holds a row of the table; the runs increase by part and first place; no two
meet. -/
def Public.paddingOK (S : Public) : Bool :=
  decide (S.padding.length ≤ 4096) &&
  (S.padding.all fun p =>
    let bits := S.parts.getD p.part 0
    decide (p.part < S.parts.length) && decide (1 ≤ p.length) && decide (p.logStep < bits) &&
    decide (p.first < 2 ^ bits) && decide (p.length ≤ 2 ^ (bits - p.logStep)) &&
    decide (p.first + (p.length - 1) * 2 ^ p.logStep < 2 ^ bits) &&
    decide (p.row < 2 ^ S.d) && (S.g == 0 || decide (S.g ≤ p.logStep)) &&
    S.keys.all fun b => !(b.holds S.g p.first && b.function.isNone)) &&
  ((S.padding.zip S.padding.tail).all fun q =>
    decide (q.1.part < q.2.part) || (q.1.part == q.2.part && decide (q.1.first < q.2.first))) &&
  allPairs (fun a b => !a.meets b) S.padding

/-- The condition on the order of the last key level: it names variables that every part has at
that level, each at most once. -/
def Public.orderOK (S : Public) : Bool :=
  let least := S.parts.foldl min S.firstBits
  (S.lastKeyLevelOrder.all fun j => decide (j < least - 1)) &&
  allPairs (fun a b => a != b) S.lastKeyLevelOrder

/-- The public inputs are well-formed and do not contradict themselves. -/
def Public.ok (S : Public) : Bool :=
  S.sizesOK && S.keysOK && S.tablesOK && S.paddingOK && !S.onlyPadding && S.orderOK

/-! ## The table and the padding -/

/-- A number below 2^64 as an element of the extension field. -/
def natE (n : Nat) : E := ofF (normF (UInt64.ofNat n))

/-- x if the bit is set, 1 - x if not. -/
def pick (bit : Bool) (x : E) : E := if bit then x else subE oneE x

/-- Row number t of the table, moved by the shift. 0 if no piece holds row t, which tablesOK rules
out for t below 2^d; the C++ (lkp_row) ends the process there. -/
def rowAt (S : Public) (theta : E) (t : Nat) : E :=
  let own := fun (p : TablePart) => (if S.h != 0 then t / 2 ^ S.h else t) % 2 ^ p.logRows
  let hit := S.tables.find? fun p =>
    if S.h != 0 then t % 2 ^ S.h == p.first else t / 2 ^ p.logRows == p.first / 2 ^ p.logRows
  match hit with
  | some p =>
    addE (if p.rows.isEmpty then natE (own p) else p.rows.getD (own p) zeroE)
      (mulE (natE p.function) theta)
  | none => zeroE

/-- The loop of halve. done: the entries so far, the last one first. -/
def halveLoop (x : E) : List E → List E → List E
  | a :: b :: l, done => halveLoop x l (addE a (mulE x (subE b a)) :: done)
  | _, done => done.reverse

/-- Folds the lowest bit out of a list's index at x: the entries number 2 i and 2 i + 1 become
their value at x on the line through them. -/
def halve (x : E) (l : List E) : List E := halveLoop x l []

/-- The multilinear extension of the table, moved by the shift, at a point of d coordinates: each
piece's own extension (a range table's in closed form) under the factor that picks the piece. The
extension of a repeated table does not depend on the coordinates above its own. -/
def tableAt (S : Public) (theta : E) (point : List E) : E :=
  S.tables.foldl (fun sum t =>
    let low := if S.h != 0 then 0 else t.logRows
    let high := if S.h != 0 then S.h else S.d
    let weight := (List.range (high - low)).foldl (fun w i =>
      mulE w (pick (t.first.testBit (low + i)) (point.getD (low + i) zeroE))) oneE
    let z := (point.drop S.h).take t.logRows
    let own :=
      if t.rows.isEmpty then
        ((List.range t.logRows).zip z).foldl (fun r p => addE r (mulE (natE (2 ^ p.1)) p.2)) zeroE
      else (z.foldl (fun l x => halve x l) t.rows).headD zeroE
    addE sum (mulE weight (addE own (mulE (natE t.function) theta)))) zeroE

/-- The padding as a list: how many places, and the number of the row that they hold. The runs come
first, then the blocks of trees that hold only padding. -/
def paddingList (S : Public) : List (Nat × Nat) :=
  (S.padding.map fun p => (p.length, p.row)) ++
  (S.keys.filter (·.function.isNone)).map fun b =>
    (2 ^ (S.firstBits - S.g + b.logTrees), b.paddingRow)

/-- The number of all places of padding. -/
def paddingCount (S : Public) : Nat := ((paddingList S).map (·.1)).sum

/-- The public factor: the product of alpha - row over all places of padding. -/
def factorOf (S : Public) (theta alpha : E) : E :=
  (paddingList S).foldl (fun a p => mulE a (powE (subE alpha (rowAt S theta p.2)) p.1)) oneE

/-- The key numbers i with the same bits as value wherever mask has a bit. -/
structure Cube where
  /-- the bits that are fixed -/
  mask : Nat
  /-- their values -/
  value : Nat
  deriving DecidableEq, Repr, Inhabited

/-- growBits x left steps b: the largest c from b on, at most b + steps, such that for every
number from b + 1 to c the block of that many bits which begins at x is aligned and has at most
left numbers. -/
def growBits (x left : Nat) : Nat → Nat → Nat
  | 0, b => b
  | k + 1, b =>
    if x % 2 ^ (b + 1) == 0 && decide (2 ^ (b + 1) ≤ left) then growBits x left k (b + 1) else b

/-- The loop of cubesOf: cubesLoop bits logStep low most x left. most: a bound on the number of
cubes; x: the next place, counted in steps; left: how many places are left. A block has at most 2^62
places, as in the C++ (lkp_cubes); a run has fewer than 2^63. -/
def cubesLoop (bits logStep low : Nat) : Nat → Nat → Nat → List Cube
  | 0, _, _ => []
  | k + 1, x, left =>
    if left == 0 then []
    else
      let b := growBits x left 62 0
      let all := 2 ^ bits - 1
      ⟨all ^^^ (all &&& ((2 ^ b - 1) * 2 ^ logStep)), low + x * 2 ^ logStep⟩ ::
        cubesLoop bits logStep low k (x + 2 ^ b) (left - 2 ^ b)

/-- A run of padding as cubes that do not meet. bits: the number of bits of a key's number. The
blocks first grow and then shrink, each size at most once on either side, and a size has fewer
than 64 bits: so 130 cubes are enough. -/
def cubesOf (p : Padding) (bits : Nat) : List Cube :=
  cubesLoop bits p.logStep (p.first % 2 ^ p.logStep) 130 (p.first / 2 ^ p.logStep) p.length

/-- The trees of a block as a cube. -/
def cubeOfBlock (S : Public) (b : KeyBlock) : Cube :=
  ⟨(2 ^ S.g - 1) ^^^ ((2 ^ S.g - 1) &&& (2 ^ b.logTrees - 1)), b.first⟩

/-- The sum of the equality vector at z over a cube. -/
def cubeWeight (c : Cube) (z : List E) : E :=
  ((List.range z.length).zip z).foldl (fun w p =>
    if c.mask.testBit p.1 then mulE w (pick (c.value.testBit p.1) p.2) else w) oneE

/-- The vector that is scalar times the equality vector at z on a cube, and 0 elsewhere. -/
def cubeTensor (c : Cube) (z : List E) (scalar : E) : Tensor where
  scalar := scalar
  pairs := ((List.range z.length).zip z).map fun p =>
    let picked := c.mask.testBit p.1
    let one := c.value.testBit p.1
    (if picked && one then zeroE else subE oneE p.2, if picked && !one then zeroE else p.2)

/-! ## Orders of rounds -/

/-- From the highest variable down. -/
def defaultOrder (variables : Nat) : List Nat := (List.range variables).reverse

/-- The named variables first, the others from the highest down. -/
def orderBeginning (first : List Nat) (variables : Nat) : List Nat :=
  first ++ (defaultOrder variables).filter fun j => !first.contains j

/-- A point given round by round, with each coordinate put back at its variable's place. Round j
has bound variable order[j]. -/
def byVariable (byRound : List E) (order : List Nat) : List E :=
  (List.range byRound.length).map fun t => ((order.zip byRound).lookup t).getD zeroE

/-! ## The summands -/

/-- The product of two shown maps. -/
def summandProduct : Psc.Summand where
  shown := 2
  kept := 0
  degree := 2
  coeffs := fun _ y => [mulE (y.getD 0 zeroE) (y.getD 1 zeroE)]

/-- The first step of the tie: y0 - a y1^2 y2. -/
def summandTieFirst (a : E) : Psc.Summand where
  shown := 3
  kept := 0
  degree := 3
  coeffs := fun _ y =>
    [subE (y.getD 0 zeroE)
      (mulE (mulE (mulE a (y.getD 1 zeroE)) (y.getD 1 zeroE)) (y.getD 2 zeroE))]

/-- A later step of the tie: y0^2 y1. -/
def summandTie : Psc.Summand where
  shown := 2
  kept := 0
  degree := 3
  coeffs := fun _ y => [mulE (mulE (y.getD 0 zeroE) (y.getD 0 zeroE)) (y.getD 1 zeroE)]

/-- The factor of a bit in a leaf of the table's tree: alpha - 1 - table, at a point on all mu + d
variables. The table's variables are those above the planes'. -/
def leavesFactor (S : Public) (theta alpha : E) (point : List E) : E :=
  subE (subE alpha oneE) (tableAt S theta (point.drop S.mu))

/-- The leaves of the table's tree: 1 + bit (alpha - 1 - table). The bits are a kept map. -/
def summandLeaves (S : Public) (theta alpha : E) (order : List Nat) : Psc.Summand where
  shown := 0
  kept := 1
  degree := 0
  coeffs := fun byRound _ => [oneE, leavesFactor S theta alpha (byVariable byRound order)]

/-- y^2 - y, which is 0 exactly at 0 and 1. -/
def summandBits : Psc.Summand where
  shown := 1
  kept := 0
  degree := 2
  coeffs := fun _ y => [subE (mulE (y.getD 0 zeroE) (y.getD 0 zeroE)) (y.getD 0 zeroE)]

/-! ## Numbers of mask entries -/

/-- The number of mask entries that come from the second message (keyMasks of verify) if the caller
names one: two for each part. -/
def keyMasks (S : Public) : Nat := 2 * S.parts.length

/-- The number of all mask entries that a lookup uses. The prover sends as many elements. -/
def allMasks (S : Public) : Nat :=
  7 + 6 * (S.planes - 2) + 5 * (S.parts.length - 1) +
  (S.parts.map fun v => ((List.range v).map fun k => 2 * k + 5).sum).sum +
  ((List.range S.d).map fun l => 2 * (S.mu + l) + 5).sum +
  (1 + S.mu + 2 * S.d) + (1 + 2 * (S.mu + S.d) + 2 + 1)

/-! ## The rounds -/

/-- The rounds of a product tree from the root down: level l is a sumcheck in l + more variables
with two shown values, followed by the draw "LINE" (line, OnBytes/Iop/Psc.lean). -/
def treeRounds (work levels more : Nat) : List Fmt.Round :=
  (List.range levels).flatMap fun l =>
    Psc.roundsOf work { degree := List.replicate (l + more) 3 } ++ [rDraw "LINE" work 1]

/-- The rounds of one lookup, for tests. work: the bits of proof of work that every round with a
draw is given here, as in Psc.roundsOf. -/
def roundsOf (work : Nat) (S : Public) : List Fmt.Round :=
  (if S.shifted then [rDraw "LKP shift" work 1] else []) ++ [rDraw "LKP" work 1] ++
  ((List.range (S.planes - 1)).flatMap fun j =>
    Psc.roundsOf work { degree := [], degreeY := 3, values := if j == 0 then 3 else 2 }) ++
  ((List.range (S.parts.length - 1)).flatMap fun _ => Psc.roundsOf work { degree := [] }) ++
  [rDraw "JOIN" work S.mu] ++
  (S.parts.flatMap fun v => treeRounds work v 0) ++
  treeRounds work S.d S.mu ++
  Psc.roundsOf work
    { degree := List.replicate S.d 3 ++ List.replicate S.mu 2, withY := false, degreeY := 0,
      values := 0 } ++
  [rDraw "ZERO" work (S.mu + S.d)] ++
  Psc.roundsOf work { degree := List.replicate (S.mu + S.d) 3, degreeY := 2, values := 1 }

/-! ## What is handed on -/

/-- The claim on one part of the keys: the sum of weights[i] times key number i, as it is before
the shift, plus the mask form, equals the target. -/
structure Keys where
  /-- the point of the equality vector in the weights -/
  point : List E
  /-- the equality vector at the point, made 0 at every place of padding -/
  weights : Form
  /-- the mask form -/
  masks : MaskForm
  /-- the target, with the shares of the padding and of the shift taken out -/
  target : E
  deriving Inhabited

/-- What one lookup hands on, besides the rows that it has added to the group.

What is handed on. Rows on mask entries and on the vector of multiplicities, which the block adds to
the caller's group, and one claim for each part of the keys: a weighted sum of the real keys, plus a
mask form, equals a target. The weights are 0 at every place of padding, and the padding's share is
already taken out of the target. Two tests on values are made here: that the two claims which a
level leaves are at one point (line), and that each row that is added has the coefficient 0 on every
entry of the group's messages that masks an answer to a sample (Blk.addRow). All else is left to the
blocks that follow, which test the rows against the committed vectors. -/
structure Out where
  /-- the shift; 0 if there is none -/
  theta : E
  /-- the point at which the two products are compared -/
  alpha : E
  /-- one claim for each part of the keys. The caller must make a row of each; nothing here tests
  that it does. -/
  keys : List Keys
  deriving Inhabited

/-! ## The block -/

/-- What the steps of one lookup are told. -/
structure Env where
  /-- the public inputs -/
  S : Public
  /-- adds a vector on the mu + d variables of the multiplicities, the plane in the low ones, to a
  row. It must read the real planes only (liveBlocks cuts them into aligned blocks); nothing here
  tests that. -/
  planesAt : Row → Tensor → Row
  /-- the oracle message that gives the mask entries -/
  masks : Nat
  /-- the oracle message that gives, at each part's last key level, the two mask entries under which
  the halves of alpha - key are shown; line joins them into the claim on the keys -/
  keyMasks : Nat
  /-- the group to which the rows are added -/
  group : Nat

/-- The n fresh mask entries of one sumcheck: first those of the hiding polynomial, then one for
each shown value. keys: the last two, which mask the two shown values, come from e.keyMasks. -/
def fresh (e : Env) (n : Nat) (keys : Bool) : Blk (List Slot) := do
  if keys then
    Blk.must (decide (2 ≤ n))
    let a ← takeSlots e.masks (n - 2)
    let b ← takeSlots e.keyMasks 2
    pure (a ++ b)
  else takeSlots e.masks n

/-- Adds a row to the group. Every row of the block goes into the group here, so that no caller can
lose one. Fails if the row reads the main table of a message that the public inputs do not declare
as read. -/
def leave (e : Env) (row : Row) : Blk Unit := do
  let declared := fun (o : Nat) => e.S.readFrom.contains o
  Blk.must ((row.terms.all fun t => t.part != .main || declared t.oracle) &&
    (row.units.all fun t => t.part != .main || declared t.oracle) &&
    (row.runs.all fun t => t.part != .main || declared t.oracle) &&
    row.forms.all fun t => declared t.oracle)
  Blk.addRow e.group row

/-- One sumcheck with fresh mask entries. Its row goes to the group. lastOfKeys: the last level of a
key tree, whose last two mask entries come from e.keyMasks (fresh). kept: where its kept maps live.
place: puts the coordinates of its point back at their variables' places. -/
def psc (e : Env) (c : Psc.Claim) (S : Psc.Summand) (lastOfKeys : Bool := false)
    (kept : List MapAt := []) (place : List E → List E := id) : Blk Psc.Out := do
  let fr ← fresh e (Psc.masksOf c S) lastOfKeys
  let o ← Psc.verify c S fr
  let o := { o with
    point := place o.point
    ends := o.ends.map fun x => { x with point := place x.point } }
  leave e (← Blk.get (Psc.rowU o kept))
  pure o

/-- A claim on a value that is never sent, read as a sum without variables. Fails if the claim's
point has a coordinate. -/
def onValue (c : PointClaim) : Blk Psc.Claim := Blk.get (Psc.Claim.atPoint c [])

/-- The levels of a product tree from the root down. keys: the tree is a key tree, whose last level
has an order and two mask entries of its own. levels: the number of levels. more: the number of
variables of the top level. The unnamed number counts the levels that are left, and c is the claim
on the level that is reached. Returns the claim on the leaves. -/
def levelChain (e : Env) (keys : Bool) (levels more : Nat) : Nat → PointClaim → Blk PointClaim
  | 0, c => pure c
  | n + 1, c => do
    let l := levels - (n + 1)
    let variables := more + l
    let lastOfKeys := keys && l + 1 == levels
    let order :=
      if lastOfKeys then orderBeginning e.S.lastKeyLevelOrder variables
      else defaultOrder variables
    Blk.must (order.length == variables && c.point.length == variables)
    let sum : Psc.Claim :=
      { vars := order.map fun t => Psc.Weight.equality (c.point.getD t zeroE) 3
        masks := c.masks
        target := c.value }
    let o ← psc e sum summandProduct lastOfKeys [] fun p => byVariable p order
    match o.ends with
    | [e0, e1] =>
      let next ← line e0 e1
      levelChain e keys levels more n next
    | _ => Blk.fail

/-- The later steps of the tie. onPower: the claim on the power that is reached. Returns the claims
on the planes' roots from plane 1 on. The number counts the steps that are left. -/
def tieSteps (e : Env) : Nat → PointClaim → Blk (List PointClaim)
  | 0, onPower => pure [onPower]
  | n + 1, onPower => do
    let o ← psc e (← onValue onPower) summandTie
    match o.ends with
    | [power, plane] =>
      let rest ← tieSteps e n power
      pure (plane :: rest)
    | _ => Blk.fail

/-- From the product of the parts' roots to each root. onRoot: the claim on the product of the roots
that are left. The number counts the steps that are left. -/
def partSteps (e : Env) : Nat → PointClaim → Blk (List PointClaim)
  | 0, onRoot => pure [onRoot]
  | n + 1, onRoot => do
    let o ← psc e (← onValue onRoot) summandProduct
    match o.ends with
    | [root, rest] =>
      let more ← partSteps e n rest
      pure (root :: more)
    | _ => Blk.fail

/-- The claims on the planes' roots as one claim on the top level of the table's tree, at the
point r. A plane that is not real has the root 1. -/
def joinPlanes (S : Public) (r : List E) (onPlane : List PointClaim) : PointClaim :=
  (List.range (2 ^ S.mu)).foldl (fun (c : PointClaim) j =>
    let weight := eqWeight r j oneE
    match onPlane[j]? with
    | some p =>
      { c with
        masks := c.masks ++ Psc.scaleForm weight p.masks
        value := addE c.value (mulE weight p.value) }
    | none => { c with value := addE c.value weight }) ⟨r, [], zeroE⟩

/-- The key trees of all parts, one after the other: the parts' sizes in bits, and the claims on
their roots. Returns the claims on their leaves. -/
def keyTrees (e : Env) : List Nat → List PointClaim → Blk (List PointClaim)
  | v :: vs, c :: cs => do
    let x ← levelChain e true v 0 v c
    let rest ← keyTrees e vs cs
    pure (x :: rest)
  | _, _ => pure []

/-- What the making of a claim on the keys carries along. -/
structure KeyAcc where
  /-- the target so far -/
  target : E
  /-- the weights so far -/
  weights : Form
  /-- for each block of tree numbers the weight of its real places -/
  real : List E

/-- The places of a cube hold one row: the row's share is subtracted from the target, and the
places' weight becomes 0. block: the number of the block of tree numbers in whose trees the cube
lies, so that the cube's weight is taken off the weight of that block's real places; none for trees
that hold only padding. -/
def takeOut (S : Public) (theta : E) (point : List E) (a : KeyAcc) (cube : Cube) (row : Nat)
    (block : Option Nat) : KeyAcc :=
  let weight := cubeWeight cube point
  { target := subE a.target (mulE weight (rowAt S theta row))
    weights := a.weights.add (cubeTensor cube point (negE oneE))
    real :=
      match block with
      | some b => a.real.set b (subE (a.real.getD b zeroE) weight)
      | none => a.real }

/-- The claim on the leaves alpha - key of one part's tree, rewritten as a claim on the real keys as
they are before the shift. -/
def keysOf (S : Public) (theta alpha : E) (part : Nat) (onLeaves : PointClaim) : Keys :=
  let point := onLeaves.point
  let start : KeyAcc :=
    { target := subE alpha onLeaves.value
      weights := Form.ofTensor (Tensor.eq point)
      real := S.keys.map fun b =>
        if b.function.isNone then zeroE else cubeWeight (cubeOfBlock S b) point }
  let a1 := (S.keys.filter (·.function.isNone)).foldl
    (fun a b => takeOut S theta point a (cubeOfBlock S b) b.paddingRow none) start
  let a2 := (S.padding.filter (·.part == part)).foldl (fun a p =>
    let b := S.keys.findIdx fun k => k.holds S.g p.first
    (cubesOf p point.length).foldl (fun a c => takeOut S theta point a c p.row (some b)) a) a1
  let target := (S.keys.zip a2.real).foldl (fun t q =>
    match q.1.function with
    | some n => if n == 0 then t else subE t (mulE (mulE theta (natE n)) q.2)
    | none => t) a2.target
  { point := point
    weights := a2.weights
    masks := Psc.scaleForm (negE oneE) onLeaves.masks
    target := target }

/-- Notes the targets of the claims on the keys. -/
def noteKeys : List Keys → Blk Unit
  | [] => pure ()
  | k :: ks => do
    Blk.note "LKP: a part's key claim" k.target
    noteKeys ks

/-- The samples of all listed oracle messages have been answered. -/
def mustBeSampled : List Nat → Blk Unit
  | [] => pure ()
  | o :: os => do
    Blk.must (← Blk.oracle o).sampled
    mustBeSampled os

/-- One drawn element, in a round in which the prover sends nothing. -/
def drawOne (name : String) : Blk E := do
  Blk.get (← hearDraw name 1).head?

/-- The steps of one lookup, in their order.

The steps, in the order of the rounds:
 0. if Public.shifted is set, as it must be where several functions, each with a table of its own,
    share the lookup: theta is drawn, and the keys and rows of function number n are moved by n
    theta. The protocol's argument is that a key which is in no row of its own function's table
    then passes only if key + n theta = row + m theta for a row of another function m: one value
    of theta for each such row. In every case alpha is drawn;
 1. the tie: the root of the key side equals the public factor times the product of the roots of
    the planes of bits, plane j raised to the power 2^j, by squaring and multiplying;
 2. if the keys come in parts (for a prover that cannot hold all keys at once): from the product of
    the parts' roots to each root;
 3. a point is drawn that makes the claims on the planes' roots one claim;
 4. the levels of each part's key tree, then the levels of the table's tree;
 5. the leaves of the table's tree, which are affine in the bits;
 6. a point is drawn, and a sumcheck runs on bit^2 - bit under the equality vector at that point,
    with the target 0: the claim that the bits are 0 or 1;
 7. without a message: the row that says that the counts add up to the number of keys that are not
    padding. It gives both sides of the idea's equation the same degree in alpha. -/
def run (e : Env) : Blk Out := do
  let S := e.S
  let theta ← if S.shifted then drawOne "LKP shift" else pure zeroE
  let alpha ← drawOne "LKP"
  let a := factorOf S theta alpha
  Blk.note "LKP: alpha" alpha
  Blk.note "LKP: the public factor a" a
  -- 1: the tie
  let first ← psc e { vars := [], masks := [], target := zeroE } (summandTieFirst a)
  let (onRoot, onPower, onPlane0) ←
    match first.ends with
    | [x, y, z] => pure (x, y, z)
    | _ => Blk.fail
  let later ← tieSteps e (S.planes - 2) onPower
  -- 2: from the product of the parts' roots to each root
  let onRoots ← partSteps e (S.parts.length - 1) onRoot
  -- 3: one claim on the top level of the table's tree
  let r ← hearDraw "JOIN" S.mu
  let onTop := joinPlanes S r (onPlane0 :: later)
  Blk.note "LKP: the table side's first claim" onTop.value
  -- 4: the key trees, then the table's tree
  let onLeaves ← keyTrees e S.parts onRoots
  let onTable ← levelChain e false S.d S.mu S.d onTop
  -- 5: the leaves of the table's tree
  let all := S.mu + S.d
  let order := defaultOrder all
  let bitsAt : MapAt := fun row point coeff => e.planesAt row (Tensor.eq point coeff)
  let leaves ← psc e
    { vars := order.map fun t =>
        Psc.Weight.equality (onTable.point.getD t zeroE) (if t < S.mu then 2 else 3)
      masks := onTable.masks
      target := onTable.value }
    (summandLeaves S theta alpha order) false [bitsAt] fun p => byVariable p order
  Blk.note "LKP: the leaves' factor" (leavesFactor S theta alpha leaves.point)
  -- 6: the bits are bits
  let zeta ← hearDraw "ZERO" all
  let bits ← psc e
    { vars := order.map fun t => Psc.Weight.equality (zeta.getD t zeroE) 3
      masks := []
      target := zeroE }
    summandBits false [] fun p => byVariable p order
  leave e (pointRow (← Blk.get bits.ends.head?) bitsAt)
  -- 7: the counts add up to the number of keys that are not padding
  leave e (e.planesAt { target := natE (S.allKeys - paddingCount S) }
    { pairs := ((List.range S.mu).map fun t => (oneE, natE (2 ^ 2 ^ t))) ++
        List.replicate S.d (oneE, oneE) })
  let keys := ((List.range onLeaves.length).zip onLeaves).map fun p => keysOf S theta alpha p.1 p.2
  Blk.must (keys.length == S.parts.length)
  noteKeys keys
  pure { theta := theta, alpha := alpha, keys := keys }

/-- The verifier's part in one lookup. S: the public inputs; that the chain's first query binds
them, or values from which they follow, is the caller's duty (see below). planesAt: adds a vector
on the multiplicities to a row, and must read the real planes only. masks: the oracle message from
whose mask rows the lookup takes its entries. group: where the rows go; the messages that are read
and the message masks are members of it already. keyMasks, if named: the message that gives
keyMasks S of the entries. It need not be a member of the group: the block's own rows name none of
its entries, only the claims on the keys do. Fails if the public inputs are not well-formed, or if
the sample of a message that is read or that gives mask entries has not been answered.

What the caller does. It says where a vector on the multiplicities is in what was sent (planesAt);
that routine must read the real planes only. It makes a row of every claim on the keys. Without
these rows a lookup says nothing about what was sent, and no honest run would show that. The C++
ends the process if a claim is dropped and the channel has not refused the proof (LkpKeyClaim). The
type here does not enforce it: the caller owes it, and nothing here tests that it uses Out.keys.

What must be fixed before the run, the caller's duty. Everything in Public (sizes, tables, which
keys belong to which function, padding, orders) must be bound by the hash chain's first query, or
follow from values that are. A prover that can still choose a row of the table when it knows alpha
picks it so that the two products agree, for keys that are in no row. The C++ entry points take the
public inputs as a Public<LkpPublic>: a value that a chain's Binder has bound, or that was derived
from such values alone (blocks/chain/public.h). Lkp.verify takes a plain value: the type does not
enforce where it came from, and the caller owes it. -/
def verify (S : Public) (planesAt : Row → Tensor → Row) (masks group : Nat)
    (keyMasks : Option Nat := none) : Blk Out := do
  mustBeSampled (masks :: keyMasks.toList)
  Blk.must S.ok
  mustBeSampled S.readFrom
  run { S := S, planesAt := planesAt, masks := masks, keyMasks := keyMasks.getD masks,
        group := group }

/-! ## For the caller: vectors on the real planes, and on one function's keys -/

/-- The loop of liveBlocks: liveLoop live most first. most: a bound on the number of blocks; first:
the next plane. There are at most 64 planes, so a block has at most 6 bits. -/
def liveLoop (live : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | k + 1, first =>
    if live ≤ first then []
    else
      let bits := growBits first (live - first) 6 0
      (first, bits) :: liveLoop live k (first + 2 ^ bits)

/-- The real planes 0 .. live - 1 as aligned blocks of plane numbers: the first number and the
size in bits. -/
def liveBlocks (live : Nat) : List (Nat × Nat) := liveLoop live 64 0

/-- Sets the variables from low up to below high to the bits of number: they leave their factors in
the scalar. The other variables stay. For a vector of product form: a factor that is written out is
dropped, where the C++ (lkp_on_block, lkp_weights_of_block) ends the process. -/
def setBits (v : Tensor) (low high number : Nat) : Tensor :=
  ((List.range v.pairs.length).zip v.pairs).foldl (fun (part : Tensor) p =>
    if low ≤ p.1 && p.1 < high then
      part.scale (if number.testBit p.1 then p.2.2 else p.2.1)
    else part.push p.2.1 p.2.2) { scalar := v.scalar }

/-- The part of a vector on the multiplicities that lies on one block of planes (first plane, size
in bits): the block's own plane variables stay, and the higher plane variables are set to the bits
of the block's first plane. -/
def onBlock (v : Tensor) (mu : Nat) (block : Nat × Nat) : Tensor := setBits v block.2 mu block.1

/-- The weights of a claim on the keys, restricted to the own key vector of the function that holds
the block b of tree numbers: the tree bits above the block's own are set to those of b.first. For
the weights that this file makes, which are sums of product forms on all bits of a key's number:
single entries are dropped. Not tested here, where the C++ (lkp_weights_of_block) ends the process
otherwise: that b has a function, and that the weights have this form. -/
def weightsOfBlock (S : Public) (weights : Form) (b : KeyBlock) : Form where
  tensors := weights.tensors.map fun v => setBits v b.logTrees S.g b.first

end Lkp

end OnBytes
