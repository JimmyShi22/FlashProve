-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Twin.lean: a committer that runs: from a stored table's plain entries and the
committer's random values to the table's root, its name, its out-of-domain (OOD) sample and the
commitment ID. Definitions alone.

What it is. The programs (the C++ implementation that comes with this Lean code) make a commitment
in two layers. The first turns a secret seed into random values and the weights into a table of
field elements. The second, which is written here, is a function of that table and these values:
   1. c, the digest of the three public files (docs/format/FORMAT.md, R4.9);
   2. a row's message: its plain entries, then its pads; a row's polynomial: the tail's entries are
      the lowest coefficients, the message's follow;
   3. the symbol of a row at a position: the polynomial's value at the position's point;
   4. a leaf for each position: all rows' symbols there, then the leaf's salt; the hash tree over
      the leaves; its root;
   5. the table's name: root, c and six words of the shape (R4.10);
   6. the OOD seeds, drawn from the name (R4.8): a point of the cube and a factor each;
   7. the OOD answers (R13.8): for each row and seed, the sum over the plain entries of eq(place;
      point) times the entry, plus the factor times the element of the extension field that the
      seed's three pads spell;
   8. the commitment ID (R4.11): one hash of c, the name, the seeds and the answers.
It follows the format pages and a written description of what the programs compute, which is not in
the repository.
The file's name: it is meant as a second text, on byte strings, of the committer that
Johnson/Top/ToldCommitPlain.lean writes as mathematics. No theorem in this file ties the two.

One text, three arguments.
   The shape (a, l, r, v, s, sigma) is an argument: the same definitions are taken at any size. They
      are the format's code only at shapes with at most 2^32 positions (a ≤ 32): above that the
      library's roots of unity stay at the order 2^32 (`Fmt.M1.rootOf2`), so that positions share
      points. The functions are total there all the same.
   The hash is an argument, as in the files of Fmt/ whose names end in W: a monad m and a function h
      (number, tree, index, start, bytes) with values in m. At m := Id and h := Fmt.formatHash they run at
      the format's own hash (`commit`). At h := Fmt.HM ask every call is a question to one oracle.
   The encoder is an argument of the innermost definition (`coreW`): a function from a position to
      the column of all rows' symbols. `plainW` lays the plain encoder, which evaluates each row's
      polynomial at each point by Horner's rule (`Fmt.M1.symF`): l + r multiplications a symbol.

Inputs by address. The table's entries, tails and pads are functions of a row and a place, a salt is
a function of a leaf (`Table`). They are read only at rows below 2^v, plain entries below l - 3 s,
tail entries below r, pads below 3 s and leaves below 2^a. So no input has a wrong length.
No input is refused, and none is sent to a fixed commitment: a raw value is normalised as follows.
Choices that make the functions total:
   a word that is not below p counts modulo p: it enters only sums and products that reduce
      (Fmt/FieldE.lean), so every symbol and every answer is below p;
   a salt is cut to sigma bytes, or filled up with zero bytes (`Fmt.fit`);
      (`fitted` applies these two rules to the random values; that the committer reads them through
      it alone is proved in Johnson/Bind/TwinFitted.lean);
   where 3 s is at least l there are no plain entries; where it exceeds l the encoder cuts the
      message to l entries;
   where the drawing of the seeds returns nothing, the empty list stands for them (as in
      `OnBytes.Key.commitmentId`); it returns nothing only if the hash's value is not 32 bytes long.

The order and number of the hash's calls, read off the text: c (1); the leaves in the order of the
positions (2^a); the vertices depth by depth from the leaves' parents up, within a depth in the
order of places (2^a - 1); if s > 0 the seeds' chain: its first value (1) and the calls under the
number 162 that `Fmt.recordSeedsW` fetches; the ID (1).

Main definitions: `Shape`, `Table`, `Coins`, `fitted`, `Out`, `laid`, `columnOf`, `rootW`, `seedsW`,
`eqAt`, `answers`, `closeW`, `coreW`, `plainW`, `commitW`, `commit`.

Limits.
(1) No theorem is in this file, and no theorem ties it to the programs. Evaluations have compared it
    with runs of the programs at the small stored example's public files, on synthetic weights, and
    nowhere else; what was compared, and what was not, stands in Johnson/Bind/README.md ("What is
    run, not proved"). Tests at small shapes are in Johnson/Bind/TwinKnown.lean, at a stored
    example's files in Johnson/Bind/TwinAnchor.lean.
(2) Nothing is said on what a commitment fixes or hides: no binding of the commitment, no
    correctness of extraction, no index privacy.
(3) From a secret seed to the random values, and from weights to the plain entries: not here.
    Nothing asks that the random values are fresh or differ from leaf to leaf (R4.12, R7.3).
(4) The key file's proofs are not made here, nor the leaf tables and their links: the commitment ID
    does not depend on them.
(5) The answers sum over all plain entries of a row, as the format page has it.
(6) The definitions are total at every shape; they are the format's only where a ≤ 32, l + r ≤ 2^a,
    3 s < l and sigma is a multiple of 8 from 40 to 64 (R7.3, R12.1, R12.11, R13.8). Elsewhere
    nothing is refused: where l + r exceeds 2^a different tables have the same encoded table; where
    3 s is at least l a row has no plain entry.

-/
import Fmt.Rules7
import Fmt.RecordSeeds
import Fmt.M1Codes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open Fmt (Ext Fld)

/-! ### The shape and the inputs -/

/-- A stored table's shape: the six words of its name (R4.10). -/
structure Shape where
  /-- A row's codeword has 2^a symbols; the tree has 2^a leaves. -/
  a : Nat
  /-- The entries of a row's message: plain entries, then pads. -/
  l : Nat
  /-- The entries of a row's random tail. -/
  r : Nat
  /-- The table has 2^v rows. -/
  v : Nat
  /-- The OOD answers of a row: as many as there are OOD seeds. -/
  s : Nat
  /-- The bytes of a leaf's salt. -/
  sigma : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Shape

/-- The number of rows. -/
def rows (S : Shape) : Nat := 2 ^ S.v

/-- The pads of a row: three for each answer. -/
def pads (S : Shape) : Nat := 3 * S.s

/-- The plain entries of a row. -/
def plain (S : Shape) : Nat := S.l - 3 * S.s

/-- The coordinates of an OOD seed's point: the least C with l ≤ 2^C. -/
def cube (S : Shape) : Nat := if S.l ≤ 1 then 0 else Nat.log2 (S.l - 1) + 1

/-- The rows' code. -/
def code (S : Shape) : Fmt.M1.Code := ⟨S.a, S.l, S.r⟩

end Shape

/-- What the committer lays into a table, by address. -/
structure Table where
  /-- Row, place: a plain entry. -/
  entry : Nat → Nat → UInt64
  /-- Row, place: an entry of the row's random tail. -/
  tail : Nat → Nat → UInt64
  /-- Row, number: a pad. The pads 3 i, 3 i + 1, 3 i + 2 belong to the answer i. -/
  pad : Nat → Nat → UInt64
  /-- Leaf: its salt. -/
  salt : Nat → ByteArray

/-- The committer's random values, by address: what of a table is not the plain entries. The type
depends on no shape and on no public file. -/
structure Coins where
  /-- Row, place: an entry of the row's random tail. -/
  tail : Nat → Nat → UInt64
  /-- Row, number: a pad. -/
  pad : Nat → Nat → UInt64
  /-- Leaf: its salt. -/
  salt : Nat → ByteArray

/-- The table of given plain entries and random values. -/
def Table.of (entry : Nat → Nat → UInt64) (c : Coins) : Table := ⟨entry, c.tail, c.pad, c.salt⟩

/-- The word below p that a word counts as. -/
def residue (w : UInt64) : UInt64 := Fld.two.red w.toNat

/-- The random values as the committer reads them at the shape S: every word as its residue modulo
p, every salt cut to sigma bytes or filled up with zero bytes. -/
def fitted (S : Shape) (c : Coins) : Coins where
  tail b j := residue (c.tail b j)
  pad b j := residue (c.pad b j)
  salt x := Fmt.fit S.sigma (c.salt x)

/-- What the committer computes. -/
structure Out where
  /-- The root of the tree over the encoded table. -/
  root : ByteArray
  /-- The table's name. -/
  name : ByteArray
  /-- The OOD seeds: a point and a factor each. -/
  seeds : List (List Ext × Ext)
  /-- The OOD answers: by row, within a row by seed. -/
  answers : List Ext
  /-- The commitment ID. -/
  id : ByteArray

/-! ### The encoded table, by Horner's rule -/

/-- A row's message: the plain entries, then the pads. -/
def message (S : Shape) (T : Table) (b : Nat) : List UInt64 :=
  (List.range S.plain).map (T.entry b) ++ (List.range S.pads).map (T.pad b)

/-- A row's tail. -/
def tailOf (S : Shape) (T : Table) (b : Nat) : List UInt64 := (List.range S.r).map (T.tail b)

/-- Every row's message and tail, as lists. -/
def laid (S : Shape) (T : Table) : List (List UInt64 × List UInt64) :=
  (List.range S.rows).map fun b => (message S T b, tailOf S T b)

/-- The column at the position x: every row's symbol there, in the order of the rows. -/
def columnOf (S : Shape) (rows : List (List UInt64 × List UInt64)) (x : Nat) : List UInt64 :=
  rows.map fun w => Fmt.M1.symF S.code x w.1 w.2

/-! ### The OOD answers -/

/-- eq(p; z): the product over the coordinates z_t of z_t where bit t of p is 1, and of 1 - z_t
where it is 0. Bit 0 is the lowest and goes with the first coordinate. -/
def eqAt : List Ext → Nat → Ext
  | [], _ => Fld.oneE
  | z :: zs, p =>
    Fld.two.mulE (if p % 2 = 1 then z else Fld.two.subE Fld.oneE z) (eqAt zs (p / 2))

/-- eq(p; z) at the places p below n. -/
def eqTable (z : List Ext) (n : Nat) : Array Ext := (Array.range n).map (eqAt z)

/-- acc plus the sum of row(q) times eqs(q) over the n places q from p on. -/
def sumFrom (eqs : Array Ext) (row : Nat → UInt64) : Nat → Nat → Ext → Ext
  | 0, _, acc => acc
  | n + 1, p, acc =>
    sumFrom eqs row n (p + 1) (Fld.two.addE acc (Fld.two.scaleE (row p) (eqs.getD p Fld.zeroE)))

/-- The answer i of the row b, at the table eqs of the seed's point and the seed's factor. -/
def answerAt (S : Shape) (T : Table) (b i : Nat) (eqs : Array Ext) (factor : Ext) : Ext :=
  Fld.two.addE (sumFrom eqs (T.entry b) S.plain 0 Fld.zeroE)
    (Fld.two.mulE factor (T.pad b (3 * i), T.pad b (3 * i + 1), T.pad b (3 * i + 2)))

/-- All answers at given seeds: by row, within a row by seed. Each seed's table of eq is made once.
-/
def answers (S : Shape) (T : Table) (seeds : List (List Ext × Ext)) : List Ext :=
  let prepared := Fmt.numbered 0 (seeds.map fun y => (eqTable y.1 S.plain, y.2))
  (List.range S.rows).flatMap fun b => prepared.map fun w => answerAt S T b w.1 w.2.1 w.2.2

/-- The table's name. -/
def nameOf (S : Shape) (root cfg : ByteArray) : ByteArray :=
  Fmt.tableName root cfg S.a S.l S.r S.v S.s S.sigma

/-! ### What hashes: over any monad, the hash an argument -/

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The leaf at the position x of a stored table's tree: number 174, tree 0. -/
def leafAtW (S : Shape) (start : ByteArray) (col : List UInt64) (salt : ByteArray) (x : Nat) :
    m ByteArray :=
  Fmt.leafW h 174 0 S.a x start col (Fmt.fit S.sigma salt)

/-- The n leaves from the position x on, behind those that are there. -/
def leavesFromW (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) : Nat → Nat → Array ByteArray → m (Array ByteArray)
  | 0, _, acc => pure acc
  | n + 1, x, acc => do
    let d ← leafAtW h S (start x) (col x) (salt x) x
    leavesFromW S start col salt n (x + 1) (acc.push d)

/-- The n vertices from the place i on of the depth above `below`, behind those that are there: the
vertex at the place i has the children at the places 2 i and 2 i + 1. -/
def upFromW (cfg : ByteArray) (below : Array ByteArray) :
    Nat → Nat → Array ByteArray → m (Array ByteArray)
  | 0, _, acc => pure acc
  | n + 1, i, acc => do
    let d ← Fmt.vertexW h cfg (below.getD (2 * i) ByteArray.empty)
      (below.getD (2 * i + 1) ByteArray.empty)
    upFromW cfg below n (i + 1) (acc.push d)

/-- From the values of the depth d to the root. -/
def climbW (cfg : ByteArray) : Nat → Array ByteArray → m ByteArray
  | 0, now => pure (now.getD 0 ByteArray.empty)
  | d + 1, now => do
    let up ← upFromW h cfg now (2 ^ d) 0 #[]
    climbW cfg d up

/-- The root of the tree over the columns: all leaves, then depth by depth. `start` is each leaf's
start; the committer lays cfg there (`coreW`). -/
def rootW (S : Shape) (cfg : ByteArray) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) : m ByteArray := do
  let leaves ← leavesFromW h S start col salt (2 ^ S.a) 0 #[]
  climbW h cfg S.a leaves

/-- The OOD seeds, from the table's name. None are drawn where the shape has no answers. -/
def seedsW (S : Shape) (name : ByteArray) : m (List (List Ext × Ext)) :=
  if S.s = 0 then pure [] else do
    let r ← Fmt.recordSeedsW h .two name S.cube S.s
    pure (r.getD [])

/-- From a root on: the name, the seeds, the answers as a function of the seeds, the ID. -/
def closeW (S : Shape) (cfg root : ByteArray) (answersAt : List (List Ext × Ext) → List Ext) :
    m Out := do
  let name := nameOf S root cfg
  let seeds ← seedsW h S name
  let given := answersAt seeds
  let id ← Fmt.publishedIDW h cfg name (Fmt.flatSeeds seeds) given []
  pure ⟨root, name, seeds, given, id⟩

/-- The committer behind the public files' digest cfg, with the encoder's columns as an argument.
cfg is the start of every leaf and of every vertex. -/
def coreW (S : Shape) (cfg : ByteArray) (col : Nat → List UInt64) (T : Table) : m Out := do
  let root ← rootW h S cfg (fun _ => cfg) col T.salt
  closeW h S cfg root (answers S T)

/-- The committer behind cfg, at the plain encoder. The rows' lists are made once. -/
def plainW (S : Shape) (cfg : ByteArray) (T : Table) : m Out :=
  let rows := laid S T
  coreW h S cfg (columnOf S rows) T

/-- The committer: it asks for the digest of the public files, then goes on behind it. -/
def commitW (S : Shape) (files : List ByteArray) (T : Table) : m Out := do
  let cfg ← Fmt.configDigestW h files
  plainW h S cfg T

end

/-! ### At the format's own hash -/

/-- `commitW` at the format's own hash. -/
def commit (S : Shape) (files : List ByteArray) (T : Table) : Out :=
  commitW (m := Id) Fmt.formatHash S files T

/-- `closeW` at the format's own hash. -/
def close (S : Shape) (cfg root : ByteArray) (answersAt : List (List Ext × Ext) → List Ext) : Out :=
  closeW (m := Id) Fmt.formatHash S cfg root answersAt

/-- `commitW` over one oracle that is a function: every call of the hash is a question to O (two
under the number 162). -/
def commitO (O : ByteArray → ByteArray) (S : Shape) (files : List ByteArray) (T : Table) : Out :=
  commitW (m := Id) (Fmt.HM (m := Id) O) S files T

end Bind.Twin
