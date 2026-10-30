-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFast.lean: a fast encoder for the committer that runs: the symbols of a row by a
transform, a block of positions at a time, instead of one evaluation of the row's polynomial for
each position. Definitions, and the statement that the fast encoder's columns are the plain
encoder's (`FastIsPlain`), which is proved in Johnson/Bind/TwinFastProof.lean.

The mathematics. Let w_j be the root of unity of order 2^j (`Fmt.M1.rootOf2 j`, for j up to 32), so
w_(j+1)^2 = w_j for j below 32, and w_1 = -1. The point of the position x is z_x = 7 times the
product of w_(i+1) over the set bits i of x (`Fmt.M1.point`). Squaring k times forgets the k lowest
bits of x: z_x^(2^k) = 7^(2^k) times the product of w_(i+1-k) over the set bits i ≥ k of x.
So on the 2^(k+1) positions x with x div 2^(k+1) = B the value z_x^(2^k) is t where bit k of x is 0
and -t where it is 1, with t = 7^(2^k) times the product of w_(i+2) over the set bits i of B
(`twiddle`). A polynomial lo(X) + X^(2^k) hi(X), with lo and hi of fewer than 2^k coefficients,
therefore has at these positions the values of lo + t hi (bit k is 0) and of lo - t hi (bit k is 1).
One step replaces the 2^(k+1) coefficients in place by these two halves (`butterflies`); the lower
half goes on with the block 2 B, the upper with 2 B + 1 (`spread`). After k + 1 steps each place
holds a polynomial with one coefficient: the value at its position. Positions come out in their own
order.

Blocks. A row's polynomial has r + l coefficients. With K (`Shape.span`) the least number with
r + l ≤ 2^K (and K ≤ a), the steps above K change nothing: each of the 2^(a-K) blocks of 2^K
positions starts from the same coefficients. So the committer can go block by block: it encodes all
rows at one block (`blockAt`), hashes that block's leaves with the same loop as the plain committer
(`leavesFromW`), and drops the block (`leavesBlocksW`). It holds 2^(K + v + 3) bytes of symbols at a
time, and each row's coefficients, made once (`prepare`).

The field's operations are the library's on machine words (OnBytes/Field/Word.lean), which are
proved equal to those of Fmt/FieldE.lean (OnBytes/Field/WordEq.lean, OnBytes/Field/MulEq.lean).
Symbols and coefficients are kept as bytes, 8 a word, lowest first.

Main definitions: `rootsTable`, `twiddle`, `butterflies`, `spread`, `coefficient`, `prepare`,
`blockAt`, `fastColumn`, `leavesBlocksW`, `fastW`, `commitFastW`, `FastIsPlain`.
Limits.
(1) `FastIsPlain` is a statement here. Its proof: Johnson/Bind/TwinFastProof.lean. Tests:
    Johnson/Bind/TwinFastKnown.lean. What it buys: Johnson/Bind/TwinFastLaws.lean.
(2) It speaks of shapes with a ≤ 32 and l + r ≤ 2^a alone. Where l + r exceeds 2^a the fast encoder
    drops coefficients. Above a = 32 the statement would be false: the library's `rootOf2 j` stays
    at the root of order 2^32 for j above 32, so its square is no longer `rootOf2 (j - 1)`, the
    points repeat, and at a position with bit 32 set the fast encoder's factor is not the point's
    power. (At the shape (33, 2, 1, 0, 0, 40), block 2^30, place 0: plain has 49 w^2 at the third
    coefficient, fast has 49 w, with w of order 2^32.)

-/
import Johnson.Bind.Twin
import OnBytes.Field.Word

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open OnBytes (addF subF mulF normF)

/-! ### The transform -/

/-- Entry B, for B below 2^n: the product of the roots of unity of order 2^(i + 2) over the set bits
i of B. -/
def rootsTable : Nat → Array UInt64
  | 0 => #[1]
  | i + 1 =>
    let t := rootsTable i
    t ++ t.map (mulF (Fmt.M1.rootOf2 (i + 2)))

/-- 7^(2^k), for k below n. -/
def sevens (n : Nat) : Array UInt64 := (Array.range n).map (Fmt.M1.sqN 7)

/-- z^(2^k) at the positions x with x div 2^(k + 1) = B whose bit k is 0. -/
def twiddle (roots sev : Array UInt64) (k B : Nat) : UInt64 :=
  mulF (sev.getD k 0) (roots.getD B 0)

/-- One step on one block: for the n places j, j + 1, .. below `half`, the entries lo at off + j and
hi at off + half + j become lo + t hi and lo - t hi. -/
def butterflies (t : UInt64) (off half : Nat) : Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, A => A
  | n + 1, j, A =>
    let lo := A.getD (off + j) 0
    let u := mulF t (A.getD (off + half + j) 0)
    butterflies t off half n (j + 1)
      ((A.setIfInBounds (off + j) (addF lo u)).setIfInBounds (off + half + j) (subF lo u))

/-- From the 2^k coefficients at off on to the values at the positions of the block B of 2^k
positions. -/
def spread (roots sev : Array UInt64) : Nat → Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, _, A => A
  | k + 1, B, off, A =>
    let A1 := butterflies (twiddle roots sev k B) off (2 ^ k) (2 ^ k) 0 A
    let A2 := spread roots sev k (2 * B) off A1
    spread roots sev k (2 * B + 1) (off + 2 ^ k) A2

/-! ### Rows as bytes -/

/-- The least K with l + r ≤ 2^K, and a if that is less. -/
def Shape.span (S : Shape) : Nat :=
  min S.a (if S.l + S.r ≤ 1 then 0 else Nat.log2 (S.l + S.r - 1) + 1)

/-- Coefficient j of the polynomial of the row b, below p: the tail, the plain entries, the pads;
0 from r + l on. -/
def coefficient (S : Shape) (T : Table) (b j : Nat) : UInt64 :=
  if j < S.r then normF (T.tail b j)
  else if j - S.r < S.plain then normF (T.entry b (j - S.r))
  else if j - S.r < S.l then normF (T.pad b (j - S.r - S.plain))
  else 0

/-- A word's 8 bytes, lowest first, behind B. -/
def pushWord (B : ByteArray) (w : UInt64) : ByteArray :=
  (((((((B.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push
    (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push
    (w >>> 48).toUInt8).push (w >>> 56).toUInt8

/-- The n words f j, f (j + 1), .. as bytes behind acc. -/
def packFrom (f : Nat → UInt64) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, j, acc => packFrom f n (j + 1) (pushWord acc (f j))

/-- The first n words of a string of bytes; 0 beyond its end. -/
def unpack (n : Nat) (bytes : ByteArray) : Array UInt64 :=
  (Array.range n).map fun j => Fmt.wordAt bytes (8 * j)

/-- What is made once for a table: the roots, the powers of 7, and each row's r + l coefficients as
bytes. -/
structure Prepared where
  roots : Array UInt64
  sev : Array UInt64
  rows : Array ByteArray

def prepare (S : Shape) (T : Table) : Prepared where
  roots := rootsTable (S.a - 1)
  sev := sevens S.a
  rows := (Array.range S.rows).map fun b =>
    packFrom (coefficient S T b) (S.r + S.l) 0 ByteArray.empty

/-- The symbols of one row at the 2^K positions of the block B, as bytes, from the row's
coefficients as bytes. -/
def blockRow (P : Prepared) (K B : Nat) (row : ByteArray) : ByteArray :=
  (spread P.roots P.sev K B 0 (unpack (2 ^ K) row)).foldl pushWord ByteArray.empty

/-- All rows' symbols at the block B. -/
def blockAt (S : Shape) (P : Prepared) (B : Nat) : Array ByteArray :=
  P.rows.map (blockRow P S.span B)

/-- The column at the place i of a block, read off the rows' bytes. -/
def fastColumn (table : Array ByteArray) (i : Nat) : List UInt64 :=
  table.toList.map fun row => Fmt.wordAt row (8 * i)

/-- **The statement: the fast encoder's columns are the plain encoder's**, at every shape with at
most 2^32 positions whose polynomials are no longer than its codewords, every table, every block and
every place in it. -/
def FastIsPlain : Prop :=
  ∀ (S : Shape) (T : Table), S.a ≤ 32 → S.l + S.r ≤ 2 ^ S.a →
    ∀ B i, B < 2 ^ (S.a - S.span) → i < 2 ^ S.span →
      fastColumn (blockAt S (prepare S T) B) i = columnOf S (laid S T) (B * 2 ^ S.span + i)

/-! ### The committer, block by block -/

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The leaves of the n blocks from the block B on, behind those that are there. Each block's table
is made once, read by that block's leaves, and dropped. -/
def leavesBlocksW (S : Shape) (start : Nat → ByteArray) (block : Nat → Array ByteArray)
    (salt : Nat → ByteArray) : Nat → Nat → Array ByteArray → m (Array ByteArray)
  | 0, _, acc => pure acc
  | n + 1, B, acc => do
    let table := block B
    let more ← leavesFromW h S start (fun x => fastColumn table (x - B * 2 ^ S.span)) salt
      (2 ^ S.span) (B * 2 ^ S.span) acc
    leavesBlocksW S start block salt n (B + 1) more

/-- The committer behind cfg, at the fast encoder: all leaves block by block, then as `coreW`: the
tree's depths, the name, the seeds, the answers, the ID. -/
def fastW (S : Shape) (cfg : ByteArray) (T : Table) : m Out :=
  let P := prepare S T
  do
    let leaves ← leavesBlocksW h S (fun _ => cfg) (blockAt S P) T.salt (2 ^ (S.a - S.span)) 0 #[]
    let root ← climbW h cfg S.a leaves
    closeW h S cfg root (answers S T)

/-- The committer at the fast encoder. -/
def commitFastW (S : Shape) (files : List ByteArray) (T : Table) : m Out := do
  let cfg ← Fmt.configDigestW h files
  fastW h S cfg T

end

/-- `commitFastW` at the format's own hash. -/
def commitFast (S : Shape) (files : List ByteArray) (T : Table) : Out :=
  commitFastW (m := Id) Fmt.formatHash S files T

end Bind.Twin
