-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastKnown.lean: tests of the fast encoder (Johnson/Bind/TwinFast.lean) against the
plain one (Johnson/Bind/Twin.lean) at small shapes. Tests alone: each is a #guard, which Lean's
evaluator runs when the file is compiled; a #guard leaves no theorem.

1. At each shape of a list, at every place of every block: the fast encoder's column is the plain
   encoder's. The list has shapes whose polynomials fill the codeword's length, fill a part of it
   (several blocks from the same coefficients), have one coefficient, and a shape with one position.
2. The same at a table with words that are not below p.
3. The whole commitment at the fast encoder is that at the plain encoder.
4. Negative tests. At a shape whose polynomials are longer than its codewords the two part: the
   condition in `FastIsPlain` is needed. With the table of roots reversed, or one power of 7
   changed, they part.
5. Why the statement stops at 2^32 positions: a root's square is the root of half the order up to 32
   and not at 33; at 2^33 positions two positions share a point; at the shape (33, 2, 1, ..),
   position 2^32, the plain symbol is not the value that the fast encoder's steps would give. That
   value is written out here by hand: the fast encoder itself is not run there (its table of roots
   would have 2^32 entries).
Two expected values are written here by hand: the twelve shapes' spans (the second #guard) and the
value under 5. In every other test both sides are computed. The tables are TwinKnown.lean's
synthetic one (given by a formula in that file) and a second one that this file makes of it.
Limits. Finitely many cases. The proof of `FastIsPlain` is in Johnson/Bind/TwinFastProof.lean.

-/
import Johnson.Bind.TwinFast
import Johnson.Bind.TwinKnown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin
namespace FastKnown

open Fmt (hex)

/-- At every place of every block the columns made from P are the plain encoder's. -/
def sameAs (S : Shape) (T : Table) (P : Prepared) : Bool :=
  let rows := laid S T
  (List.range (2 ^ (S.a - S.span))).all fun B =>
    let table := blockAt S P B
    (List.range (2 ^ S.span)).all fun i =>
      fastColumn table i == columnOf S rows (B * 2 ^ S.span + i)

def same (S : Shape) (T : Table) : Bool := sameAs S T (prepare S T)

def shapes : List Shape :=
  [Known.shapeA, Known.shapeB, Known.shapeC, ⟨6, 8, 3, 1, 1, 40⟩, ⟨4, 13, 3, 1, 1, 40⟩,
    ⟨5, 20, 12, 2, 2, 40⟩, ⟨3, 1, 0, 0, 0, 40⟩, ⟨0, 1, 0, 1, 0, 40⟩, ⟨7, 5, 0, 1, 1, 40⟩,
    ⟨8, 100, 29, 0, 3, 40⟩, ⟨1, 1, 1, 1, 0, 40⟩, ⟨4, 2, 1, 0, 1, 40⟩]

#guard shapes.all fun S => decide (S.l + S.r ≤ 2 ^ S.a)
#guard shapes.map (·.span) == [4, 5, 6, 4, 4, 5, 0, 0, 3, 8, 1, 2]
#guard shapes.all fun S => same S Known.toy

/-- Every word raised by p where that fits a word. -/
def raised (f : Nat → Nat → UInt64) : Nat → Nat → UInt64 :=
  fun b q => if (f b q).toNat + Known.p < 2 ^ 64 then f b q + UInt64.ofNat Known.p else f b q

def high : Table :=
  { Known.toy with
    entry := raised Known.toy.entry, tail := raised Known.toy.tail, pad := raised Known.toy.pad }

#guard high.entry 0 0 != Known.toy.entry 0 0 && high.pad 0 0 != Known.toy.pad 0 0
#guard shapes.all fun S => same S high

#guard [Known.shapeA, Known.shapeB, Known.shapeC].all fun S =>
  let o := commit S Known.files Known.toy
  let o' := commitFast S Known.files Known.toy
  hex o.root == hex o'.root && hex o.id == hex o'.id &&
    Known.spell o.answers == Known.spell o'.answers

-- negative tests
#guard !same ⟨2, 8, 3, 1, 1, 40⟩ Known.toy
#guard !sameAs Known.shapeC Known.toy
  { prepare Known.shapeC Known.toy with roots := (rootsTable 5).reverse }
#guard !sameAs Known.shapeC Known.toy
  { prepare Known.shapeC Known.toy with sev := (sevens 6).setIfInBounds 2 7 }
#guard !sameAs ⟨6, 8, 3, 1, 1, 40⟩ Known.toy
  { prepare ⟨6, 8, 3, 1, 1, 40⟩ Known.toy with roots := (rootsTable 5).reverse }
#guard (prepare Known.shapeC Known.toy).roots == rootsTable 5 &&
  (prepare Known.shapeC Known.toy).sev == sevens 6

/-! ### Why the statement stops at 2^32 positions -/

-- up to 32 a root's square is the root of half the order; at 33 it is not: the library's root stays
#guard (List.range 32).all fun j =>
  Fmt.Fld.two.mul (Fmt.M1.rootOf2 (j + 1)) (Fmt.M1.rootOf2 (j + 1)) == Fmt.M1.rootOf2 j
#guard Fmt.M1.rootOf2 33 == Fmt.M1.rootOf2 32 &&
  Fmt.Fld.two.mul (Fmt.M1.rootOf2 33) (Fmt.M1.rootOf2 33) != Fmt.M1.rootOf2 32
-- so at 2^33 positions two positions share a point
#guard Fmt.M1.point 33 (2 ^ 32) == Fmt.M1.point 33 (2 ^ 31)
-- and the plain symbol at the position 2^32 of the shape (33, 2, 1, ..) is not what the fast
-- encoder's steps give there: c0 + z c1 + t c2 with t = 7^2 times the root of the block 2^30
#guard
  let z := Fmt.M1.point 33 (2 ^ 32)
  let t := Fmt.Fld.two.mul 49 (Fmt.M1.rootOf2 32)
  let f := Fmt.Fld.two
  let plain := Fmt.M1.symF ⟨33, 2, 1⟩ (2 ^ 32) [11, 17] [5]
  plain == f.add 5 (f.add (f.mul z 11) (f.mul (f.mul z z) 17)) &&
    plain != f.add 5 (f.add (f.mul z 11) (f.mul t 17))

end FastKnown
end Bind.Twin
