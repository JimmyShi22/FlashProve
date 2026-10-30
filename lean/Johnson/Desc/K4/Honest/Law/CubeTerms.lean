-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeTerms.lean: seven definitions; no theorem.

What is here. The terms in which the laws on a sum over a cube (Johnson/Desc/K4/Honest/Cube.lean)
are stated.

A reading (`OnBytes.Model.Reading`) takes the program's elements, which are coded on machine words,
into a commutative ring K, and sums, differences and products with them. Every law on a VALUE of the
cube is an equation between readings, not between words.

  `sumOver q f`   the sum of f over the 2 ^ q.length numbers below that power, each bit with a pair
     of weights: the first pair of q belongs to bit 0; a bit 0 takes the pair's first member
  `sidesK`   the readings of a variable's two weights
  `partK ρ c rs`   the partial sum behind the challenges rs
  `maskedEnds ends masks y`   each end value plus y times its mask entry
  `PolyOn d F`   read in the library's extension field, F is a polynomial function of degree at most
     d
  `ReadsAlike f`   on two lists that read alike, member by member, f's values read alike
  `wayLen`   of a way of summing: nothing, or the number of the point's coordinates

Limits. `partK` is made of the program's own `Cube.bound`: it is the weighted sum, over the entries
of the tables AS THE PROGRAM HAS BOUND THEM, of the summand on these entries. Nothing in this file
says that these tables are the first tables' multilinear extensions at the challenges. `PolyOn`
speaks of the library's extension field alone. `maskedEnds` is a text of arithmetic on two lists: it
is the term that `polyInY` (Johnson/Desc/K4/Honest/Cube.lean) hands to its function, with a letter y
for `polyInY`'s numbers 0, .., dY; nothing here says what the second list holds or whence it comes;
where the two lists differ in length the longer is cut.

Kin. Another kind has a partial sum of the same name for its own sum: `PairSum.partK`
(Johnson/Desc/K6/Honest/PairLaw.lean). Other files of the library have a `sumOver` of their own
(five, as far as its writers have searched): plain sums over a range, a list or an array, without
weights: other functions.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cube
import Johnson.Desc.Part.MaskedSumSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open Polynomial

/-- The sum of f over the numbers below 2 ^ q.length, each bit with a pair of weights. The first
pair belongs to bit 0. A bit 0 takes the pair's first member, a bit 1 the second. -/
def sumOver {K : Type} [CommRing K] : List (K × K) → (ℕ → K) → K
  | [], f => f 0
  | w :: q, f => w.1 * sumOver q (fun i => f (2 * i)) + w.2 * sumOver q (fun i => f (2 * i + 1))

/-- The readings of a variable's two weights. -/
def sidesK {K : Type} [CommRing K] (ρ : Reading K) (c : Cube) (v : ℕ) : K × K :=
  (ρ.val (sidesOf c v).1, ρ.val (sidesOf c v).2)

/-- **The partial sum behind the challenges rs**: the summand on the tables that the program has
bound at rs, summed over the variables that are left, each in the cube's way. -/
def partK {K : Type} [CommRing K] (ρ : Reading K) (c : Cube) (rs : List E) : K :=
  sumOver ((c.bound rs).1.reverse.map (sidesK ρ c))
    fun i => ρ.val (termsAt c.pairs (c.bound rs).2 i)

/-- Each end value plus y times its mask entry: what `polyInY` hands to its function. Where the two
lists differ in length the longer is cut. -/
def maskedEnds (ends masks : List E) (y : E) : List E :=
  (ends.zip masks).map fun x => addE x.1 (mulE y x.2)

/-- Read in the library's extension field, F is a polynomial function of degree at most d. -/
def PolyOn (d : ℕ) (F : E → E) : Prop :=
  ∃ P : Cb.Gl.E[X], P.natDegree ≤ d ∧ ∀ y, Reading.gl.val (F y) = P.eval (Reading.gl.val y)

/-- On two lists that read alike, member by member, f's values read alike. -/
def ReadsAlike (f : List E → E) : Prop :=
  ∀ a b : List E, a.map Reading.gl.val = b.map Reading.gl.val →
    Reading.gl.val (f a) = Reading.gl.val (f b)

/-- What `Cube.fits` reads of a way of summing: nothing, or the number of the point's coordinates.
-/
def wayLen : Way → Option ℕ
  | .plain => none
  | .point rho => some rho.size

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumOver
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sidesK
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.partK
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.maskedEnds
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.wayLen
