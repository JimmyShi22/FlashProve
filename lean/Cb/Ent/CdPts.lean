-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/CdPts.lean: the sizes of the codes of the entry's link, and the evaluation points of these
codes, in the field with p = 2^64 - 2^32 + 1 elements.

Definitions. No theorem is in this file.

Main names:
  `RsPar`: the sizes of a Reed-Solomon code: 2^a positions, l entries of a message, r random
    coefficients (the tail).
  `LkPar`: the sizes of the link: the stored tables' code T, the numbers of positions drawn for the
    two folds, the codes C and Z of a folded row's oracle message, the number R of its rows; with
    the numbers of digits aR, aP, aPhi and the entry t0 at which a folded row's tail begins.
  `gen7`, `rootW`, `expFrom`, `pt`: the point of the position x of a code of length 2^a is
    7 w^(expFrom x a 0), w a fixed element: bit j of x gives the exponent 2^(32 - (j + 1)).
  `GF`, `GE`: the library's `Cb.Gl.F` and its cubic extension `Cb.Gl.E`.

Limits: numbers and field elements alone: no machine words. That a program's points on machine words
are these is not said here. That w has order 2^32 and that the points are different: CdPoints.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlField
import Iop.InteractiveOracleProof

set_option autoImplicit false

namespace Cb.Ent

/-- The sizes of a code: words of length 2^a, messages of l entries, a random tail of r entries. -/
structure RsPar where
  a : ℕ
  l : ℕ
  r : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The sizes of the link: the stored tables' code T, the numbers of positions drawn for the two
folds, the codes of a folded row's oracle message and the number R of its rows. -/
structure LkPar where
  T : RsPar
  nu0 : ℕ
  nuj : ℕ
  C : RsPar
  Z : RsPar
  R : ℕ

/-- the digits of a row's number in a folded row's oracle message -/
def LkPar.aR (P : LkPar) : ℕ := Nat.clog 2 P.R
/-- the digits of a place in such a row -/
def LkPar.aP (P : LkPar) : ℕ := Nat.log2 P.C.l
/-- the digits of an entry of a stored table's row -/
def LkPar.aPhi (P : LkPar) : ℕ := Nat.clog 2 P.T.l

/-- The least multiple of 2^c that is at least l, c the least number with r ≤ 2^c. -/
def t0Of (l r : ℕ) : ℕ := (l + 2 ^ Nat.clog 2 r - 1) / 2 ^ Nat.clog 2 r * 2 ^ Nat.clog 2 r
/-- the entry of a folded row's oracle message at which the tail begins -/
def LkPar.t0 (P : LkPar) : ℕ := t0Of P.T.l P.T.r

/-- The factor of all points: the points of a code lie in the coset of 7. -/
def gen7 : Cb.Gl.F := ((7 : ℕ) : Cb.Gl.F)

/-- A root of unity of order 2^32 in the base field. -/
def rootW : Cb.Gl.F := ((16334397945464290598 : ℕ) : Cb.Gl.F)

/-- The exponent that the n bits of x from bit i on contribute: bit j gives 2^(32 - (j + 1)) if it
is set. -/
def expFrom (x : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i => (if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom x n (i + 1)

/-- The point of the position x in a code of length 2^a. -/
def pt (a x : ℕ) : Cb.Gl.F := gen7 * rootW ^ expFrom x a 0

end Cb.Ent

namespace Cb.Ent
open Iop Prob

/-- The field with p = 2^64 - 2^32 + 1 elements and its cubic extension (X^3 = 2), as the library's
theory has them. -/
abbrev GF : Type := Cb.Gl.F
/-- See `GF`. -/
abbrev GE : Type := Cb.Gl.E

end Cb.Ent
