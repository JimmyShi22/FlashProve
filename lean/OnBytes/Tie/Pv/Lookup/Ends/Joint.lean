-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean: the two joint vectors of a lookup, the keys and the table, as
functions of a forest's numbers.

Definitions alone: the file states no theorem. They are over the record Forest.Shape of the Lean
verifier under OnBytes/ (OnBytes/Model/Forest.lean; here: the port) and over any commutative ring R.
Main names:
  `jointKey h kv θ X`: key number X of the joint key vector. X = x * 2^rK + y, where y is the
    tree's number and x the place in the tree. A tree y below NT belongs to the call c = callOf[y]:
    the key is call c's key number (y - first[c]) * 2^dT + x, moved by c times θ. A tree from NT on
    holds the value of call 0's padding row. An entry that callOf or first lacks is read as 0.
  `jointTab h θ u`: row u of the joint table. u = t * 2^cK + c: the row is row t mod 2^k of the
    call min c (NC - 1), where 2^k is the number of that call's rows, moved by that call's number
    times θ.
  `tauN`, `t0N`, `kN`: row t of call c's table as a number (the port's Call.tauAt), the number
    of the call's padding row, and the logarithm of the number of its rows; each is 0 where the
    shape has no call c.
  kv c i, call c's key number i, is an argument.
Limits: nothing is assumed, and all five definitions are computable. The file does not say that a
proof's keys are these, and it says nothing on a claim, a round or a message.

-/
import OnBytes.Model.Forest
import Mathlib.Algebra.Ring.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open OnBytes.Model

/-- Row t of call c's table, as a number; 0 if the shape has no call c. -/
def tauN (h : Forest.Shape) (c t : ℕ) : ℕ := ((h.calls[c]?).map fun k => (k.tauAt t).toNat).getD 0

/-- The row that call c's padding keys hold; 0 if the shape has no call c. -/
def t0N (h : Forest.Shape) (c : ℕ) : ℕ := ((h.calls[c]?).map fun k => k.t0).getD 0

/-- Call c's table has 2^(kN h c) rows; 0 if the shape has no call c. -/
def kN (h : Forest.Shape) (c : ℕ) : ℕ := ((h.calls[c]?).map fun k => k.k).getD 0

variable {R : Type} [CommRing R]

/-- **Key number X of the joint key vector.** -/
def jointKey (h : Forest.Shape) (kv : ℕ → ℕ → R) (θ : R) (X : ℕ) : R :=
  let y := X % 2 ^ h.rK
  let x := X / 2 ^ h.rK
  if y < h.NT then
    let c := h.callOf.getD y 0
    kv c ((y - h.first.getD c 0) * 2 ^ h.dT + x) + (c : R) * θ
  else (tauN h 0 (t0N h 0) : R)

/-- **Row u of the joint table.** -/
def jointTab (h : Forest.Shape) (θ : R) (u : ℕ) : R :=
  let c := min (u % 2 ^ h.cK) (h.NC - 1)
  (tauN h c (u / 2 ^ h.cK % 2 ^ kN h c) : R) + (c : R) * θ

end OnBytes.Ends

#print axioms OnBytes.Ends.tauN
#print axioms OnBytes.Ends.jointKey
#print axioms OnBytes.Ends.jointTab
