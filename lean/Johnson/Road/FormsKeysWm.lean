-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWm.lean: what a claim on the committed matrix of weights says, as a sum over
the matrix's entries.

A sub-proof of some layers ends with claims of this form (OnBytes/Model/Weights.lean): the weights
of a unit, each times a product of factors, one factor for each index group, sum to a hidden value.
The verifier never writes that sum: it settles each factor in two halves, one on the column bits of
the matrix W and one on its rows. This file writes the sum.

Only definitions.
 - Wm: the entries of W: row, column.
 - splitG: which part of a group's index goes to the columns and which to the rows.
 - colIn, rowIn, cellOf: the cell of W that holds digit q of the weight with given indices.
 - wgtOf: the weight: its digits to the base 256.
 - sumIdx, claimVal: the sum that a claim speaks of, with facAt (Johnson/Road/FormsKeysPan.lean) for
   what a factor weighs an index with.
 - bitsOf: the number of a column, as a point of zeros and ones in the order in which wsEpsT reads
   the coordinates.

What is not claimed. That the verifier's two halves multiply to facAt at the cell cellOf, and that
cellOf is the library's place of a weight's digit, is shown in other files. The program does not
import this file.
-/
import Johnson.Road.FormsKeysPan
import OnBytes.Model.Weights

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading WsGrp WsUnit WsLay WsFac WsClaim)

/-- The entries of the committed matrix of weights: row, column. -/
abbrev Wm (K : Type) := ℕ → ℕ → K

/-- The index v of a group, cut into the part that goes to the columns and the part that is left to
the rows. Class 'E', low: the lowest t bits; the rest. Class 'E', high: the highest t of the lowest
z bits; the bits above z, then the lowest z - t. Class 'A': the whole index to the columns if the
group is taken, else to the rows. -/
def splitG (g : WsGrp) (v : ℕ) : ℕ × ℕ :=
  if g.cls == 'E' then
    if g.high then
      (v / 2 ^ (g.z - g.t) % 2 ^ g.t, v / 2 ^ g.z * 2 ^ (g.z - g.t) + v % 2 ^ (g.z - g.t))
    else (v % 2 ^ g.t, v / 2 ^ g.t)
  else if g.aTaken then (v, 0)
  else (0, v)

/-- The column: each group's column part from the group's first column bit on. -/
def colIn : List (WsGrp × ℕ) → ℕ
  | [] => 0
  | (g, v) :: rest => (splitG g v).1 * 2 ^ g.cb0 + colIn rest

/-- The row within the unit, a number of mixed radix: the digit's number q is the most significant
place, then the groups in reversed order: the first group's row part is the least significant. -/
def rowIn : List (WsGrp × ℕ) → ℕ → ℕ
  | [], q => q
  | (g, v) :: rest, q => rowIn rest q * g.left + (splitG g v).2

/-- The cell of W that holds digit q of the weight of unit u with the indices idx, one for each
group: row, column. -/
def cellOf (u : WsUnit) (q : ℕ) (idx : List ℕ) : ℕ × ℕ :=
  (u.off + rowIn (u.g.zip idx) q, colIn (u.g.zip idx))

section Value

variable {K : Type} [Field K] (ρ : Reading K)

/-- The weight of unit u with the indices idx, read in W: its digits to the base 256. -/
def wgtOf (u : WsUnit) (W : Wm K) (idx : List ℕ) : K :=
  ∑ q ∈ range u.nlw, (256 : K) ^ q * W (cellOf u q idx).1 (cellOf u q idx).2

/-- The sum over all tuples of indices, one index below R for each group, of the product of what the
factors weigh the indices with, times F of the tuple. -/
def sumIdx : List (WsFac × WsGrp) → (List ℕ → K) → K
  | [], F => F []
  | (x, g) :: rest, F =>
    ∑ v ∈ range g.R, facAt ρ x g v * sumIdx rest fun idx => F (v :: idx)

/-- The sum that the claim c speaks of, in the matrix W: the weights of its unit, each times the
product of what the claim's factors weigh its indices with. 0 if the layout has no such unit. -/
def claimVal (lay : WsLay) (W : Wm K) (c : WsClaim) : K :=
  match lay.U[c.ui]? with
  | none => 0
  | some u => sumIdx ρ (c.f.zip u.g) (wgtOf u W)

end Value

/-- The number C of a column of a matrix with 2^lk columns, as a point of zeros and ones: coordinate
i is bit lk - 1 - i of C. -/
def bitsOf (lk C : ℕ) : Array E :=
  Array.ofFn (n := lk) fun i => if C.testBit (lk - 1 - i.val) then oneE else zeroE

end OnBytes.Road
