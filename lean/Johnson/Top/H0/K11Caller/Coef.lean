-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Coef.lean: the coefficients of a claim on the weights on the cells of the
committed matrix, written once for every ring.

A claim on the weights (OnBytes/Model/Weights.lean) is linear in the cells of the committed matrix
W. At a point of the column bits its summand is the sum over the cells (row, col) of W of
    coef (row, col) * W (row, col).
This file writes coef in closed form, by bit and by index. It is not copied from the verifier's
functions wsEpsT, wsRowPart, wsGamma, wsGammaAdd and eqTab, which compute the same numbers by folds,
and it calls none of them.
The text is generic in a type K with 0, 1, +, - and *. At the verifier's own field type it has code
(coefE). At a field it is the summand of the typed record (Caller.lean in this folder). Nothing
that this file imports imports Mathlib.

    coef (row, col) = C(X) * gamma (row - off) * eq (X, col)   for a row of the claim's unit,
                      0                                        for every other row
    C(X)      the product over the unit's index groups of the factor's value on the group's column
              bits, times 1 - X b for each column bit b from ncb on, which no group takes
    gamma r   256^l times the product over the groups of the factor's value on the part of the index
              that is left to the rows. r is read in mixed radix: the first group's part is the
              lowest place, the number l of the digit the highest. A cell of W holds a digit to the
              base 256, not a weight.
    eq (X, c) the product over the column bits b of X b if bit b of c is 1, and of 1 - X b if not
X b is the coordinate of column bit b. A point rm has the highest column bit first:
X b = rm (lk - 1 - b).

Main definitions: prodTo, sumTo, eqIdx, Fac, facCols, colFac, facRows, gammaAt, coef; chainB, endOf,
unitOK; coefE.

Limits: definitions alone; nothing is proved here. That coef is what the verifier computes is
proved in Prog.lean in this folder. On hiding nothing.
-/
import OnBytes.Model.Pending

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes.Model (WsGrp WsUnit WsLay WsFac WsClaim)

section Generic
variable {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K]

/-- f 0 * f 1 * ... * f (n - 1). -/
def prodTo : Nat → (Nat → K) → K
  | 0, _ => 1
  | n + 1, f => prodTo n f * f n

/-- f 0 + f 1 + ... + f (n - 1). -/
def sumTo : Nat → (Nat → K) → K
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

/-- eq on one bit: p x + (1 - p) (1 - x). -/
def eq1 (p x : K) : K := p * x + (1 - p) * (1 - x)

/-- x for a bit that is 1, and 1 - x for a bit that is 0. -/
def pick (b : Bool) (x : K) : K := if b then x else 1 - x

/-- eq (X, idx) on t bits: X s is the coordinate of bit s of idx. 0 for an index of more than t
bits. -/
def eqIdx (t : Nat) (X : Nat → K) (idx : Nat) : K :=
  if idx < 2 ^ t then prodTo t fun s => pick (idx.testBit s) (X s) else 0

/-- 256, made of 1, + and *. -/
def c256 : K :=
  let two : K := 1 + 1
  let four := two * two
  let sixteen := four * four
  sixteen * sixteen

/-- A claim's factor for one index group, each list as a function of the index. Class 'E': HV hi,
and pt i, the coordinate of bit z - 1 - i of lo. Class 'A': AV idx. -/
structure Fac (K : Type) where
  /-- class 'E': one element for each value of hi -/
  HV : Nat → K
  /-- class 'E': one coordinate for each bit of lo, the highest bit first -/
  pt : Nat → K
  /-- class 'A': one element for each index -/
  AV : Nat → K

/-- The value of one factor on its group's column bits. The i-th taken bit (class 'E') and bit s of
the index (class 'A', taken) are the column bits cb0 + i and cb0 + s. -/
def facCols (g : WsGrp) (x : Fac K) (X : Nat → K) : K :=
  if g.cls == 'E' then prodTo g.t fun i => eq1 (x.pt (g.z - 1 - g.takenAt i)) (X (g.cb0 + i))
  else if g.aTaken then sumTo g.R fun idx => x.AV idx * eqIdx g.t (fun s => X (g.cb0 + s)) idx
  else 1

/-- The product of the groups' factors on their column bits. -/
def groupsCols : List WsGrp → List (Fac K) → (Nat → K) → K
  | g :: gs, x :: xs, X => facCols g x X * groupsCols gs xs X
  | _, _, _ => 1

/-- C(X): a claim's factor on the columns. -/
def colFac (lk : Nat) (u : WsUnit) (fs : List (Fac K)) (X : Nat → K) : K :=
  groupsCols u.g fs X * prodTo (lk - u.ncb) fun i => 1 - X (u.ncb + i)

/-- The bit of lo that is the s-th one not taken, the lowest first. -/
def untakenAt (g : WsGrp) (s : Nat) : Nat := if g.high then s else g.t + s

/-- The value of one factor at j, the part of the group's index that is left to the rows. Class
'E': j is hi 2^(z - t) + (the bits of lo that are not taken). -/
def facRows (g : WsGrp) (x : Fac K) (j : Nat) : K :=
  if g.cls == 'E' then
    x.HV (j / 2 ^ (g.z - g.t)) *
      prodTo (g.z - g.t) fun s =>
        pick ((j % 2 ^ (g.z - g.t)).testBit s) (x.pt (g.z - 1 - untakenAt g s))
  else if g.aTaken then 1
  else x.AV j

/-- The number of a row within the unit, read in mixed radix from the lowest place: the groups in
their order, then the number of the digit, which dig takes. -/
def gammaGo (dig : Nat → K) : List WsGrp → List (Fac K) → Nat → K
  | g :: gs, x :: xs, r => facRows g x (r % g.left) * gammaGo dig gs xs (r / g.left)
  | _, _, l => dig l

/-- 256^l for the number l of a digit below nlw, else 0. -/
def digit (nlw l : Nat) : K := if l < nlw then prodTo l fun _ => c256 else 0

/-- gamma r: a claim's coefficient on row r of its unit. -/
def gammaAt (u : WsUnit) (fs : List (Fac K)) (r : Nat) : K := gammaGo (digit u.nlw) u.g fs r

/-- A claim's coefficient on the cell (row, col) of W, at the coordinates X of the column bits.
ui: the claim's unit. fs: its factors. -/
def coef (lay : WsLay) (ui : Nat) (fs : List (Fac K)) (X : Nat → K) (row col : Nat) : K :=
  match lay.U[ui]? with
  | none => 0
  | some u =>
    if u.off ≤ row ∧ row < u.off + u.rows then
      colFac lay.lk u fs X * (gammaAt u fs (row - u.off) * eqIdx lay.lk X col)
    else 0

end Generic

/-! ### What is asked of a unit of the layout -/

/-- The groups take column bits side by side, from bit cb on. -/
def chainB : List WsGrp → Nat → Bool
  | [], _ => true
  | g :: gs, cb => g.cb0 == cb && chainB gs (cb + g.t)

/-- The column bit after the last group's. -/
def endOf : List WsGrp → Nat → Nat
  | [], cb => cb
  | g :: gs, cb => endOf gs (cb + g.t)

/-- A unit is in order: its groups take the column bits 0 to ncb - 1 side by side, ncb is at most
lk, and its rows lie within W. -/
def unitOK (lay : WsLay) (u : WsUnit) : Bool :=
  chainB u.g 0 && endOf u.g 0 == u.ncb && decide (u.ncb ≤ lay.lk) &&
    decide (u.off + u.rows ≤ lay.m0)

/-! ### At the verifier's own field type -/

section Plain
open OnBytes

/-- The verifier's five operations under the usual signs, in this namespace alone. -/
scoped instance : Zero E := ⟨zeroE⟩
scoped instance : One E := ⟨oneE⟩
scoped instance : Add E := ⟨addE⟩
scoped instance : Sub E := ⟨subE⟩
scoped instance : Mul E := ⟨mulE⟩

/-- The verifier's factor as functions of the index. An index beyond a list reads 0, as in the
verifier. -/
def Fac.ofWs (x : WsFac) : Fac E :=
  ⟨fun i => x.HV.getD i zeroE, fun i => x.pt.getD i zeroE, fun i => x.AV.getD i zeroE⟩

/-- The coordinate of column bit b, out of a point that has the highest column bit first. -/
def colX (lk : Nat) (rm : Array E) (b : Nat) : E := rm.getD (lk - 1 - b) zeroE

/-- The plain coefficient: the coefficient of claim c on the cell (row, col) of W at the merge's
point rm. With code. -/
def coefE (lay : WsLay) (c : WsClaim) (rm : Array E) (row col : Nat) : E :=
  coef lay c.ui (c.f.map Fac.ofWs) (colX lay.lk rm) row col

end Plain

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.coefE
