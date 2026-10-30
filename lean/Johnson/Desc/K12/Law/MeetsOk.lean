-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/MeetsOk.lean: what the library's law of a sending with samples asks of each
sampled message's shape at its radius, as a test that can run. Definitions with code alone; no
theorem; no Mathlib beneath it.

The law is `Johnson.Pack.sigOf_send` (Johnson/Pack/PortF.lean); what it asks is `MeetsAt`:
conditions on numbers alone.
Main names:
  `aOfB`, `distAtB`, `shapeD`: the logarithm of the positions (the larger of the two codes'); a
    code's distance as read at 2 ^ a positions; the shape's distance: the smaller of the distances
    of the codes of which it has rows (the greatest d that `PBase` allows).
  `meetsL cs s e`: the named clauses of `MeetsAt cs s e (shapeD cs s) L`, in its arm beyond unique
    decoding, L the library's `listMax n d e` (the Johnson bound, rounded down): both codes in order
    (four); one answer; a mask row or main rows over the extension field (`CaseE`), or no mask row
    and main rows over the base field (`CaseF`); the row that bears the pad is long enough; below
    the Johnson radius: n (n − d) < (n − e) ^ 2.
  `meetsOk cs l`: over a list of shapes with radii: a sending's sampled messages.
Limits: no theorem of this file ties the clauses to `MeetsAt`. No soundness is claimed, and nothing
is said on hiding.

-/
import OnBytes.Iop.Prox

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params

abbrev Clauses : Type := List (String × Bool)
def ok (l : Clauses) : Bool := l.all (·.2)

def mainB (cs : Codes) (s : OracleShape) : OnBytes.Code := cs.base.getD s.code default
def maskB (cs : Codes) (s : OracleShape) : OnBytes.Code := cs.mask.getD s.maskCode default
def aOfB (cs : Codes) (s : OracleShape) : Nat := max (mainB cs s).logN (maskB cs s).logN
def distAtB (c : OnBytes.Code) (a : Nat) : Nat := 2 ^ (a - c.logN) * (2 ^ c.logN - (c.r + c.ell) +
    1)

/-- The greatest d that the library's PBase allows. -/
def shapeD (cs : Codes) (s : OracleShape) : Nat :=
  if s.mainRows = 0 then (if s.maskRows = 0 then 0 else distAtB (maskB cs s) (aOfB cs s))
  else if s.maskRows = 0 then distAtB (mainB cs s) (aOfB cs s)
  else min (distAtB (mainB cs s) (aOfB cs s)) (distAtB (maskB cs s) (aOfB cs s))

def baseL (cs : Codes) (s : OracleShape) : Clauses :=
  [("meets.a1", decide ((mainB cs s).logN ≤ 32)),
   ("meets.k1", decide ((mainB cs s).r + (mainB cs s).ell ≤ 2 ^ (mainB cs s).logN)),
   ("meets.a2", decide ((maskB cs s).logN ≤ 32)),
   ("meets.k2", decide ((maskB cs s).r + (maskB cs s).ell ≤ 2 ^ (maskB cs s).logN))]

def meetsL (cs : Codes) (s : OracleShape) (e : Nat) : Clauses :=
  baseL cs s ++
  [("meets.answer", decide (s.answers = 1)),
   ("meets.case", decide ((0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1))),
   ("meets.pad", if 0 < s.maskRows then decide (1 ≤ (maskB cs s).ell)
      else decide ((if s.mainDeg = 3 then 1 else 3) ≤ (mainB cs s).ell)),
   ("meets.johnson", decide (2 ^ aOfB cs s * (2 ^ aOfB cs s - shapeD cs s) < (2 ^ aOfB cs s - e) ^
       2))]

def tagM (j : Nat) (l : Clauses) : Clauses := l.map fun x => (toString j ++ ":" ++ x.1, x.2)

def meetsWalk (cs : Codes) : Nat → List (OracleShape × Nat) → Clauses
  | _, [] => []
  | j, x :: rest => tagM j (meetsL cs x.1 x.2) ++ meetsWalk cs (j + 1) rest

def meetsOk (cs : Codes) (l : List (OracleShape × Nat)) : Bool := ok (meetsWalk cs 0 l)

end H2K.Pin
