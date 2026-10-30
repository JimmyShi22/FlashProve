-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Prod/Level.lean: the grand product, a part beneath the kinds of block: one level
of a product tree, the step down to the next level, and a run of levels. Plain definitions, all with
code; no theorem; nothing is evaluated in this file.

What it is for. Over 2^D leaves stands the tree of their products: a vertex of level m is the
product of its two children in level m + 1, whose indices differ in one new highest bit. The
verifier holds a claim on level m at a point z, as a form C on slots. `level` hears the rounds that
move the claim one level down and leaves one row; `stepDown` makes the next point and the next form;
`run` folds the two over several levels. A lookup calls `run` twice; a caller that needs a single
product of two maps calls `level` alone and drops xi.

A STAND-IN. `level` calls no text of the masked sumcheck's own file,
Johnson/Desc/Part/MaskedSum4.lean. `wholeStandIn` puts its four flat functions
(OnBytes/K/Kc/Flat.lean: pscBegin, roundIn, pscEnds, pscRow) in a row, for variables with
equality weights and three coefficients alone.

Limits. `level` and `run` TEST NOTHING OF THEIR ARGUMENTS: `argsOk` and `runOk` do, on public data,
and are meant for a block's planOk. Where these say false the functions still return: a coordinate
that is not there reads as 0, a bit named twice leaves another coordinate of r at 0. They refuse
just where the flat functions refuse. These test less of a round than the program's channel does
(the note at the end of Flat.lean): whoever makes the tape must test the rest. Against Flat.lean's
Fl.levelIn the row is made in front of the round LINE, not behind it, and r is laid back from the
list of challenges; no theorem says that the two give one result.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Prod
open OnBytes OnBytes.Model OnBytes.K.Kc

/-! ## The masked sumcheck, as this part calls it: a stand-in -/

/-- What a masked sumcheck that makes its row at once hands back. -/
structure Whole where
  /-- one for each variable, in the order of the rounds; then that of the further variable Y, last;
  the draw of the first round is not among them -/
  challenges : List E
  /-- the slot of the first end value; the others follow it -/
  sEnd : Nat
  /-- the form that must be 0 -/
  row : Aff

/-- A STAND-IN for the masked sumcheck's own text. C: the start form. zs: for each variable, in the
order of the rounds, the coordinate at which it is summed with the equality weights; each round's
polynomial has three coefficients. dY: the degree in Y. n: the number of end values. endTerm: from
what was shown under the n end slots to the summand's value. -/
def wholeStandIn (C : Aff) (zs : List E) (dY n : Nat) (endTerm : List E → E) : Fl Whole := do
  let p ← Fl.pscBegin C
  let p ← zs.foldlM (fun (p : Psc) z => do
    let x ← Fl.roundIn .eq2 p z
    pure x.2) p
  let (sEnd, p) ← Fl.pscEnds p dY n
  let ends ← (List.range n).mapM fun i => Fl.shown (sEnd + i)
  let (row, _) ← Fl.pscRow p (endTerm ends)
  pure { challenges := p.r.toList, sEnd := sEnd, row := row }

/-! ## A. One level -/

/-- What a level hands back. -/
structure LevelOut where
  /-- m coordinates, the highest bit first -/
  r : Array E
  /-- the slot of vL: the level below at (0, r) -/
  sL : Nat
  /-- the slot of vR: the level below at (1, r) -/
  sR : Nat
  /-- the draw of the round LINE -/
  xi : E
  /-- the level's one claim -/
  row : Aff

/-- The point r: the challenge of round l becomes the coordinate of the bit that round l fixes. -/
def layBack (m : Nat) (order : List Nat) (cs : List E) : Array E :=
  (order.zip cs).foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) (Array.replicate m zeroE)

/-- **One level.** m: the number of variables. z: a point of m coordinates, the highest bit first.
order: member l is the bit that round l fixes. C: the start form, on filled slots. It hears m + 4
rounds: the masked sumcheck's m + 3, then LINE. -/
def level (m : Nat) (z : Array E) (order : List Nat) (C : Aff) : Fl LevelOut := do
  let w ← wholeStandIn C (order.map fun b => z.getD (m - 1 - b) zeroE) 2 2
    fun v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)
  let r := layBack m order (w.challenges.take m)
  let xi ← Fl.answer .line
  pure { r := r, sL := w.sEnd, sR := w.sEnd + 1, xi := xi, row := w.row }

/-- The rounds of a level with m variables: name, scalars sent, elements drawn, how many of these
are never 0. -/
def levelShape (m : Nat) : List (String × Nat × Nat × Nat) :=
  [(RoundName.pscEpsilon.name, 1, 1, 0)] ++ List.replicate m (RoundName.pscRound.name, 2, 1, 0) ++
    [(RoundName.pscY.name, 2, 1, 1), (RoundName.pscValues.name, 2, 0, 0),
     (RoundName.line.name, 0, 1, 0)]

/-! ## B. The step down, and a run of levels -/

/-- **The step down**; no round. The next point: xi first, the coordinate of the new highest bit.
The next start form, on the two end slots. -/
def stepDown (o : LevelOut) : Array E × Aff :=
  (#[o.xi] ++ o.r, Aff.scale (Aff.slot o.sL) (subE oneE o.xi) + Aff.scale (Aff.slot o.sR) o.xi)

/-- What a run carries from level to level, beside the ledger and the rounds left. -/
structure Carried where
  /-- one row a level, in the levels' order; a caller may begin with rows of its own -/
  rows : Array Aff := #[]
  point : Array E := #[]
  form : Aff := Aff.ofConst zeroE

/-- One turn of the fold: the level with m variables, its row pushed, the step down. -/
def turn (order : List Nat) (s : Carried) (m : Nat) : Fl Carried := do
  let o ← level m s.point order s.form
  let x := stepDown o
  pure { rows := s.rows.push o.row, point := x.1, form := x.2 }

/-- **A run of n levels**, with m0, m0 + 1, … variables. orders: the order of the level with m
variables. s: the first point (m0 coordinates), the first form, the rows so far. Behind it the point
has m0 + n coordinates, and THE CALLER MUST CLOSE THE LAST FORM. -/
def run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) : Fl Carried :=
  (List.range n).foldlM (fun s i => turn (orders (m0 + i)) s (m0 + i)) s

/-! ## The tests on the arguments: public data; for planOk -/

/-- The order has m members, each below m, and each bit stands in it just once. -/
def orderOk (m : Nat) (order : List Nat) : Bool :=
  order.length == m && (order.all fun b => decide (b < m)) &&
    (List.range m).all fun b => order.count b == 1

/-- The four tests for one level; zLen: the number of the point's coordinates. -/
def argsOk (m zLen : Nat) (order : List Nat) : Bool := orderOk m order && zLen == m

/-- The same for a run: the first point's length, and every level's order. -/
def runOk (m0 n zLen : Nat) (orders : Nat → List Nat) : Bool :=
  zLen == m0 && (List.range n).all fun i => orderOk (m0 + i) (orders (m0 + i))

end VerifiableInference.Desc.First.Prod
