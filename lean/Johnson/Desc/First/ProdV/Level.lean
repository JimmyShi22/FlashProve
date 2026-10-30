-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/ProdV/Level.lean: the part «grand product» (P2): one level of a product tree, the
step down, and a run of levels, as plain functions on a sub-proof's ledger and the rounds of a view.
Definitions with code; no theorem; nothing is evaluated in this file.

The masked sumcheck is no stand-in: a level calls the
part's own text (MaskedSum.whole). So a level CUTS THE ROUNDS ITSELF: the first m + 3 go to the
masked sumcheck, which is handed just its own; the next is LINE; the rest is handed back.
A level asks two things more of its m + 4 rounds, which a view can bear: no position and no
matrix entry is drawn in them (also asked by roundsFit, Johnson/Desc/Block.lean); the draw of the
further variable Y is not 0 (the strict reading's clause; on a view asked by nobody else).
It stands over the masked sumcheck
(Johnson/Desc/Part/MaskedSum4.lean): a call
is one record, with a lead, here 0; its rounds are declared and heard from that record.

Limits. It hears; it tests no equation: each level leaves one claim, a form that must be 0. IT LACKS
THREE GUARDS: A ROUND's NAME, HOW MANY OF ITS DRAWS THE PLAN MARKS
AS NEVER 0, AND AN ENTRY's COUNT OF ROWS. These are fields of the plan's entry: a view's round bears
none, and this text is handed no entry. They are the matter of whoever compares the rounds that
this part declares (levelEntries, runEntries) with the plan's; until the strict reading of a round
asks the rows, a kind that calls this part keeps a guard of its own on them. «Not 0» judges the
three words of the draw: it says that the element is not 0 where the words are below the prime,
which is asked of the whole view in front of all kinds. The tests on the arguments
(orderOk, argsOk, runOk) are not asked inside level or run: they are for the caller's test on the
plan. A wrong order that passes them gives other claims and no refusal. The last form of a run must
be closed by the caller.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.ProdV
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part

/-- A text that hears: from the ledger and the rounds still to come to its value, the ledger behind
and the rounds left; nothing where it refuses. -/
abbrev Hears (α : Type) : Type := Fork → List Fmt.RoundView → Option (α × Fork × List Fmt.RoundView)

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

/-- The level's variables, in the order of the rounds: each is summed with the equality weights at
its own coordinate of z; each round's polynomial has three coefficients. -/
def levelVars (m : Nat) (z : Array E) (order : List Nat) : List MaskedSum.Var :=
  order.map fun b => .point (z.getD (m - 1 - b) zeroE) 3

/-- The level's ends: degree 2 in the further variable; two end values. -/
def levelEnds : MaskedSum.Ends := ⟨2, 2⟩

/-- In these rounds elements alone are drawn: no position, no matrix entry. ALSO ASKED BY roundsFit.
-/
def elementsAlone (rs : List Fmt.RoundView) : Bool :=
  rs.all fun r => r.drawn.poss.isEmpty && r.drawn.trits.isEmpty

/-- **One level.** m: the number of variables. z: a point of m coordinates, the highest bit first.
order: member l is the bit that round l fixes. C: the start form, on filled slots. It takes m + 4
rounds: the masked sumcheck's m + 3, then LINE, in which nothing is sent and one element is
drawn. It refuses if a position or a matrix entry is drawn in one of them, or if Y's draw is 0. -/
def level (m : Nat) (z : Array E) (order : List Nat) (C : Aff) : Hears LevelOut := fun F rs =>
  if !elementsAlone (rs.take (m + 4)) then none else
  match MaskedSum.whole C { lead := 0, vs := levelVars m z order, ends := some levelEnds }
      (fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) F (rs.take (m + 3)),
    rs.drop (m + 3) with
  | some (h, row, G), line :: rest =>
    match MaskedSum.roundOf 0 1 line with
    | some (_, [xi]) =>
      if isZeroE (h.r.getLastD zeroE) then none else
      some ({ r := layBack m order (h.r.take m), sL := h.sEnd, sR := h.sEnd + 1, xi := xi,
              row := row }, G, rest)
    | _ => none
  | _, _ => none

/-- The rounds of a level with m variables, as entries of the plan, the work bits left 0. -/
def levelEntries (m : Nat) : List Fmt.Entry :=
  MaskedSum.entries
      { lead := 0, vs := List.replicate m (.point zeroE 3), ends := some levelEnds } ++
    [MaskedSum.entry "LINE" 0 1 0]

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
def turn (order : List Nat) (s : Carried) (m : Nat) : Hears Carried := fun F rs =>
  (level m s.point order s.form F rs).map fun x =>
    ({ rows := s.rows.push x.1.row, point := (stepDown x.1).1, form := (stepDown x.1).2 }, x.2)

/-- **A run of n levels**, with m0, m0 + 1, … variables. orders: the order of the level with m
variables. s: the first point (m0 coordinates), the first form, the rows so far. Behind it the point
has m0 + n coordinates, and THE CALLER MUST CLOSE THE LAST FORM. -/
def run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) : Hears Carried := fun F rs =>
  (List.range n).foldlM
    (fun (x : Carried × Fork × List Fmt.RoundView) i => turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2)
    (s, F, rs)

/-- The rounds of such a run, as entries of the plan. -/
def runEntries (m0 n : Nat) : List Fmt.Entry :=
  (List.range n).flatMap fun i => levelEntries (m0 + i)

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

end VerifiableInference.Desc.First.ProdV
