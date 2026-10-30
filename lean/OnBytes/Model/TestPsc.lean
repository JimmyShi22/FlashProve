-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestPsc.lean: tests of OnBytes/Model/Hide.lean, Psc.lean and Tsc.lean. They run when
this file compiles.

What is tested.
 1. Small values by hand: forms, the weights of claims, the one equation on the mask row.
 2. A token sumcheck and a layer of a product tree over four positions, with an honest prover that
    is written here from the descriptions in OnBytes/Iop/Psc.lean (its head) and
    OnBytes/Model/Psc.lean (at Psc): a hiding polynomial, the round polynomials, the further
    variable, masked end values. On its messages the one equation holds on the prover's mask row. If
    1 is added to any one scalar of the messages, the check still runs to its end and the equation
    does not hold. The two checks are written here as well (checkToken, checkLevel). Besides the
    sumcheck's claim they add claims that compare hidden values with the prover's true values, which
    a verifier is not given. The verifier's draws are the fixed ones of the structure Toy; no others
    are tried.
 3. The dry run of the token sumcheck goes through against the plan's six entries and notes 2, 2, 2,
    2, 2 and 0 elements.

No module of the program imports this file. It holds no theorem. The prover here is not the C++
prover. It follows the descriptions named in point 2, which are this library's own, so a misreading
of the protocol that the prover and the routines share would not be caught.
-/
import OnBytes.Model.Tsc

namespace OnBytes.Model.TestPsc

open OnBytes.Psc (polyAt dot)

/-- A small number as an element of the extension field. -/
def n (x : UInt64) : E := ofF x

/-! ## Small values -/

-- 2 (slot 3) + 5 - (slot 3) - 1, on the shown value 10
#guard ((({} : Fork).slots 4).hide 3 (n 10) oneE).bind
  (·.publicPart
    (Aff.addMul (Aff.ofConst (n 5)) (Aff.slot 3) (n 2) - Aff.slot 3 - Aff.ofConst (n 1)))
  == some (n 14)
-- a second value under one slot, a slot that does not exist, a slot that is still free
#guard ((((({} : Fork).slots 4).hide 3 (n 10) oneE).bind (·.hide 3 (n 10) oneE)).isNone)
#guard (((({} : Fork).slots 4).hide 4 (n 10) oneE).isNone)
#guard (((({} : Fork).slots 4).shown 3).isNone)

/-- A state with one array of one virtual row with three columns, four slots, and theta = 2. -/
def small : Fork :=
  { (({ trees := #[{ K := 3, R := 1, rows := #[{ coef := #[oneE] }] }] } : Fork).fillL.slots 4) with
    theta := n 2, thetaDrawnF := true, planClaimsF := 2, kapMapF := #[false, false] }

/-- The state after two claims: entry 1 + 3 (slot 0) + 7 = 0 and 5 (entry 1) + (entry 2) = 0. -/
def twoClaims : Option Fork :=
  (small.lin (Aff.addMul (Aff.ent 0 0 1 + Aff.ofConst (n 7)) (Aff.slot 0) (n 3))).bind
    (·.lin (Aff.scale (Aff.ent 0 0 1) (n 5) + Aff.ent 0 0 2))

#guard (twoClaims.map fun F => (F.trees.getD 0 {}).rows.map (·.L)) == some #[#[n 0, n 11, n 2]]
#guard (twoClaims.map (·.LS)) == some #[n 3, n 0, n 0, n 0]
#guard (twoClaims.map (·.c0)) == some (n 7)
#guard (twoClaims.map (·.kapAllTakenF)) == some true
-- a third claim is more than the plan has
#guard ((twoClaims.bind (·.lin {})).isNone)
-- an entry outside the row; a row that the array does not have
#guard ((small.lin (Aff.ent 0 0 3)).isNone)
#guard ((small.lin (Aff.ent 0 1 0)).isNone)
-- slot 0 has a coefficient and is still free
#guard ((twoClaims.bind (·.settle 0)).isNone)
-- slot 0 holds 10 - 4 (mask entry 0): the mask entry gets - 3 * 4, the constant 7 + 3 * 10
#guard ((twoClaims.bind (·.hide 0 (n 10) (n 4))).bind (·.settle 1)) ==
  some (#[subE zeroE (n 12), n 0, n 0, n 0], n 37)
-- a slot that the messages have taken is still free
#guard (((twoClaims.bind (·.hide 0 (n 10) (n 4))).bind (·.settle 2)).isNone)

/-! ## An honest prover over four positions -/

/-- The sum of two polynomials, given by their coefficients. -/
def addP : List E → List E → List E
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => addE x y :: addP a b

/-- k times a polynomial. -/
def scaleP (k : E) (a : List E) : List E := a.map (mulE k)

/-- The product of two polynomials. -/
def mulP : List E → List E → List E
  | [], _ => []
  | x :: a, b => addP (scaleP x b) (zeroE :: mulP a b)

/-- The polynomial of degree 1 with the value u0 at 0 and u1 at 1. -/
def lineOf (u0 u1 : E) : List E := [u0, subE u1 u0]

/-- The sum (1 - z) q(0) + z q(1) of a polynomial with at most three coefficients. -/
def eqSum (z : E) (q : List E) : E := dot (OnBytes.Psc.Weight.equality z 3).moment q

/-- The data of one test: the point, two maps on four positions (coordinate 0 of a position is the
top bit of its index), the mask row, and what the verifier will draw. -/
structure Toy where
  /-- the point of the equality polynomial -/
  P : Array E := #[E.mk3 3 1 4, E.mk3 1 5 9]
  /-- the first map -/
  a : Array E := #[E.mk3 2 6 5, E.mk3 3 5 8, E.mk3 9 7 9, E.mk3 3 2 3]
  /-- the second map -/
  b : Array E := #[E.mk3 8 4 6, E.mk3 2 6 4, E.mk3 3 3 8, E.mk3 3 2 7]
  /-- the mask row -/
  m : Array E := #[E.mk3 9 5 0, E.mk3 2 8 8, E.mk3 4 1 9, E.mk3 7 1 6, E.mk3 9 3 9, E.mk3 9 3 7,
    E.mk3 5 1 0, E.mk3 5 8 2, E.mk3 0 9 7, E.mk3 4 9 4]
  /-- the factor of the summand -/
  eps : E := E.mk3 4 5 9
  /-- the challenge of the first round -/
  r0 : E := E.mk3 2 3 0
  /-- the challenge of the second round -/
  r1 : E := E.mk3 7 8 1
  /-- the challenge of the round in the further variable -/
  beta : E := E.mk3 6 4 0
  /-- the point on the line between a layer's two end values -/
  tau : E := E.mk3 6 2 8
  /-- the element that batches the claims -/
  theta : E := E.mk3 6 2 0

/-- What the honest prover sends, and the true values. -/
structure Sent where
  /-- the true sum -/
  sum : E
  /-- the first map at the point of challenges -/
  aR : E
  /-- the second map at the point of challenges -/
  bR : E
  /-- the sum of the hiding polynomial -/
  mu : E
  /-- the messages of the three rounds, then the end values -/
  rounds : List (List E)

/-- The map f with its coordinate 0 set to x: a polynomial in coordinate 1. -/
def bindTop (f : Array E) (x : E) : List E :=
  let g (i : Nat) : E := f.getD i zeroE
  lineOf (polyAt (lineOf (g 0) (g 2)) x) (polyAt (lineOf (g 1) (g 3)) x)

/-- The honest prover of the sum over t of eq(P, t) a(t) b(t). first: the sumcheck's first slot.
gap: the public target minus the true sum. -/
def prove (t : Toy) (first : Nat) (gap : E) : Sent :=
  let g (f : Array E) (i : Nat) : E := f.getD i zeroE
  let m (i : Nat) : E := t.m.getD (first + i) zeroE
  let p0 := g t.P 0
  let p1 := g t.P 1
  -- the hiding polynomial w0(X0) + w1(X1) + wY(Y): its seven coefficients are the mask entries
  -- first .. first + 6
  let w0 := [zeroE, m 0, m 1]
  let w1 := [zeroE, m 2, m 3]
  let wY := [m 4, m 5, m 6]
  -- the verifier's running claim starts from the public target, not from the true sum: c makes up
  -- for the gap
  let c := mulE t.eps gap
  -- the summand, summed over coordinate 1, as a polynomial in coordinate 0
  let s0 := addP
    (scaleP (subE oneE p1) (mulP (lineOf (g t.a 0) (g t.a 2)) (lineOf (g t.b 0) (g t.b 2))))
    (scaleP p1 (mulP (lineOf (g t.a 1) (g t.a 3)) (lineOf (g t.b 1) (g t.b 3))))
  -- q0, q1, qY: the polynomials of the three rounds; the constant coefficient of each is not sent
  let q0 := addP (addP w0 [addE (addE (eqSum p1 w1) (m 4)) c]) (scaleP t.eps s0)
  let a1 := bindTop t.a t.r0
  let b1 := bindTop t.b t.r0
  let q1 := addP (addP w1 [addE (addE (polyAt w0 t.r0) (m 4)) c]) (scaleP t.eps (mulP a1 b1))
  let aR := polyAt a1 t.r1
  let bR := polyAt b1 t.r1
  -- in Y the two values become aR + m7 Y and bR + m8 Y
  let qY := addP (addP wY [addE (addE (polyAt w0 t.r0) (polyAt w1 t.r1)) c])
    (scaleP t.eps (mulP [aR, m 7] [bR, m 8]))
  { sum := eqSum p0 s0, aR, bR
    mu := addE (addE (eqSum p0 w0) (eqSum p1 w1)) (m 4)
    rounds := [q0.drop 1, q1.drop 1, qY.drop 1,
      [addE aR (mulE t.beta (m 7)), addE bR (mulE t.beta (m 8))]] }

/-- Adds 1 to scalar number k of the messages; changes nothing if there are fewer. -/
def bump : Nat → List (List E) → List (List E)
  | _, [] => []
  | k, r :: rs =>
    if k < r.length then r.set k (addE (r.getD k zeroE) oneE) :: rs else r :: bump (k - r.length) rs

/-- A round of a view: the prover's elements and the drawn elements. -/
def rv (sent drawn : List E) : Fmt.RoundView :=
  { vals := sent.map fun x => Fmt.ItemValue.e x.triple
    drawn := { elems := drawn.map E.triple, poss := [], trits := [], digest := none } }

/-- The rounds of a view, from the prover's messages and the verifier's. -/
def viewOf (msgs draws : List (List E)) : List Fmt.RoundView :=
  (msgs.zip draws).map fun (p : List E × List E) => rv p.1 p.2

/-- The value of the one equation on a mask row. -/
def valueOn (m : Array E) (x : Array E × E) : E :=
  (x.1.zip m).foldl (fun (s : E) (p : E × E) => addE s (mulE p.1 p.2)) x.2

/-- The plan's entries of a sumcheck with two rounds and two end values. head: the number of scalars
in the first message. msg is a message's length in bytes, 24 for each element. The names are those
of RoundName.name (OnBytes/Model/Rounds.lean), which are the names in the plan. -/
def entriesOf (head : Nat) : List Fmt.Entry :=
  [{ name := "PSC epsilon", msg := 24 * head, drawE := 1 },
   { name := "PSC round", msg := 48, drawE := 1 }, { name := "PSC round", msg := 48, drawE := 1 },
   { name := "PSC Y", msg := 48, drawE := 1, drawNZ := 1 }, { name := "PSC values", msg := 48 }]

/-- The plan's entry of the round that batches the given number of claims. -/
def batchEntry (rows : Nat) : Fmt.Entry := { name := "BAT-sigma", drawE := 1, rows := rows }

/-- Draws theta and sets up the marks kapMapF, as t2Batch in OnBytes/Model/Trees.lean does. (modify
writes the sub-proof's state, not the context of Blk.) -/
def batchNow : SubM Unit := do
  SubM.batchBy (← SubM.batchOpen)
  modify fun F => { F with kapMapF := Array.replicate F.planClaimsF false }

/-! ### The token sumcheck -/

/-- The check: a token sumcheck, its claim, and three claims that say what Cl and the two end
values are. -/
def checkToken (t : Toy) (x : Sent) : SubM (Array E × E) := do
  SubM.slots (tscSlots 2 2 2)
  SubM.setPlanClaims 4
  let o ← tscIn t.P 2 2 2
  let (row, _) ← pscRow o.p (mulE (← SubM.shown o.sEnd) (← SubM.shown (o.sEnd + 1)))
  batchNow
  SubM.lin row
  SubM.lin (Aff.slot o.sCl - Aff.ofConst x.sum)
  SubM.lin (Aff.slot o.sEnd - Aff.ofConst x.aR)
  SubM.lin (Aff.slot (o.sEnd + 1) - Aff.ofConst x.bR)
  SubM.batchRows 4
  SubM.allTaken
  SubM.must ((← SubM.slot) == 10)
  SubM.test (o.r == #[t.r0, t.r1])
  SubM.settle (← SubM.slot)

/-- The start of the walk and of the dry run. -/
def startToken : Start := { entries := entriesOf 2 ++ [batchEntry 4], st := {} }

/-- The value of the one equation if 1 is added to scalar number k of the honest messages; none if
the check stops before its end. k = 10 and more: no scalar is changed. -/
def runToken (k : Nat) : Option E :=
  let t : Toy := {}
  let x := prove t 1 (t.m.getD 0 zeroE)
  let msgs := bump k ([addE x.sum (t.m.getD 0 zeroE), x.mu] :: x.rounds)
  let draws := [[t.eps], [t.r0], [t.r1], [t.beta], [], [t.theta]]
  let view := viewOf (msgs ++ [[]]) draws
  match Blk.walk ((checkToken t x).run {}) startToken [] view with
  | some (y, []) => some (valueOn t.m y.1)
  | _ => none

-- the honest messages: the equation holds
#guard runToken 10 == some zeroE
-- 1 added to any one scalar: the check runs to its end and the equation fails
#guard (List.range 10).all fun k => (runToken k).any fun v => !isZeroE v

-- the dry run: six rounds, with 2, 2, 2, 2, 2 and 0 elements
#guard ((Blk.rounds ((checkToken {} (prove {} 1 zeroE)).run {}) startToken).map fun l =>
  l.map fun r => (r.1.entry.name, r.1.items.length)) ==
  some [("PSC epsilon", 2), ("PSC round", 2), ("PSC round", 2), ("PSC Y", 2), ("PSC values", 2),
    ("BAT-sigma", 0)]

/-! ### A layer of a product tree -/

/-- The check: one layer that starts from a public value, its claim, and the claim that the form
which it passes down has the right value. -/
def checkLevel (t : Toy) (x : Sent) : SubM (Array E × E) := do
  SubM.slots (layerSlots 2)
  SubM.setPlanClaims 2
  let o ← levelIn 2 t.P (Aff.ofConst x.sum) (orderDefault 2)
  batchNow
  layerObject o
  SubM.lin (o.handDown.2 -
    Aff.ofConst (addE (mulE (subE oneE t.tau) x.aR) (mulE t.tau x.bR)))
  SubM.batchRows 2
  SubM.allTaken
  SubM.must ((← SubM.slot) == 9)
  SubM.test (o.handDown.1 == #[t.tau, t.r0, t.r1])
  SubM.settle (← SubM.slot)

/-- The start of the walk. -/
def startLevel : Start :=
  { entries := entriesOf 1 ++ [{ name := "LINE", drawE := 1 }, batchEntry 2], st := {} }

/-- The value of the layer's one equation if 1 is added to scalar number k of the honest messages,
which hold nine scalars; none if the check stops before its end. k = 9 and more: no scalar is
changed. -/
def runLevel (k : Nat) : Option E :=
  let t : Toy := {}
  let x := prove t 0 zeroE
  let msgs := bump k ([x.mu] :: x.rounds)
  let draws := [[t.eps], [t.r0], [t.r1], [t.beta], [], [t.tau], [t.theta]]
  let view := viewOf (msgs ++ [[], []]) draws
  match Blk.walk ((checkLevel t x).run {}) startLevel [] view with
  | some (y, []) => some (valueOn t.m y.1)
  | _ => none

-- the honest messages: the equation holds
#guard runLevel 9 == some zeroE
-- 1 added to any one scalar: the check runs to its end and the equation fails
#guard (List.range 9).all fun k => (runLevel k).any fun v => !isZeroE v

end OnBytes.Model.TestPsc
