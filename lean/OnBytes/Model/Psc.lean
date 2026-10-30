-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Psc.lean: the verifier's part in the masked sumcheck of the sub-proofs, and one layer
of a product tree.

The plan's rounds name the masked sumcheck PSC, and the protocol's pages call it zero-knowledge.
This file follows the verifier's steps and claims nothing about hiding.

It follows vf_sumcheck_psc.h, the routine roundIn of vf_sumcheck_receive.h and the end of
vf_subproof_engine.h of the C++ verifier, routine by routine. The weights of a variable and the
linear form of the hiding polynomial are those of OnBytes/Iop/Psc.lean, whose head describes the
protocol itself. Slot, mask row, hidden value, claim, dry run, plan, chain and strict reader are
explained in OnBytes/Model/Hide.lean, at Fork, Aff and SubM. What a sumcheck states (the form C, the
summand, eps, an end value), its slots and the rules that the types do not enforce are described at
Psc and pscRow. The conditions of this file that the C++ routines do not have are listed at
pscRound.

Main definitions: RoundForm.weight, Psc, pscBegin, pscRound, roundIn, pscEnds, Psc.rowForm, pscRow,
Level, levelIn, Level.handDown, layerObject.

What this file does not claim. No theorem is stated here; OnBytes/Model/HideLaws.lean has theorems
on Psc.rowForm and on the polynomial that a round completes. Soundness and zero knowledge are not
claimed here. This file does not test that eps is drawn after everything that C, the weights and the
summand depend on. That depends on the order in which the caller calls these routines.
-/
import OnBytes.Chain.Lists
import OnBytes.Iop.Psc
import OnBytes.Model.Hide

namespace OnBytes.Model

/-! ## The sumcheck -/

/-- How a round's polynomial is summed. z is read for eq2 and eq, degree for nodes and eq. Returns
none if the form does not admit the degree. (C++: internal-psc-degree.) -/
def RoundForm.weight (form : RoundForm) (z : E := zeroE) (degree : Nat := 0) :
    Option OnBytes.Psc.Weight :=
  if form.degreeOK degree then
    let d := roundValues form degree + 1
    some (if form.equality then OnBytes.Psc.Weight.equality z d else OnBytes.Psc.Weight.plain d)
  else none

/-- The state of a sumcheck in progress.

The prover's statement in a sumcheck: a sum equals a hidden value, which is given as an affine form
C (OnBytes/Model/Hide.lean). The summand is a polynomial in the values of some functions of the
summed variables (the comments call them maps). An end value is the value of such a map at the point
of challenges. The sumcheck runs on a hiding polynomial plus eps times the summand. The sum of the
hiding polynomial and the scalars of the rounds are sent without a mask; the mask entries of their
slots are the hiding polynomial's coefficients (Slots, below). The calls come in this order:
pscBegin; roundIn for each variable; pscEnds, if end values are sent (a round in one further
variable Y, whose challenge is beta); pscRow.

Each routine returns the new state of the sumcheck (Psc), and the caller must go on with that one.
The C++ routines change the state in place. The flags ended and rowMade are part of the returned
state, so they guard only a caller that does go on with it.

Slots. A sumcheck uses the entries of the mask row that have the numbers of its slots. First come
the coefficients of the hiding polynomial, by variable and then by degree, the last variable with
its constant. Then come the masks of the end values, so that an end value and its mask have the same
number. A coefficient of the hiding polynomial is the hidden value with 0 shown and the factor -1.
An end value has the factor beta.

Public numbers. The numbers of rounds, the degrees and the numbers of end values are arguments that
the caller gives. They decide which elements are received and which rounds are closed. The dry run
turns them into the description of the rounds, and the strict reader compares that description with
the plan's entries: names, kinds, numbers of draws and the bytes of each message. This file ties the
numbers to nothing else. Whoever starts the chain must make sure that the plan's entries are those
of the hashed parameter bytes. -/
structure Psc where
  /-- what the sum must equal -/
  start : Aff := {}
  /-- the public part of start (Fork.publicPart) -/
  target : E := zeroE
  /-- the factor of the summand -/
  eps : E := zeroE
  /-- the running claim: what the polynomial of the next round must sum to -/
  claim : E := zeroE
  /-- the sumcheck's first slot, which is also its first mask entry -/
  first : Nat := 0
  /-- how the variables so far are summed, in the order of the rounds -/
  vars : Array OnBytes.Psc.Weight := #[]
  /-- the challenges of the rounds so far, in the order of the rounds -/
  r : Array E := #[]
  /-- the round in the further variable has been run -/
  ended : Bool := false
  /-- the claim (the row, in the C++ source) has been made -/
  rowMade : Bool := false
  /-- start is set -/
  started : Bool := false
  deriving Inhabited

/-- The messages of the beginning: the sum of the hiding polynomial (mu below) is received, eps is
drawn, and the running claim starts from the public target. By the design any target that is fixed
before eps is drawn will do, since the claim of pscRow has the term eps P (target - start)
(Psc.rowForm); no theorem here says so. -/
def pscBeginAt (target : E) : SubM Psc := do
  let first ← SubM.takeSlots 1
  let mu ← SubM.readSum
  let eps ← SubM.answer .pscEpsilon
  pure { target, first, eps, claim := addE mu (mulE eps target) }

/-- Begins the sumcheck of a sum that must equal the form C. Every hidden value that C names must
have been shown. -/
def pscBegin (C : Aff) : SubM Psc := do
  let p ← pscBeginAt (← SubM.publicPart C)
  pure { p with start := C, started := true }

/-- True if w.fixedInv is the inverse of w.moment[w.fixed], and w.moment applied to psi (the sum of
w.moment[i] * psi[i]) is 1. w.moment[i] is what the weight gives as the sum of X^i
(OnBytes/Iop/Psc.lean). Both hold for Weight.plain, and for Weight.equality at every z
(Weight.atZero is the case z = 0). So they do not depend on a drawn z, and pscRound may require them
as a public condition. Another kind of weight would need its own argument. -/
def weightHeld (w : OnBytes.Psc.Weight) : Bool :=
  mulE (w.moment.getD w.fixed zeroE) w.fixedInv == oneE &&
  OnBytes.Psc.dot w.moment w.psi == oneE

/-- One round in a variable that is summed by w. Receives the coefficients of the round's polynomial
except the one that the equation w(q) = claim fixes, fills that one in, draws the challenge by draw,
and carries the claim on to q(challenge). Returns the challenge.

Conditions of this file that its C++ counterparts do not have. pscRound requires that the weight's
sizes fit and that weightHeld holds; in the C++ source the makers of a weight require this. pscRow
requires one challenge for each variable. levelIn requires that the order has mu elements, each
below mu, and that the point has the coordinates that are read. pscRound and pscEnds require that as
many elements were received as were asked for. -/
def pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) : SubM (E × Psc) := do
  SubM.must (w.fits && weightHeld w)
  let sent ← SubM.read (w.d - 1)
  SubM.must (sent.size + 1 == w.d)
  let q := w.complete sent.toList p.claim
  let r ← StateT.lift draw
  let _ ← SubM.takeSlots (w.d - 1)
  pure (r, { p with claim := OnBytes.Psc.polyAt q r, vars := p.vars.push w, r := p.r.push r })

/-- One round of the given form. z is read for the forms eq2 and eq, degree for nodes and eq.
Returns the challenge. The C++ routine also says which of two kinds of draw the form takes; on the
chain both are the same draw, so that has no counterpart here. (C++: internal-psc-order.) -/
def roundIn (form : RoundForm) (p : Psc) (z : E := zeroE) (degree : Nat := 0) :
    SubM (E × Psc) := do
  SubM.must (!p.ended)
  let w ← SubM.get (form.weight z degree)
  pscRound p w roundDraw

/-- Runs the round in the further variable Y, in which degreeInY scalars are sent, and draws beta.
Then receives the n end values as one message, after which the verifier draws nothing. Returns the
slot e of the first end value: SubM.shown (e + j) is what was sent, and Aff.slot (e + j) is the
hidden end value. beta is the last element of r. It is the factor of the end values' mask entries,
and it is drawn by the rule that never gives 0. That rule is the strict reader's: it is not tested
here, and in the dry run beta is 0. (C++: internal-psc-order.) -/
def pscEnds (p : Psc) (degreeInY n : Nat) : SubM (Nat × Psc) := do
  SubM.must (!p.ended && decide (1 ≤ degreeInY) && decide (1 ≤ n))
  let (beta, p) ← pscRound p (OnBytes.Psc.Weight.atZero (degreeInY + 1)) (trAnswerNotZero .pscY)
  let v ← SubM.read n
  SubM.must (v.size == n)
  SubM.empty .pscValues
  let e ← SubM.takeSlots n
  SubM.change (·.hideRun e v beta)
  pure (e, { p with ended := true })

/-- One step of addSlots: adds x times the hidden value under slot j and goes on to the next
slot. -/
def addSlot : Nat × Aff → E → Nat × Aff
  | (j, u), x => (j + 1, Aff.addMul u (Aff.slot j) x)

/-- The form a + sum_i form[i] * (the hidden value under slot first + i). -/
def addSlots (a : Aff) (first : Nat) (form : Array E) : Aff :=
  (form.foldl addSlot (first, a)).2

/-- The value of the hiding polynomial at the challenges as a linear form in its coefficients, and
the product P over the variables of psi at the challenge, where psi is the variable's polynomial
with sum 1. -/
def Psc.walk (p : Psc) : List E × E := OnBytes.Psc.hidingWalk (zipT p.vars.toList p.r.toList)

/-- The form of the claim that a sumcheck leaves:
  <form(challenges), hiding coefficients> + eps P (target - start) + eps kept - (claim - eps S0).
form and P are those of Psc.walk. -/
def Psc.rowForm (p : Psc) (S0 : E) (kept : Aff) : Aff :=
  let u := Aff.ofConst (subE zeroE (subE p.claim (mulE p.eps S0)))
  let u := addSlots u p.first p.walk.1.toArray
  let u := Aff.addMul u (Aff.ofConst p.target - p.start) (mulE p.eps p.walk.2)
  Aff.addMul u kept p.eps

/-- The claim that a sumcheck leaves, as a form that must be 0 (Psc.rowForm). S0 is the summand at
the point of challenges on the shown end values, without its terms in maps whose values are not
shown. kept holds those terms: the sum of each one's coefficient times the map's value as a form.
The coefficients of the hiding polynomial are put under their slots here. (C++:
internal-psc-order.)

A round tests no equation (pscRound). The claim of pscRow is the one equation that is left of a
sumcheck's rounds. It is not tested here. The caller adds it with SubM.lin or t2Lin
(OnBytes/Model/Trees.lean), or builds it into the start of another sumcheck (hearTerms,
OnBytes/Model/Layer.lean), and the sum of the sub-proof's claims goes to the request's chain
(OnBytes/Model/Trees.lean). That an end value is the value of a certain map at the point of
challenges is a further claim, left to the caller. -/
def pscRow (p : Psc) (S0 : E) (kept : Aff := {}) : SubM (Aff × Psc) := do
  SubM.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size)
  SubM.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE))
  pure (p.rowForm S0 kept, { p with rowMade := true })

/-! ## One layer of a product tree -/

/-- One layer of a product tree, as it was received (ProductLevel in the C++ source). -/
structure Level where
  /-- the challenges of the layer's variables -/
  r : Array E := #[]
  /-- the slot of the left end value -/
  sL : Nat := 0
  /-- the slot of the right end value -/
  sR : Nat := 0
  /-- the point on the line between the two end values -/
  tau : E := zeroE
  /-- the claim that the layer's sumcheck leaves; the caller adds it with layerObject -/
  row : Aff := {}
  deriving Inhabited

/-- The rounds of a layer in the given order. Round number j runs in variable v = order[j]; its
coordinate of the equality point is rho[mu - 1 - v], and its challenge is stored at the same
place of r. -/
def levelRounds (mu : Nat) (rho : Array E) : List Nat → Array E → Psc → SubM (Array E × Psc)
  | [], r, p => pure (r, p)
  | v :: order, r, p => do
    SubM.must (decide (v < mu) && decide (mu - 1 - v < rho.size))
    let (x, p) ← roundIn .eq2 p (rho.getD (mu - 1 - v) zeroE)
    levelRounds mu rho order (r.set! (mu - 1 - v) x) p

/-- Runs one layer of a product tree with mu variables (readProductLevelRounds in the C++ source): a
sumcheck that starts from the form C, under the equality polynomial at rho. The summand is the
product of the two end values. -/
def levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) : SubM Level := do
  SubM.must (order.length == mu)
  let p ← pscBegin C
  let (r, p) ← levelRounds mu rho order (Array.replicate mu zeroE) p
  let (sL, p) ← pscEnds p 2 2
  let tau ← SubM.answer .line
  let (row, _) ← pscRow p (mulE (← SubM.shown sL) (← SubM.shown (sL + 1)))
  pure { r, sL, sR := sL + 1, tau, row }

/-- What a layer passes to the next one: the point (tau, r) and the form (1 - tau) vL + tau vR,
where vL and vR are the layer's hidden end values. -/
def Level.handDown (o : Level) : Array E × Aff :=
  (#[o.tau] ++ o.r,
    Aff.scale (Aff.slot o.sL) (subE oneE o.tau) + Aff.scale (Aff.slot o.sR) o.tau)

/-- Adds the claim of a layer (its object, in the C++ source). -/
def layerObject (o : Level) : SubM Unit := SubM.lin o.row

end OnBytes.Model
