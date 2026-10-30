-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Claim.lean (kind K9's, for every kind): DEFINITIONS WITH CODE; NO THEOREM: the one type
of a claim, which every kind's second half ("claims") hands to the batching draw, and how the
batching adds a claim to the one equation.

A claim says that an affine form is 0. The form speaks of the scalars that were sent under a mask
(by their slots) and of entries of committed arrays (by virtual row and column): single entries, and
runs of entries with written weights.
THE WEIGHT. The claims of a link are ONE ordered list. Claim number c gets chi^c, chi the batching
element. One exception, which the claim itself states: a tie or a read of the smallness test takes
a number like any claim, but its weight is chi^(n + first): n the number of claims in the plan,
first the number of its first equation. Its further equations' powers are weights inside its runs.

Main names:
  Claim: form; runs; eqFirst (none: the claim's own number; some first: n + first).
  addClaim F cl: the sub-proof's record with the claim added. addAll: a list of claims, in order.

A STAND-IN: the sums are kept in `verify-on-bytes`'s plain record Fork, and are
added by its own pure functions, by name: Fork.kap (the next number's weight; each number once),
Fork.push (the form), Fork.pushRuns (the runs). Their guards come with the calls: the door is not
shut; chi has been drawn; ONCE THE BATCHING DRAW HAS SET UP THE MARKS (kapMapF; before that Fork.kap
hands out chi^c for any c): the number is below the plan's and was not handed out; a form names an
entry that the arrays have and a slot below ns; a run fits its row and its weights.
`verify-on-bytes` reaches chi^(n + first) otherwise: it scales the claim's coefficients by
chi^(n - c + first) (HTailF2.leadF) and adds them under chi^c: the same element of the field;
leadF's own guard (numbers are left: c < n) is asked here too.

What is not claimed. That a kind's list of claims is what the protocol asks of it. Nothing on
soundness, on an honest prover or on hiding.


-/
import OnBytes.Model.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Model

/-- A claim: form + the runs = 0. -/
structure Claim where
  /-- the constant, the slots and the single entries -/
  form : Aff := {}
  /-- the runs of entries -/
  runs : Array Run2 := #[]
  /-- none: the weight is chi^(the claim's own number). some first: chi^(n + first). -/
  eqFirst : Option Nat := none
  deriving Inhabited

/-- The record with the claim added under its weight. The claim takes the next number. -/
def addClaim (F : Fork) (cl : Claim) : Option Fork :=
  F.kap.bind fun x =>
    let k : Option E :=
      match cl.eqFirst with
      | none => some x.1
      | some first =>
        if F.nClaim < F.planClaimsF then some (powE F.theta (F.planClaimsF + first)) else none
    k.bind fun k => (x.2.push k cl.form).bind (·.pushRuns k cl.runs)

/-- A list of claims, in order. -/
def addAll (F : Fork) (cls : List Claim) : Option Fork := cls.foldlM addClaim F

end VerifiableInference.Desc
