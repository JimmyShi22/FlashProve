-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Tsc.lean: the verifier's part in the token sumcheck of the sub-proofs.

It follows verifier/src/vf_sumcheck_token.h of the C++ verifier, routine by routine.

The prover's statement: Cl is the sum over t below 2^lt of eq(P, t) s(t), where t runs over the
token positions of the request and lt is the base-2 logarithm of their number. Cl is only a name for
that sum. eq(P, .) is the equality polynomial at the point P, and s is a sum of products of maps of
t. The messages are: Cl, a hidden value that is sent outside a sumcheck; then the masked sumcheck
that starts from it (OnBytes/Model/Psc.lean), with two scalars a round. The caller then computes the
summand on the shown scalars (hearTerms, OnBytes/Model/Layer.lean, passes 0 instead) and makes the
claim with pscRow, whose docstring says what is left to the caller.

Slot, hidden value and claim are explained in OnBytes/Model/Hide.lean, at Fork and Aff.

Main definitions: Tsc, tscRounds, tscIn, tscSlots.

What this file does not claim. No theorem is stated here. Soundness and zero knowledge are not
claimed here.
-/
import OnBytes.Model.Psc

namespace OnBytes.Model

/-- The state of a token sumcheck in progress. -/
structure Tsc where
  /-- the slot of Cl -/
  sCl : Nat := 0
  /-- the slot of the first end value -/
  sEnd : Nat := 0
  /-- the challenges, coordinate 0 first -/
  r : Array E := #[]
  /-- the sumcheck -/
  p : Psc := {}
  /-- the one claim that the sumcheck leaves; the caller sets it -/
  rowU : Aff := {}
  deriving Inhabited

/-- One round for each coordinate in the list, in order. Appends the challenges to r. -/
def tscLoop : List E → Array E → Psc → SubM (Array E × Psc)
  | [], r, p => pure (r, p)
  | z :: zs, r, p => do
    let (x, p) ← roundIn .eq2 p z
    tscLoop zs (r.push x) p

/-- Cl, the beginning of the sumcheck, and its lt rounds under the first lt coordinates of P; for a
caller that goes on with further rounds of this sumcheck. P must have that many coordinates; the C++
source, which takes a pointer, has no such condition. -/
def tscRounds (P : Array E) (lt : Nat) : SubM Tsc := do
  SubM.must (decide (lt ≤ P.size))
  let sCl ← SubM.claimsIn 1
  let p ← pscBegin (Aff.slot sCl)
  let (r, p) ← tscLoop (P.toList.take lt) #[] p
  pure { sCl, r, p }

/-- The whole token sumcheck. shown: the number of end values. degreeInY: the degree of the summand
in the maps whose values are shown. -/
def tscIn (P : Array E) (lt shown degreeInY : Nat) : SubM Tsc := do
  let o ← tscRounds P lt
  let (sEnd, p) ← pscEnds o.p degreeInY shown
  pure { o with sEnd := sEnd, p := p }

/-- The number of slots that a token sumcheck takes: one for Cl, and those of the sumcheck. more:
the number of rounds that the caller runs after those over t. -/
def tscSlots (lt shown degreeInY : Nat) (more : Nat := 0) : Nat :=
  1 + sumcheckSlots .eq2 (lt + more) shown degreeInY

end OnBytes.Model
