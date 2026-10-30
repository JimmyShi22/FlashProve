-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G9/FlatStep.lean: the verifier of a short sumcheck on plain lists.

The functions of this file read lists over a commutative ring K and no record of the library, so
they have code and can be run over a large field. That takeSc computes the fields of shortV and
shortVC (Cb/G6/Value.lean, Cb/G6/Core.lean) at the pick F₀ is not proved in this file.

Main names:
  Rounds K: plain data: for each round the scalars sent and the challenges drawn.
  Sc K: what a sumcheck leaves: eps; the challenges by round, that of the further variable Y last
    where there is one; the last value fin; the values shown.
  evalGo: the sum of c_t x^(t+1): a round's message holds the coefficients of the powers 1 to n,
    rising. The constant is left out.
  runVars: the rounds of the variables. Of each variable the function knows one number z, the sum of
    every power from 1 on over the variable's nodes: z for equality weights at z, and 0 for the
    further variable Y. The constant, which is left out, is the running claim less z times the sum
    of the message.
  takeSc: one sumcheck: the first round (a scalar and ε), with the start: that scalar plus ε times
    the target; the variables' rounds; the round of values if there is one; and the rounds that are
    left.

Limits: the functions read by headD and getD with defaults, so on data of another form they give
values and no error. Plain variables, where the linear coefficient is left out, are not covered.

-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.List.Defs

set_option autoImplicit false

namespace TwV

/-- What a sumcheck leaves: the coefficient, the challenges by round (the dummy's last, where there
is one), the last value, the shown values. -/
structure Sc (K : Type) where
  eps : K
  xs : List K
  fin : K
  vals : List K
  deriving Repr, DecidableEq

/-- plain data: for each round the scalars sent and the challenges drawn -/
abbrev Rounds (K : Type) : Type := List (List K × List K)

section
variable {K : Type} [CommRing K]

/-- Σ_t c_t x^(t+1) -/
def evalGo (x : K) : ℕ → List K → K
  | _, [] => 0
  | t, c :: cs => c * x ^ (t + 1) + evalGo x (t + 1) cs

/-- The rounds of the variables. σ: the claimed sum; z: the equality weight's point of each variable
(the dummy: 0: its functional is the value at 0). The constant, which is left out, is
σ − z (c₁ + .. + c_n). Returns the last value and the challenges. -/
def runVars : K → List K → Rounds K → K × List K
  | σ, z :: zs, r :: rs =>
    let x := r.2.headD 0
    let q := runVars ((σ - z * r.1.sum) + evalGo x 0 r.1) zs rs
    (q.1, x :: q.2)
  | σ, _, _ => (σ, [])

/-- One sumcheck: round 0, the variables' rounds, the round of values if there is one. Returns what
is left of the rounds. -/
def takeSc (rs : Rounds K) (tg : K) (zs : List K) (shown : Bool) : Sc K × Rounds K :=
  let r0 := rs.headD ([], [])
  let eps := r0.2.headD 0
  let q := runVars (r0.1.headD 0 + eps * tg) zs rs.tail
  (⟨eps, q.2, q.1, if shown then (rs.getD (1 + zs.length) ([], [])).1 else []⟩,
    rs.drop (1 + zs.length + if shown then 1 else 0))

end
end TwV
