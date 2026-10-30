-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Hear.lean: an attention segment's own rounds: what the verifier does while it
hears, as one short text over OnBytes/Model's record of a sumcheck, in the carrier and with the
routines of OnBytes/K/Kc/Flat.lean. A yardstick for Att/K5AttentionKind.lean and a
seat's tool; no part of the kind.

In the order of the messages: give each waiting scalar the next number; run a masked sumcheck once
for each unit of a softmax-table call and six times more; take four batching elements and one point.
Nothing is compared and nothing is derived. All that it reads of the plan is the planner's record of
these rounds.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Flat
import OnBytes.Params.SubRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.Short
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Psc RoundForm)

/-- What is handed on of a masked sumcheck. -/
structure Sum where
  /-- the challenges of its variables' rounds -/
  r : Array E
  /-- the number of its first end value -/
  ends : Nat
  /-- its record: eps, beta, the running claim at the end, the start form -/
  p : Psc

/-- A masked sumcheck from a start form. rounds: for each variable the round's form and degree. -/
def sumcheck (rounds : List (RoundForm × Nat)) (dY n : Nat) (start : Aff) : Fl Sum := do
  let p ← Fl.pscBegin start
  let (r, p) ← rounds.foldlM (fun (x : Array E × Psc) d => do
    let y ← Fl.roundIn d.1 x.2 zeroE d.2
    pure (x.1.push y.1, y.2)) (#[], p)
  let (ends, p) ← Fl.pscEnds p dY n
  let (_, p) ← Fl.pscRow p zeroE
  pure { r, ends, p }

/-- A sumcheck of products of two maps: n variables, m pairs of maps. -/
def products (n m : Nat) (start : Aff) : Fl Sum := sumcheck (List.replicate n (.sum3, 0)) 2 (2 * m) start

/-- The form Σ_b w_b · (scalar number first + step · b + off), over n members. -/
def batched (n : Nat) (w : Array E) (first step off : Nat) : Aff :=
  (List.range n).foldl (fun a b => a.addMul (.slot (first + (step * b + off))) (w.getD b zeroE)) (.ofConst zeroE)

/-- What was heard. A field of type Nat: the number of the first of the scalars named. -/
structure Heard where
  /-- for each unit of a remainder-table call: its three values -/
  remainders : Array Nat
  /-- for each unit of a softmax-table call: its seven values; its sumcheck (query · key) -/
  scores : Array (Nat × Sum)
  /-- accumulator · denominator × output · denominator · the high parts of two remainders -/
  five : Nat
  /-- the index's bits -/
  bits : Nat
  /-- the two high parts at the second point -/
  two : Nat
  /-- denominator × output -/
  division : Sum
  /-- the powers of the element that joins accumulator and denominator -/
  gam : Array E
  /-- the value product below the diagonal, and on it -/
  values : Nat
  below : Sum
  on : Sum
  /-- tg · ti · tk · tbg · tbi -/
  point : Array E
  /-- each pair's row maximum -/
  maxima : Nat
  om : Array E
  /-- the score at the index -/
  atIndex : Sum
  om' : Array E
  /-- the key at the index -/
  key : Sum
  om'' : Array E
  /-- the index's cells are bits -/
  cells : Sum

/-- **What the verifier does while it hears.** -/
def hear (x : Params.AttentionRounds) : Fl Heard := do
  let (lgk, lt, NP) := (x.lgk, x.lt, x.pairs)
  let remainders ← (Array.range x.planeMessages).mapM fun _ => Fl.claimsIn 3
  let scores ← x.score.toArray.mapM fun (n, pieces) => do
    let seven ← Fl.claimsIn 7
    pure (seven, ← products n pieces (.slot (seven + 6)))
  let five ← Fl.claimsIn 5
  let bits ← Fl.claimsIn lt
  let two ← Fl.claimsIn 2
  let division ← products x.e NP (.slot (five + 1))
  let gam ← Fl.batch 2
  let values ← Fl.claimsIn 2
  let below ← products x.valueM NP (.slot values)
  let on ← products x.valueD NP (.slot (values + 1))
  let point ← Fl.point .zero (2 * lgk + 2 * lt + 4)
  let maxima ← Fl.claimsIn NP
  let om ← Fl.batch NP
  let atIndex ← products x.attained NP (batched NP om maxima 1 0)
  let om' ← Fl.batch NP
  let degrees := List.replicate lt 2 ++ List.replicate lgk (lt + 2) ++ List.replicate lt (lt + 1)
  let key ← sumcheck (degrees.map (.nodes, ·)) (lt + 1) (x.Lam + NP * lt) (batched NP om' atIndex.ends 2 1)
  let om'' ← Fl.batch NP
  let cells ← products x.bits NP (.ofConst zeroE)
  pure { remainders, scores, five, bits, two, division, gam, values, below, on, point, maxima, om, atIndex,
         om', key, om'', cells }

end VerifiableInference.Desc.First.Att.Short
