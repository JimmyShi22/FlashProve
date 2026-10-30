-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookPlanesOwn.lean: the lookup's three claims that read the planes, with
the claim of the sumcheck over the leaves made in the description's own text.

What it is for: `planeClaimsF` (LookPlanes.lean) makes that claim by the flat function `Fl.pscRow`
and tests the planes' packing by `Forest.planeCols`, both by name. Here the three lines of the one
and the test of the other stand written out, each with what it asks.

Main names:
  `leavesRowOwn p S0 kept`: the claim that a finished sumcheck leaves, and its slots filled.
  `planeClaimsOwn`: the three claims.
That they are the texts that they replace: LookPlanesOwnAgrees.lean.

Limits: the ledger's `Fork.hideRun`, the record `Psc` with its plain functions `walk` and
`rowForm`, and the carrier `Fl` with `must` and `change` are the verifier program's and the
library's, by name. `hideRun` can refuse: a slot outside the ledger's room, or one that is filled
already. That it cannot refuse here is promised at the border in front (K3Borders.lean, `k3OnOut`),
not tested here. Nothing is said of soundness or of hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Desc.First.Look.ShapeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.K.Kc

/-- **The claim that a finished sumcheck leaves.** -/
def leavesRowOwn (p : Psc) (S0 : E) (kept : Aff) : Fl Aff := do
  -- the claim is made once, of a sumcheck that was begun and has a challenge for each variable
  Fl.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size)
  -- the coefficients of the hiding polynomial were never sent: their slots are filled with the
  -- shown value 0 and the factor -1, so that each stands for its mask entry alone
  Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE))
  pure (p.rowForm S0 kept)

/-- **The three claims that read the planes**: the leaves' sumcheck's claim; the bits' value at
the second point; the count of all keys that are no padding. -/
def planeClaimsOwn (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff) (pin : Nat → Fl Aff) :
    Fl (Array Aff) := do
  let h := g.shape
  Fl.must (planesOk h lm)
  let at0 ← planesAtF g lm 0 bit
  let at1 ← planesAtF g lm 1 bit
  let count ← (List.range (h.NC * 2 ^ (h.kT + 5 - lm))).foldlM
    (fun (f : Aff) col => do pure (f + (← pin col)))
    (Aff.ofConst (negE (ofF (2 ^ h.v - h.padding).toUInt64)))
  let leavesRow ← leavesRowOwn g.leaves oneE (Aff.scale at0 g.leavesA)
  pure #[leavesRow, Aff.slot g.sBit - at1, count]

end VerifiableInference.Desc.First.Look
