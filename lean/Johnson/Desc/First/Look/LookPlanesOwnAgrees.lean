-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookPlanesOwnAgrees.lean: the yardstick for LookPlanesOwn.lean: the claims
that read the planes, in own text, are `planeClaimsF`'s (LookPlanes.lean). Theorems alone.

Main names: `leavesRowOwn_eq`, `planeClaimsOwn_eq`.

Limits: equations of functions on a ledger and a tape; nothing on what the claims say. No file of
the description imports this one.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.LookPlanesOwn
import Johnson.Desc.First.Look.ShapeOwnAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.K.Kc

/-- The own text of the leaves' claim is the flat function's, whatever follows: the record that
the flat function hands on beside the claim is read by nothing here. -/
theorem leavesRowOwn_eq {β : Type} (p : Psc) (S0 : E) (kept : Aff) (k : Aff → Fl β) :
    (leavesRowOwn p S0 kept >>= k) = (Fl.pscRow p S0 kept >>= fun x => k x.1) := by
  funext F t
  simp only [leavesRowOwn, Fl.pscRow, bind, Fl.andThen, Fl.must, Fl.change, pure, Fl.ret]
  by_cases hb : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true
  · simp only [hb, if_true]
    cases F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) <;> rfl
  · simp only [hb]
    rfl

/-- **The three claims in own text are `planeClaimsF`'s**, at every ledger and tape. -/
theorem planeClaimsOwn_eq (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) : planeClaimsOwn g lm bit pin = planeClaimsF g lm bit pin := by
  unfold planeClaimsOwn planeClaimsF
  simp only [planesOk_eq, leavesRowOwn_eq]

end VerifiableInference.Desc.First.Look
