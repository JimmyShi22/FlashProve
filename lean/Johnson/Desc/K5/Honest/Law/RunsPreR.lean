-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsPreR.lean: CONDITIONAL: THE FOUR RUNS' ONE PREMISE ON VALUES
(`preK5`, Johnson/Desc/K5/Honest/Law/RunsLaw.lean) FROM THE SENTENCE ON WHAT THE LOOKUP RETURNED
(`lookR`, Johnson/Desc/K5/Honest/Law/LookR.lean: one term at the plan's letters, on an attention
link's field g). One statement with its proof.

Main names:
  `valsTS_of_R`   **lookR at the field g; what the link's own rounds handed on is laid; the function
    of the points returns: then the premise holds**. OF g ARE SPENT `lookR` AND, IN THAT RETURN, ITS
    KEY POINTS; beside them stand the facts on the plan alone (`PlanR`, LookR.lean)

WHAT THE PREMISE READS OF THE STATE BESIDE g, AND IS NOT `lookR`'s: the field heard5 (laid), and the
ledger (the function of the points returns: its guards ask lengths of what was heard and of the key
points, and that the end values' slots of the link's sumchecks are filled). It reads nothing of the
smallness test's part.
Limits. `valsTS_of_R` IS CONDITIONAL on all four. zx and zy are free under K3Pts: no challenge's
value is asked after. Who lays `lookR`, who keeps it, and who hands the rest at a state, is not said
here. No theorem here says that any premise holds anywhere.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsPre
import Johnson.Desc.K5.Honest.Law.LookR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard UnitG UnitsAll K3Pts)
open OnBytes.Road.L5 (dimOf callsOf)

/-- **THE PREMISE, FROM THE SENTENCE ON g AND THE REST.** CONDITIONAL on: the facts on the plan;
`lookR` at the field g; heard5 is laid; the function of the points returns at the state's own parts.
-/
theorem valsTS_of_R (A : Attention.Plan) {r1 r2 u1 u2 wl ix wh : UnitG}
    (Q : PlanR A r1 r2 u1 u2 wl ix wh) {s : First.S} {a : First.AttOwn} {h : Heard}
    (hh : s.here = .att a) (hR : lookR A a.g) (h5 : a.heard5 = some h)
    (hp : ∀ gl, a.g = some gl → ∃ p, P.ptsFrom (P.parCOf A).geo gl.zk h a.F = some p) (n : Nat) :
    preK5 A n s := by
  obtain ⟨gl, hg, H3⟩ := hR
  obtain ⟨p, hp⟩ := hp gl hg
  exact valsTS_of_K3Pts A Q.units Q.norm Q.tiles Q.planes hh h5 hg H3
    (P.keyPts_of_k3 Q.calls H3).size (by rw [H3.nx]; exact Q.lmS) (by rw [H3.nx]; exact Q.tokens)
    hp n

end H2K5.Honest

#print axioms H2K5.Honest.valsTS_of_R
