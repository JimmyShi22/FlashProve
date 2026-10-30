-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K4RowOfParts.lean: K4's one closed test `k4RowB` under the head, out of two named
parts.

What it is for. K4's law in the counted form stands on the head and one Bool, `k4RowB Zp`
(`k04_counted_of_last`, Johnson/Road/K4/K04Last.lean). This file cuts «the head gives that Bool»
into two sentences, and pays the rest from the library's laws on the goals' scope.

What it says. `k4Row_of_parts`: under the head, if
  hF   at the groups 0 and 1 the listing `frontB` accepts at the group's entry, and
  hL   at each of the twelve groups the arithmetic test `Pend.rowLightB` accepts at the group's
       entry,
then `k4RowB Zp = true`. That there are twelve groups, each with an entry, is
`Meaning.scope_plans` and `Meaning.scope_plans24`.

Limits. A joining: hF and hL are premises; no theorem HERE shows either (under the head they are
shown in Johnson/Road/K4/K4RowOfHead.lean). A member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/). K04_law is
not proved. Nothing on soundness.
-/
import Johnson.Road.K4.K4RowTestLaws
import Johnson.Goal.Meaning.PlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4.Total (frontB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **`k4RowB` under the head, out of its two parts.** -/
theorem k4Row_of_parts (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hF : ∀ g, g < 2 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
      frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo = true)
    (hL : ∀ g, g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
      Pend.rowLightB (P5J.At.X Zp).layers g hp.NCL Zp.first.lin = true) :
    k4RowB Zp = true := by
  obtain ⟨_, kN, _, _⟩ := Meaning.scope_plans hA.scope hA.reads hA.pubOne
  have hE := Meaning.scope_plans24 hA.scope hA.reads hA.pubOne
  show k4RowAt (P5J.At.X Zp) Zp.first.lin = true
  refine k4RowAt_iff.2 ⟨by rw [kN]; decide, fun g hg => ?_⟩
  rw [kN] at hg
  obtain ⟨hp, e⟩ := (hE g hg).1
  refine ⟨hp, e, fun h2 => hF g h2 hp e, ?_⟩
  rw [← Pend.rowLight_eq]
  exact hL g hg hp e

#print axioms OnBytes.Road.K4.k4Row_of_parts

end OnBytes.Road.K4
