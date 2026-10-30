-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlanLay.lean: IN THE GOALS' SCOPE, AT EVERY LAYERS' LINK (an even link
below 24): layAt AND tlAt ANSWER, AND WHAT layAt ANSWERS MEETS LayOK AND THE PROGRAM's TEST ON THE
PLANES' PACKING: the field "lay" of the structure K3Plan (K3Means.lean), to the letter.
Statements and proofs. A tie of public data: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: sentences on Verify.publicOf's value.
Used by K03PlanOf.lean (Johnson/Desc/First/Look/).
LETTERS: Z, pp, lay, X as in the scope's theorems; l: an even link below 24.

Main name: `layAt_scope`.

How it goes. Meaning.scope_plans (Johnson/Goal/Meaning/PlanShapes.lean): profile 4, twelve groups.
Meaning.plans_size (Johnson/Goal/Meaning/PlanNames.lean): a layers' plan for every group: so lookAt
answers. layOK_scope (K3CallerLayScope.lean): LayOK at lookAt's own place: its first field says that
the made record is the plan's: so layAt's copy is that place. lay_planes (K3CallerAtPlan.lean) has
the two bounds on lm; planes_toBool (K3CallerAttPublic.lean) makes the program's test of them.

Limits. The full size's scope alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerLayTests
import Johnson.Desc.First.Look.K3CallerLayScope
import Johnson.Desc.First.Look.K3CallerAttPublic
import Johnson.Goal.Meaning.PlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **In scope layAt and tlAt answer at every layers' link**, and what layAt answers meets LayOK and
the test on the planes' packing. -/
theorem layAt_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {l : ℕ} (hl : l < 24) (h0' : l % 2 = 0) :
    ∃ x tl, layAt X l = some x ∧ tlAt X l = some tl ∧ LayOK (Params.settingOf X.P.frame) x ∧
      (Forest.planeCols x.fs x.lm).toBool = true := by
  obtain ⟨hp4, hN, -, -⟩ := Meaning.scope_plans hZ hR h
  have hG : X.G.size = 12 := (Meaning.plans_size h).trans hN
  have hst : (if X.p4 then 2 else 1) = 2 := if_pos hp4
  have hg : X.G[l / 2]? = some X.G[l / 2] := Array.getElem?_eq_getElem (by omega)
  have hn : l ≠ (if X.p4 then 2 else 1) * X.NGr := by
    rw [hst, hN]
    omega
  have h0 : l % (if X.p4 then 2 else 1) = 0 := by
    rw [hst]
    exact h0'
  obtain ⟨x, e⟩ : ∃ x, lookAt X l false = some x := by
    unfold lookAt
    dsimp only
    rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hst, hg]
    exact ⟨_, rfl⟩
  have H := layOK_scope hZ hR h e hn h0 (Params.settingOf X.P.frame)
  obtain ⟨tl, ht, hpl⟩ := lay_planes h e hn h0
  obtain ⟨b5, bk, -⟩ := planesAtB_iff.1 hpl
  refine ⟨x, tl, ?_, ht, H, planes_toBool b5 bk⟩
  unfold layAt stepOf
  rw [if_pos (by
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨h0, hn⟩), e, Option.bind_some, H.shape, Option.map_some]

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.layAt_scope
