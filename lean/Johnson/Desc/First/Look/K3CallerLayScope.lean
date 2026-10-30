-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerLayScope.lean: WHAT IS ASKED OF THE PUBLIC DATA AT A LAYERS' LINK's
CALLS (LayOK, Johnson/Desc/First/Look/K3CallerLay.lean) HOLDS AT ALL PUBLIC FILES IN THE GOALS'
SCOPE,
at the place that lookAt makes. One theorem, which joins this folder's theorems with those of
Johnson/Goal/Meaning/LookScope.lean. NO SOUNDNESS IS CLAIMED.

Why. LayOK names the library's reference sizes and tables: so it is no law at every record that
Verify.publicOf returns (at a small example set publicOf returns and the field «sizes» fails). In
the
goals' scope four of its five fields are theorems at the record X.y.fo
(Johnson/Goal/Meaning/LookScope.lean); the place's record is X.y.fo, and
the kind's own parameters make it (Johnson/Desc/First/Look/K3CallerAtPlan.lean).

Main name: `layOK_scope`.

Limits. In the scope alone. One direction. Nothing on the guards of the caller's reading.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Goal.Meaning.LookScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **In the goals' scope LayOK holds at every layers' link's place.** -/
theorem layOK_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {i : ℕ} {x : Place}
    (e : lookAt X i false = some x) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) = 0) (set : Params.Setting) : LayOK set x := by
  obtain ⟨hp, -, -, e1, -⟩ := lookAt_lay e hn h0
  refine ⟨lay_shape set h e hn h0, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact Meaning.P34.look_eight hZ hR h
  · rw [e1]
    exact Meaning.P34.look_hot hZ hR h
  · intro c
    rw [e1]
    exact le_of_eq (Meaning.P34.look_sizes hZ hR h c).symm
  · intro c u hu
    rw [e1] at hu ⊢
    exact Meaning.P34.look_tabs hZ hR h c u hu

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.layOK_scope
