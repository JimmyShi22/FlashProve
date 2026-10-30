-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlanLettersLay.lean: IN THE GOALS' SCOPE, AT A LAYERS' LINK: THE PLACE
THAT layAt ANSWERS IS THE PLACE THAT lookAt ANSWERS. layAt returns lookAt's place with its shape of
the lookup replaced by the shape that the place's calls fix; in scope the public parameters' own
shape IS that one (LayOK's field shape, by layOK_scope): so nothing is replaced. The layers' like of
the last clause of attAt_letters (Johnson/Desc/First/Look/K3PlanLetters.lean). On public data alone.
NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: sentences on Verify.publicOf's value.
Used by K3CallsOwedScope.lean (Johnson/Desc/Sound/MgAt/) · K03Due5.lean, K03LeftAt.lean
  (Johnson/P5J/) and 1 more.
LETTERS: Z, pp, lay, X as in the scope's theorems; g: a group below 12.

Main name: `layAt_letters`.

Limits. The full size's scope alone. The links below 24.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3PlanLay
import Johnson.Desc.First.Look.K3CallsAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **At a layers' link.** -/
theorem layAt_letters (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {x : Place}
    (e : layAt X (2 * g) = some x) : lookAt X (2 * g) false = some x ∧ x.link = 2 * g := by
  obtain ⟨hp4, hN, -, -⟩ := Meaning.scope_plans hZ hR h
  have hG : X.G.size = 12 := (Meaning.plans_size h).trans hN
  have hst : (if X.p4 then 2 else 1) = 2 := if_pos hp4
  have hgg : X.G[2 * g / 2]? = some X.G[2 * g / 2] := Array.getElem?_eq_getElem (by omega)
  have hn : 2 * g ≠ (if X.p4 then 2 else 1) * X.NGr := by
    rw [hst, hN]
    omega
  have h0 : 2 * g % (if X.p4 then 2 else 1) = 0 := by
    rw [hst]
    omega
  obtain ⟨x0, e0⟩ : ∃ x0, lookAt X (2 * g) false = some x0 := by
    unfold lookAt
    dsimp only
    rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hst, hgg]
    exact ⟨_, rfl⟩
  have H := layOK_scope hZ hR h e0 hn h0 (Params.settingOf X.P.frame)
  have e1 : layAt X (2 * g) = some x0 := by
    unfold layAt stepOf
    rw [if_pos (by
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      exact ⟨h0, hn⟩), e0, Option.bind_some, H.shape, Option.map_some]
  obtain rfl : x0 = x := Option.some.inj (e1.symm.trans e)
  exact ⟨e0, VerifiableInference.OnPublicFiles.lookAt_link e0⟩

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.layAt_letters
