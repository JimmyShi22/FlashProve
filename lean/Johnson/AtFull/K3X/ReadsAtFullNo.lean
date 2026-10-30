-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/ReadsAtFullNo.lean: A NEGATIVE TEST beside readsXB_zFull
(Johnson/AtFull/K3X/ReadsAtFull.lean): at the same public data with the last layers' plan dropped,
the comparison with code on the six hypotheses rejects. So it can fail next to the value at which it
accepts. A short law; nothing is evaluated.

  `readsXB_pop_no`: readsXB { X₀ with G := X₀.G.pop } = false, at whatever letter X₀ the public
    part's maker returns at the library's written copy of the full-size public files. Link 22 is the
    last layers' link: its plan is number 11 of twelve; without it the lookup has no place.

Limits. One bend alone, and the coarsest: a place that is not there; no value is bent at this level
(finer negative tests stand beside the closed facts at the makers). Under hsz, as the fact beside
it. Nothing on soundness.

-/
import Johnson.AtFull.K3X.ReadsAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Lots.K3 (readsXB readsXAt)
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Look (lookAt)

/-- **With the last layers' plan dropped the comparison rejects.** -/
theorem readsXB_pop_no (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : readsXB { X₀ with G := X₀.G.pop } = false := by
  obtain ⟨X₁, hX₁, hG, -, -, -, P, -⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX)
  have h4 : ({ X₁ with G := X₁.G.pop } : Public).p4 = true := P.p4
  have hN : ({ X₁ with G := X₁.G.pop } : Public).NGr = 12 := P.groups
  have hn : (X₁.G.pop)[11]? = none := Array.getElem?_eq_none (by simp [hG])
  have e : lookAt { X₁ with G := X₁.G.pop } 22 false = none := by
    simp [lookAt, h4, hN, hn]
  have h22 : readsXAt { X₁ with G := X₁.G.pop } 22 = false := by
    simp [readsXAt, e]
  unfold readsXB
  rw [List.all_eq_false]
  exact ⟨22, by simp, by simp [h22]⟩

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.readsXB_pop_no
