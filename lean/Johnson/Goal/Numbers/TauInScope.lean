-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/TauInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE APPROXIMATE RANGE
PROOF HAS 128 COMBINATIONS IN EVERY SUB-PROOF's PLAN: in what the verifier's own `publicOf` returns,
the field tau of the plan of each layers' group, of each attention group and of the output head is
128. Statements and proofs; nothing is evaluated at particular files.

How. The parameter file's line "tau 128" is one of the 86 fixed value lines of `policyFile v`
(`VerifierAndGoals.Lines.value_fixed`, Johnson/Goal/Meaning/ScopeLines.lean): so the scan's header has 128
(`hdr_tau`). Each of the three plans makes its value by `HTailF2.shapeF` from a blank with that tau,
which `shapeF` keeps (`shapeF_caps`, OnBytes/Model/Fit/ShapeFCaps.lean); what follows keeps it too.
  `hdr_tau`: in scope `X.P.h.tau = 128`.
  `shapeF_arg`: where `shapeF` returns, its argument tau is the blank's ("hid-tau").
  `planG_tau`: a layers' group's plan has the layout's shape's tau: `planG_shape`'s walk
    (OnBytes/Model/Fit/LayerTail.lean) once more, for the other field.
  **`tau_layers`**, **`tau_attention`**, **`tau_head`**: the three; **`tau_in_scope`**: together.

OBJECT: three fields of `Verify.Public`. USERS: Johnson/P5J/K8OwnSizesAt.lean ·
Johnson/K8Q14R/TauAt.lean; meant: "128 combinations" at the 25 places of kind K8 (`ProofFile.k8Par` lays
`tau := X.tl.tau`). LETTERS: Z, pp, lay, X: free.

Limits. Every statement has the premise that `publicOf` returns: that it does at any file in scope
is not said here. Nothing on the built links: that a link's tl is its plan's is another file's
(`IM.ground_tails`). Nothing on soundness.
-/
import Johnson.Goal.Meaning.PlanShapes
import OnBytes.Model.Fit.LayerTail
import OnBytes.Model.Fit.AttCaps
import OnBytes.Model.Fit.HeadWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Tau

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf layerShape)
open Fo.BatRows (bindE_ok addTreesF_keeps)

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- In scope the scan's header has 128 combinations. -/
theorem hdr_tau (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.P.h.tau = 128 := by
  have hX := OnBytes.Road.Hd.scan_of_public h
  rw [OnBytes.Road.Hd.policy_of_scope hZ hR] at hX
  rw [Model.ConfigReaders.polScan_h hX]
  exact VerifierAndGoals.Lines.value_fixed hX (p := ("tau", 128)) (by decide)

end

private theorem okJp {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- Where `shapeF` returns, its argument tau is the blank's. -/
theorem shapeF_arg {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') : tau = tl.tau := by
  unfold HTailF2.shapeF at h
  obtain ⟨h1, _⟩ := okJp h
  simpa using h1

/-- **A layers' group's plan has the layout's shape's number of combinations.** -/
theorem planG_tau {P : Layer.Pub} {g : Nat} {O : Option Layer.HPlan2} {hp : Layer.HPlan2}
    (h : Layer.planG P g O = .ok hp) : hp.tl.tau = P.y.h.tau := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k0 : tl.tau = P.y.h.tau := (shapeF_caps hS).2.2.2.trans (shapeF_arg hS).symm
  have k1 : tl1.tau = tl.tau := (addTreesF_keeps _ _ _ _ _ _ _ _ hA).2
  have k2 : (tl1.ownerIs g).tau = P.y.h.tau := k1.trans k0
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl : tl1.ownerIs g = y := Except.ok.inj hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k2
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := Except.ok.inj ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [← hy]
      exact (Fo.Pub.borderMeans_keeps hB).2.trans k2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **At every layers' group.** -/
theorem tau_layers (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} {hp : Layer.HPlan2} (hg : X.G[g]? = some hp) :
    hp.tl.tau = 128 := by
  have a : hp.tl.tau = X.y.h.tau := planG_tau (Fo.Pub.public_G h g hp hg)
  rw [a, (Meaning.scope_plans hZ hR h).2.2.1]
  exact hdr_tau hZ hR h

/-- **At every attention group.** -/
theorem tau_attention (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} {a : Attention.Plan} (hg : X.A[g]? = some a) :
    a.seam.tl.tau = 128 := by
  obtain ⟨sc, lines, cf, a0, _, _, _, hp, _, _, ht⟩ := Fo.Pub.public_A h g a hg
  obtain ⟨seam0, h0, h1, _⟩ := Fo.BatRows.planA_rows0 _ _ _ _ hp
  obtain ⟨_, k1⟩ := Fo.BatRows.seamPlan_keeps _ _ _ _ _ h1
  obtain ⟨f, hF⟩ := OnBytes.Model.Fit.seamShape_F h0
  rw [ht, k1, (shapeF_caps hF).2.2.2]
  exact hdr_tau hZ hR h

/-- **At the output head.** -/
theorem tau_head (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.H.tl.tau = 128 := by
  obtain ⟨⟨m, f, tl1, hsh, _, ht⟩, _⟩ := OnBytes.Model.Verify.head_walk h
  rw [ht, (shapeF_caps hsh).2.2.2]
  exact hdr_tau hZ hR h

/-- **In scope every sub-proof's plan has 128 combinations.** -/
theorem tau_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → hp.tl.tau = 128) ∧
      (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → a.seam.tl.tau = 128) ∧
      X.H.tl.tau = 128 :=
  ⟨fun _ _ hg => tau_layers hZ hR h hg, fun _ _ hg => tau_attention hZ hR h hg, tau_head hZ hR h⟩

end

end Meaning.Tau

#print axioms Meaning.Tau.hdr_tau
#print axioms Meaning.Tau.shapeF_arg
#print axioms Meaning.Tau.planG_tau
#print axioms Meaning.Tau.tau_layers
#print axioms Meaning.Tau.tau_attention
#print axioms Meaning.Tau.tau_head
#print axioms Meaning.Tau.tau_in_scope
