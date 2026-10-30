-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Fits.lean: what the merge's two own tests on a claim's sizes ask. Theorems
with their proofs. No block imports this file.

Main names:
  `facFits_iff`, `claimFits_iff`: each test (Johnson/Desc/First/Fork/MergeKind.lean) says yes
    exactly where a written statement on sizes holds.
  `facFits_eq`, `claimFits_eq`: yardsticks: at all arguments each test says what `verify-on-bytes`'s
    test says (OnBytes/Model/Weights.lean: WsFac.fits, wsClaimShape).

Limits. Statements on two tests alone. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Model (WsLay WsClaim WsFac WsGrp wsClaimShape)
open Johnson.Desc.First.ForkMerge (facFits claimFits)

/-- **What `facFits` asks.** -/
theorem facFits_iff (x : WsFac) (g : WsGrp) :
    facFits x g = true ↔
      (g.cls = 'E' ∧ x.HV.size = g.o ∧ x.pt.size = g.z ∧ x.AV.size = 0) ∨
      (g.cls ≠ 'E' ∧ x.AV.size = g.R ∧ x.HV.size = 0 ∧ x.pt.size = 0) := by
  unfold facFits
  by_cases h : g.cls = 'E'
  · simp [h, and_assoc]
  · simp [h, and_assoc]

/-- **What `claimFits` asks**: the layout has the claim's unit; as many factors as the unit has
groups; factor number i has the sizes of group number i. -/
theorem claimFits_iff (lay : WsLay) (c : WsClaim) :
    claimFits lay c = true ↔
      ∃ u, lay.U[c.ui]? = some u ∧ c.f.length = u.g.length ∧
        ∀ y ∈ c.f.zip u.g, facFits y.1 y.2 = true := by
  unfold claimFits
  cases h : lay.U[c.ui]? with
  | none => simp
  | some u => simp

/-- A yardstick: the factor's test says what `verify-on-bytes`'s says. -/
theorem facFits_eq (x : WsFac) (g : WsGrp) : facFits x g = x.fits g := by
  have e : ∀ a : Array OnBytes.E, a.isEmpty = (a.size == 0) := fun a => by
    cases h : a.size <;> simp [Array.isEmpty, h]
  unfold facFits WsFac.fits
  rw [e, e, e]

/-- A yardstick: the claim's test says yes just where `verify-on-bytes`'s `wsClaimShape`
returns. -/
theorem claimFits_eq (lay : WsLay) (c : WsClaim) :
    claimFits lay c = (wsClaimShape lay c).isOk := by
  unfold claimFits wsClaimShape
  cases h : lay.U[c.ui]? with
  | none => rfl
  | some u =>
    simp only [facFits_eq]
    by_cases hb : (c.f.length == u.g.length && (c.f.zip u.g).all fun y => y.1.fits y.2) = true
    · simp [hb, Except.isOk, Except.toBool, pure, Except.pure]
    · simp [hb, Except.isOk, Except.toBool, throw, throwThe, MonadExceptOf.throw]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.facFits_iff
#print axioms VerifiableInference.Desc.First.MergeLaw.claimFits_iff
#print axioms VerifiableInference.Desc.First.MergeLaw.facFits_eq
#print axioms VerifiableInference.Desc.First.MergeLaw.claimFits_eq
