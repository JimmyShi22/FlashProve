-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/LiveAtFiles.lean: `theLive_policy_free` (Johnson/LPFPol/LiveAtPolicy.lean) in the
words of the goals' own reader. A statement and its proof.
  `form_of_scope`: a set of public files in scope is `at_` at the free numbers that the reader read.
  **`theLive_same_of_scope`**: two sets of public files, both in scope and read, with one scale
      file, at which the reader read the same five numbers eps1, eps2, epsF, MF, KF: `protocolDataWellFormed` gives
      one verdict at both. (That both are read follows from scope, `read_of_scope`; the two
      premises name what was read.)
Limits. As LiveAtPolicy.lean's: which verdict it is, is not said; a yes of `protocolDataWellFormed` is no sign that
the verifier accepts anything. Nothing where the scale file or one of the five numbers differs.
Nothing on soundness.

-/
import Johnson.LPFPol.LiveAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 3000

namespace LPFPol
open VerifierAndGoals FlashProve

attribute [local irreducible] VerifierAndGoals.policyFile

/-- A set of public files in scope is `at_` at the free numbers that the reader read, the stored
layout file and its own scale file. -/
theorem form_of_scope {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : InScope Z = true)
    (hR : readFiles Z = .ok pp) :
    Z = at_ (freeLinesOf pp) storedPublicFiles.lay Z.KL := by
  unfold InScope at hZ
  rw [hR] at hZ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hZ
  obtain ⟨h1, h2, -⟩ := hZ
  obtain ⟨pol, lay, KL⟩ := Z
  dsimp only at h1 h2
  unfold at_
  rw [← h1, ← h2]

/-- **One verdict at two sets in scope** with one scale file and the same five numbers eps1, eps2,
epsF, MF, KF. -/
theorem theLive_same_of_scope {Z Z' : PublicFiles} {pp pp' : Inst.Model.ScalesAndPolicy} (hZ : InScope Z = true)
    (hZ' : InScope Z' = true) (hR : readFiles Z = .ok pp) (hR' : readFiles Z' = .ok pp')
    (hKL : Z'.KL = Z.KL) (e1 : (freeLinesOf pp').eps1 = (freeLinesOf pp).eps1)
    (e2 : (freeLinesOf pp').eps2 = (freeLinesOf pp).eps2)
    (e3 : (freeLinesOf pp').epsF = (freeLinesOf pp).epsF)
    (e4 : (freeLinesOf pp').MF = (freeLinesOf pp).MF)
    (e5 : (freeLinesOf pp').KF = (freeLinesOf pp).KF) :
    protocolDataWellFormed (asDescriptionFiles Z') = protocolDataWellFormed (asDescriptionFiles Z) := by
  have f := form_of_scope hZ hR
  have f' := form_of_scope hZ' hR'
  have ev : freeLinesOf pp' = { freeLinesOf pp with
      C := (freeLinesOf pp').C, theta := (freeLinesOf pp').theta, cap :=
          (freeLinesOf pp').cap } := by
    generalize freeLinesOf pp' = a at *
    generalize freeLinesOf pp = b at *
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := a
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := b
    dsimp only at e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    rfl
  rw [hKL, ev] at f'
  rw [f] at hZ
  rw [f'] at hZ'
  rw [f, f']
  exact theLive_policy_free _ _ _ _ _ _ hZ hZ'

end LPFPol

#print axioms LPFPol.form_of_scope
#print axioms LPFPol.theLive_same_of_scope
