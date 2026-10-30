-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Files/ScopeAtPolicies.lean: a name for the public files `storedPublicFiles` (Ladder/Stored.lean)
with another acceptance policy (C, theta, cap), and that they are in the goals' scope exactly where
2 ^ 8 ≤ theta ≤ C < 2 ^ 32 and cap ≤ 1024.

Why. Johnson/Goal/Files/FilesReadProof.lean shows `VerifierAndGoals.InScope` at two sets of files, `storedPublicFiles` and
`zGap`, each by an evaluation in Lean's kernel. Johnson/LPFPol/ScopeAtPolicy.lean carries it to
every policy within the four bounds, at files written as a triple. Here the same is said at one
name, `zAt`, beside `storedPublicFiles` and `zGap`, for the statements that speak of files by name.

Main names.
* `zAt C theta cap`: `storedPublicFiles` with the parameter file `policyFile { storedLines with C, theta, cap
  }`. It is a term for three files. It is no proposition and no goal names it: this file states no
  goal. `zAt_lay`, `zAt_KL`, `zAt_pol`: its three fields. `zAt_form`: it is `LPFPol.at_` at these
  numbers. `zGap_eq`: `zGap` is `zAt 25856 512 1`.
* `inScope_zAt`: within the four bounds the files are in scope: a call of `LPFPol.inScope_at_stored`
  (Johnson/LPFPol/LiveCorollaries.lean). `inScope_zAt_iff`: and nowhere else: a call of
  `LPFPol.inScope_iff_range`.

Limits.
* The five other free numbers, the scale file and the layout file are `storedPublicFiles`'s.
* `storedPublicFiles` is a term written in Ladder/Stored.lean. No Lean ties it, or `zAt`'s parameter file, to a
  file in a folder of examples or to a file that a program writes, and the example's weights are
  synthetic (that file's head).
* "In scope" says that the goals speak of these files. It says nothing of any description or
  verifier: no goal is met by it. Nothing on whether a policy is a good test of anything. Nothing on
  soundness.

-/
import Johnson.LPFPol.LiveCorollaries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals
open OnBytes OnBytes.Model

/-- The public files `storedPublicFiles` with the acceptance policy (C, theta, cap). -/
def zAt (C theta cap : Nat) : PublicFiles :=
  { storedPublicFiles with pol := policyFile { storedLines with C := C, theta := theta, cap := cap } }

/- The next five are true by definition. Each is stated apart, with the named files unfolded first:
left to find them by itself, Lean compares whole files byte by byte and runs out of stack
(Johnson/Goal/Files/FilesReadProof.lean has the same note). -/

/-- Its layout file is `storedPublicFiles`'s. -/
theorem zAt_lay (C theta cap : Nat) : (zAt C theta cap).lay = storedPublicFiles.lay := by
  unfold zAt
  dsimp only

/-- Its scale file is `storedPublicFiles`'s. -/
theorem zAt_KL (C theta cap : Nat) : (zAt C theta cap).KL = storedPublicFiles.KL := by
  unfold zAt
  dsimp only

/-- Its parameter file is `policyFile` at the stored free numbers with C, theta, cap. -/
theorem zAt_pol (C theta cap : Nat) : (zAt C theta cap).pol =
    policyFile { storedLines with C := C, theta := theta, cap := cap } := by
  unfold zAt
  dsimp only

/-- It is the triple of which the laws on a change of policy speak. -/
theorem zAt_form (C theta cap : Nat) : zAt C theta cap =
    LPFPol.at_ { storedLines with C := C, theta := theta, cap := cap } storedPublicFiles.lay storedPublicFiles.KL := by
  unfold zAt LPFPol.at_
  rfl

/-- The second named set of files is one of these. -/
theorem zGap_eq : zGap = zAt 25856 512 1 := by
  unfold zGap zAt
  rfl

/- The named files stay folded from here on. -/
attribute [local irreducible] storedPublicFiles zAt

/-- **The files `zAt C theta cap` are in the goals' scope, for every policy with
2 ^ 8 ≤ theta ≤ C < 2 ^ 32 and cap ≤ 1024.** -/
theorem inScope_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) : InScope (zAt C theta cap) = true := by
  rw [zAt_form]
  exact LPFPol.inScope_at_stored C theta cap h1 h2 h3 h4

/-- **The files `zAt C theta cap` are in scope exactly within the four bounds.** -/
theorem inScope_zAt_iff {C theta cap : Nat} :
    InScope (zAt C theta cap) = true ↔ C < 2 ^ 32 ∧ theta ≤ C ∧ cap ≤ 1024 ∧ 2 ^ 8 ≤ theta := by
  have h0 : InScope ⟨policyFile storedLines, storedPublicFiles.lay, storedPublicFiles.KL⟩ = true := by
    have e := inScope_full
    rw [LPFPol.zFull_form] at e
    exact e
  rw [zAt_form]
  exact LPFPol.inScope_iff_range h0 C theta cap

end VerifierAndGoals

#print axioms VerifierAndGoals.zAt_lay
#print axioms VerifierAndGoals.zAt_KL
#print axioms VerifierAndGoals.zAt_pol
#print axioms VerifierAndGoals.zAt_form
#print axioms VerifierAndGoals.zGap_eq
#print axioms VerifierAndGoals.inScope_zAt
#print axioms VerifierAndGoals.inScope_zAt_iff
