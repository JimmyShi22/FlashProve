-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/LiveCorollaries.lean: corollaries of `theLive_policy_free`
(Johnson/LPFPol/LiveAtPolicy.lean): an instance at the two named sets of public files, and the law
with an explicit range of policies in the place of "in scope".

The range: C < 2^32, theta ≤ C, cap ≤ 1024 and 2^8 ≤ theta.

Main names.
* `zGap_form`: the second named set (`VerifierAndGoals.zGap`, Ladder/Stored.lean) is the stored full-size
  example's three files with the parameter file written at the policy (25856, 512, 1).
* `live_gap_eq_full`: the test `protocolDataWellFormed` (Johnson/Goal/Description/Live.lean) gives one verdict at
  `zGap` and at `storedPublicFiles`. No premise: that both sets are in the goals' scope is a theorem
  (`VerifierAndGoals.inScope_full`, `VerifierAndGoals.inScope_gap`, Johnson/Goal/Files/ScopeExample.lean). So the
  premises of `theLive_policy_free` can be met.
* `theLive_in_range`: at files in scope, `protocolDataWellFormed` gives at every policy in the range the verdict
  that it gives at the files' own policy. By `inScope_withPol` (Johnson/LPFPol/ScopeAtPolicy.lean).
* `inScope_at_stored`: the stored full-size example's files with a policy in the range are in scope.
* `live_in_range_at_stored`: so a yes of `protocolDataWellFormed` at the stored files gives a yes at every policy
  in the range, at that example's layout file, scale file and five other free numbers.

Limits. The verdicts are equal. Which verdict it is, is not said here: that `protocolDataWellFormed` accepts at the
stored files (the term `VerifierAndGoals.storedPublicFiles`) is a premise of `live_in_range_at_stored`; the side library
proves it: `theLive_zFull` (AtFullSide/Top/LiveAtFull.lean), with that file's limits. A yes of
`protocolDataWellFormed` is no sign that the verifier accepts anything. Outside the range no set of these files is
in scope (`inScope_iff_range`), and nothing is said there. Which scale files and which values of the
five other free numbers are in scope is not said: Lean holds one scale file and one set of the five
in scope. Nothing where the scale file or one of the five other free numbers differs too. Nothing on
soundness, on an honest prover or on hiding.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.LiveAtPolicy
import Johnson.LPFPol.ScopeAtPolicy

set_option autoImplicit false

namespace LPFPol

open VerifierAndGoals FlashProve

/-- The second named set of files is of the form. -/
theorem zGap_form :
    zGap = at_ { storedLines with C := 25856, theta := 512, cap := 1 } storedPublicFiles.lay storedPublicFiles.KL := by
  unfold zGap at_
  rfl

/-- **One verdict at the two named sets of public files.** -/
theorem live_gap_eq_full : protocolDataWellFormed (asDescriptionFiles zGap) = protocolDataWellFormed (asDescriptionFiles storedPublicFiles) := by
  have h := theLive_policy_free storedLines 25856 512 1 storedPublicFiles.lay storedPublicFiles.KL
    (by rw [← zFull_form]; exact inScope_full) (by rw [← zGap_form]; exact inScope_gap)
  rw [← zGap_form, ← zFull_form] at h
  exact h

/-- **One verdict at every policy in the range**, at files in the goals' scope. -/
theorem theLive_in_range (v : FreeLines) (lay KL : ByteArray) (h0 : InScope (at_ v lay KL) = true)
    (C theta cap : Nat) (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    protocolDataWellFormed (asDescriptionFiles (at_ { v with C := C, theta := theta, cap := cap } lay KL)) =
      protocolDataWellFormed (asDescriptionFiles (at_ v lay KL)) :=
  theLive_policy_free v C theta cap lay KL h0 (inScope_withPol h0 h1 h2 h3 h4)

/-- **The stored full-size example's files with a policy in the range are in scope.** -/
theorem inScope_at_stored (C theta cap : Nat) (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    InScope (at_ { storedLines with C := C, theta := theta, cap := cap } storedPublicFiles.lay storedPublicFiles.KL) =
      true := by
  have h0 : InScope (at_ storedLines storedPublicFiles.lay storedPublicFiles.KL) = true := by
    rw [← zFull_form]
    exact inScope_full
  exact inScope_withPol h0 h1 h2 h3 h4

/-- **A yes at the stored files gives a yes at every policy in the range.** -/
theorem live_in_range_at_stored (live : protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true) (C theta cap : Nat)
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    protocolDataWellFormed (asDescriptionFiles
                     (at_ { storedLines with C := C, theta := theta, cap := cap } storedPublicFiles.lay storedPublicFiles.KL)) = true :=
  live_at_stored_scales live C theta cap (inScope_at_stored C theta cap h1 h2 h3 h4)

end LPFPol

#print axioms LPFPol.live_gap_eq_full
#print axioms LPFPol.theLive_in_range
#print axioms LPFPol.inScope_at_stored
#print axioms LPFPol.zGap_form
#print axioms LPFPol.live_in_range_at_stored
