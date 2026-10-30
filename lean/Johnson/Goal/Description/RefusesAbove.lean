-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Description/RefusesAbove.lean: a control on the laws that carry the planner's return
along a change of the acceptance policy: at `storedPublicFiles`'s parameter file with (256, 257, 0) for C,
theta, cap the strict scan returns and the planner's public part does not.

Why. A law "where the planner returns at one policy, it returns at another" would hold idly of a
planner that did not read the policy. The laws in Johnson/LPFPol/ give conditions under which the
return is carried; they are not shown there to be necessary. Here one of them, theta ≤ C, is shown
to be forced by the planner's own text, and a file is shown at which it fails.

Main names.
* `publicOfO_theta`: where `publicOfO o` returns X, the scan's theta is at most its C. Beneath it
  `layout_theta`, `policy_theta`: the fourth line of `Head.policy` (OnBytes/Model/HeadLayout.lean).
* `publicOfO_refuses_of_theta`: so at a parameter file whose scan has theta above C it returns
  nothing.
* `scan_theta_above`: the strict scan returns on `policyFile` at the stored free numbers with (256,
  257, 0), with theta above C. By `LPFPol.scan_returns_withPol` (Johnson/LPFPol/ScanReturns.lean)
  and `scan_withPol` (Johnson/Goal/Meaning/ScopeScanTies.lean).
* `refuses_theta_above`: at that file `publicOfO o` returns nothing, whatever o, the scale file and
  the layout file.

Limits.
* That the planner returns at any file is not shown here. A planner that refused every file would
  meet `refuses_theta_above` too. So: where the planner returns at `storedPublicFiles`, it tells two policies
  apart.
* One of the conditions alone is tried. The file of the control is outside the goals' scope.
* Nothing on whether a policy is a good test of anything. Nothing on soundness.

-/
import Johnson.LPFPol.ScanReturns
import OnBytes.Flat.CoveredJoin
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Goal.Meaning.ScalesReturn
import Johnson.Goal.Files.ScopeExample
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open VerifiableInference.PlanWritten

/-- Where Head.policy passes, theta is at most C: its fourth line. -/
theorem policy_theta {h : Head.Shape} (k : Head.policy h = .ok ()) : h.theta ≤ h.clipC := by
  unfold Head.policy at k
  obtain ⟨_, _, k⟩ := exc_bind k
  obtain ⟨_, _, k⟩ := exc_bind k
  obtain ⟨_, _, k⟩ := exc_bind k
  obtain ⟨_, k4, _⟩ := exc_bind k
  have b : (!(decide (h.theta > h.clipC) || decide (h.cap > h.T) || decide (h.cap ≥ 2 ^ 16))) =
      true := OnBytes.Flat.needed_inv k4
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at b
  omega

/-- Where the head's layout returns, theta is at most C. -/
theorem layout_theta {h : Head.Shape} {t : Array F} {Ly : Head.HL}
    (k : Head.layout h t = .ok Ly) : h.theta ≤ h.clipC := by
  unfold Head.layout at k
  obtain ⟨_, _, k⟩ := exc_bind k
  obtain ⟨⟨⟩, hp, _⟩ := exc_bind k
  exact policy_theta hp

/-- **Where the public part returns, the scan's theta is at most its C.** -/
theorem publicOfO_theta {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    X.P.h.theta ≤ X.P.h.clipC := by
  have hP := publicOfO_scan h
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  have eP : X.P = P := Except.ok.inj (hP.symm.trans (polLayout_scan h0))
  rw [eP]
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  have h := Fo.Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨HLy, hL, _⟩ := exc_bind h
  exact layout_theta hL

/-- **A control: at a parameter file whose scan has theta above C the public part does not
return**, at any function in the second hash function's place. -/
theorem publicOfO_refuses_of_theta {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {P : PolScan} (hs : polScan pol = .ok P)
    (ht : P.h.clipC < P.h.theta) (X : Public) : publicOfO o pol KL layout ≠ .ok X := by
  intro h
  have e : X.P = P := Except.ok.inj ((publicOfO_scan h).symm.trans hs)
  have f := publicOfO_theta h
  rw [e] at f
  omega

/-- A control: the strict scan returns on a parameter file with theta above C. -/
theorem scan_theta_above :
    ∃ P, polScan (policyFile { storedLines with C := 256, theta := 257, cap := 0 }) = .ok P ∧
      P.h.clipC < P.h.theta := by
  obtain ⟨hZ, pp, hR, -⟩ := filesRead.full
  obtain ⟨P, hP, -⟩ := Meaning.Ret.shape_of_read hZ hR
  rw [pol_zFull] at hP
  obtain ⟨P', hP'⟩ := LPFPol.scan_returns_withPol hP (C := 256) (theta := 257) (cap := 0)
    (by decide) (by decide) (by decide)
  refine ⟨P', hP', ?_⟩
  rw [Lines.scan_withPol hP hP']
  show 256 < 257
  decide

/-- **A control: at that parameter file the public part does not return**, at any function in the
second hash function's place, any scale file and any layout file. -/
theorem refuses_theta_above (o : Nat → ByteArray → ByteArray) (KL : ByteArray)
    (layout : Option ByteArray) (X : Public) :
    publicOfO o (policyFile { storedLines with C := 256, theta := 257, cap := 0 }) KL layout ≠
      .ok X := by
  obtain ⟨P, hP, ht⟩ := scan_theta_above
  exact publicOfO_refuses_of_theta hP ht X

end FlashProve

#print axioms FlashProve.policy_theta
#print axioms FlashProve.layout_theta
#print axioms FlashProve.publicOfO_theta
#print axioms FlashProve.publicOfO_refuses_of_theta
#print axioms FlashProve.scan_theta_above
#print axioms FlashProve.refuses_theta_above
