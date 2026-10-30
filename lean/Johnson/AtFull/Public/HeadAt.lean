-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/HeadAt.lean: THE TWO PREMISES ON THE HEAD's PLAN THAT hV_at AND armsB_at
(Johnson/AtFull/Public/AtWitnesses.lean) TAKE, at the closed plan HW of the model's head
(Johnson/AtFull/Head/PlanAtFull.lean), its ledger trimmed as the public part's maker trims it.

  `headB H`: one test on a head's plan: the view (LV, Johnson/AtFull/Made/DeclView.lean) of the link
    that listLinksH makes of it among twelve groups is viewsFull's last member; its own numbers at
    the written head's shape are ownH; the sizes of its smallness test are smallH
    (Johnson/AtFull/Rows/ArmsOfFields.lean).
  `head_walk`: [Lean's kernel] planH2 at the stand-ins returns, and headB accepts its value.
    `head_bent`: a negative test: with one scalar more the makers return and headB rejects.
  `head_W`: headB HW = true.
  **`hHV_at`**: hV_at's premise, at a public part X with twelve groups and X.H = HW trimmed.
  **`hHA_at`**: armsB_at's premise, at such an X whose head's shape is the written one and whose
    head's layout has the nineteen written numbers (headReads, Johnson/AtFull/Head/PlanReads.lean).

Limits. At HW: that the public part's own head's plan is HW trimmed is the join's. The full size
alone. Nothing on soundness.

-/
import Johnson.AtFull.Head.PlanAtFull
import Johnson.AtFull.Public.Views
import Johnson.AtFull.Rows.ArmsOfFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Made.Decl (LV viewL viewsFull)
open _root_.AtFull.Head (HW runW runW_ok headReads headReadsW)
open _root_.AtFull.Rows (lookH ownH smallH)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)

/-- One test on a head's plan. -/
def headB (H : Head.HPlanH2) : Bool :=
  decide ([lvOf "H" 2 (1 + 12) true H.ns H.NCL H.tl H.Fp.trimL H.Tp] = viewsFull.drop 24) &&
    decide (H.own Cond.hFull = ownH) && decide (smallSize H.tl = smallH)

/-- **By the kernel**: the run at the stand-ins returns, and the test accepts its value. -/
theorem head_walk : (match runW with
    | .ok H => headB H
    | .error _ => false) = true := by decide +kernel

/-- A negative test: the run returns, and with one scalar more the test rejects. -/
theorem head_bent : (match runW with
    | .ok H => !headB { H with nMsg := H.nMsg + 1 }
    | .error _ => false) = true := by decide +kernel

theorem head_W : headB HW = true := by
  have h := head_walk
  rw [runW_ok] at h
  exact h

/-- **hV_at's premise on the head's link.** -/
theorem hHV_at {X : Public} (hN : X.NGr = 12) (eH : X.H = { HW with Fp := HW.Fp.trimL }) :
    [viewL ((Verify.headPlanOf X default).link "H" (1 + X.NGr) 2 0 true)] = viewsFull.drop 24 := by
  have h := head_W
  unfold headB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [viewL_link, hN]
  show [lvOf "H" 2 (1 + 12) true X.H.ns X.H.NCL X.H.tl X.H.Fp X.H.Tp] = viewsFull.drop 24
  rw [eH]
  exact h.1.1

/-- **armsB_at's premise on the head's three parts.** -/
theorem hHA_at {X : Public} (eH : X.H = { HW with Fp := HW.Fp.trimL }) (eS : X.hS = Cond.hFull)
    (hR : headReads X.HLy = headReadsW) :
    forestSize X.HLy.fs = lookH ∧ X.H.own X.hS = ownH ∧ smallSize X.H.tl = smallH := by
  have h := head_W
  unfold headB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_, ?_⟩
  · unfold headReads headReadsW at hR
    simp only [List.cons.injEq] at hR
    obtain ⟨-, -, -, -, a, b, c, d, e, -⟩ := hR
    unfold forestSize lookH Forest.Shape.v Forest.Shape.d
    rw [a, b, c, d, e]
    rfl
  · rw [eH, eS]
    exact h.1.2
  · rw [eH]
    exact h.2

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.head_walk
#print axioms Johnson.AtFull.Public.head_bent
#print axioms Johnson.AtFull.Public.head_W
#print axioms Johnson.AtFull.Public.hHV_at
#print axioms Johnson.AtFull.Public.hHA_at
