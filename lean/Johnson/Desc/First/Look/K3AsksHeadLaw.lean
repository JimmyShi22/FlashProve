-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AsksHeadLaw.lean: A YES OF THE LOOKUPS' LIGHT TEST AT THE HEAD's LINK's
CALLS (Johnson/Desc/First/Look/K3AsksHead.lean) GIVES THE TEST THAT THE LAW NAMES, AND SO ITS
PREMISE HeadOK (Johnson/Desc/First/Look/K3CallerHead.lean). Statements and proofs. Ties of texts: no
error term. NO SOUNDNESS IS CLAIMED.

OBJECT: the function headRow of K3AsksHead.lean.
USER: K3AsksDoorLaw.lean, K03PlanOf.lean (asks_head); Johnson/P5J/K03HeadTestsAt.lean (headAt_up,
  headAt_shape).
LETTERS: X : Verify.Public free.
Compiled with the whole library.


Main names:
  `headB_up`: the light test is the law's headB, at the sizes read off the head's shape.
  `headAt_shape`: at headAt's place the kind's own parameters make the place's record.
  `asks_head`: headRow X = true: the law's headAt answers, the law's headB says yes there at the
    program's own floor, and HeadOK holds there.

Limits. Those of K3CallerHead.lean.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AsksHead
import Johnson.Desc.First.Look.K3CallerHeadTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (P lookAt)
open VerifiableInference.Desc.Kinds.Head.Law (sizesOf policyOf HeadOK headOK_of)

/-- The light test is the law's. -/
theorem headB_up (h : Head.Shape) (floor : ℕ) (fs : Forest.Shape) :
    @Kinds.Head.Law.headB (sizesOf h) floor fs = headB h floor fs := rfl

theorem headAt_up (X : Verify.Public) : Kinds.Head.Law.headAt X = headAt X := rfl

theorem floorAt_up (h : Head.Shape) : Head.keyFloor h = floorAt h := rfl

/-- At headAt's place the kind's own parameters make the place's record. -/
theorem headAt_shape {X : Verify.Public} {x : First.Look.Place} (e : headAt X = some x) :
    (P.ofPlace (Params.settingOf X.P.frame) false x).shape = some x.fs := by
  unfold headAt at e
  obtain ⟨x0, -, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨h', hh, e⟩ := Option.map_eq_some_iff.1 e
  subst e
  exact hh

/-- **THE HEAD's ROW GIVES HeadOK.** -/
theorem asks_head {X : Verify.Public} (h : headRow X = true) :
    ∃ x, Kinds.Head.Law.headAt X = some x ∧
      @Kinds.Head.Law.headB (sizesOf X.hS) (Head.keyFloor X.hS) x.fs = true ∧
      @HeadOK (sizesOf X.hS) (Params.settingOf X.P.frame) x (Head.keyFloor X.hS) := by
  unfold headRow at h
  cases e : headAt X with
  | none =>
    rw [e] at h
    exact absurd h (by simp)
  | some x =>
    rw [e] at h
    have h1 : @Kinds.Head.Law.headB (sizesOf X.hS) (Head.keyFloor X.hS) x.fs = true := h
    exact ⟨x, e, h1,
      @headOK_of (sizesOf X.hS) (policyOf X.hS) ⟨fun _ => 0, 0, 0⟩ _ _ _ (headAt_shape e) h1⟩

end VerifiableInference.Desc.K3Asks

#print axioms VerifiableInference.Desc.K3Asks.headB_up
#print axioms VerifiableInference.Desc.K3Asks.asks_head
