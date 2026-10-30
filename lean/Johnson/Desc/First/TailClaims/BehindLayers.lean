-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/BehindLayers.lean: the sub-protocol without a round "behind the
batching" at a layers' link, whose order names three runs: "K8.lsTail", "free-slot", "K8.tests"
(orderAfterOf, Johnson/Desc/First/Driver/Chain.lean): one step on the shape of the first chain's
state, with its two laws. The like of behindG, behind_carries and behind_returns
(Johnson/Desc/First/TailClaims/BehindChain.lean), with the run in the middle as a letter. General
laws; nothing is evaluated.

  `behindG₃ gT gF nU`: the step on the shape: a test gT for the link's tests behind the adding; then
    lsTailG; then a step gF for the run in the middle; then testsGC.
  **`behind₃_carries`**: under "the middle run carries gF".
  **`behind₃_returns`**: under "the middle run carries gF, and returns where gF returns and a test
    vF on values accepts"; vF accepts behind "K8.lsTail"; and the premises of behind_returns, its
    last one asked at the state behind the two runs.

Limits. THE RUN IN THE MIDDLE, ITS STEP gF AND ITS TWO LAWS ARE PREMISES: another kind's. So are the
link's tests behind the adding. That a description's link has this order is not said here. That
behindG₃ returns at a shape of the protocol is not shown. Four premises of behind₃_returns are asked
at every state and spent at one or two. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.BehindChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (sits_lsTail sits_tests)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)

/-- **The step on the shape.** -/
def behindG₃ (gT : ChainSh → Bool) (gF : ChainSh → Except String ChainSh) (nU : Array Nat)
    (a : ChainSh) : Except String ChainSh :=
  if gT a then ((lsTailG a).bind gF).bind (testsGC nU)
  else .error "the tests behind the adding: the shape"

variable {L : Link S Claim} {i : Nat} {oF : Nat × String} {p : K8.ParW} {same : S → S → Bool}
  {r₁ r₂ rF : S → Except String S} {gT : ChainSh → Bool} {gF : ChainSh → Except String ChainSh}

theorem behind₃_carries (ho : L.orderAfter = [(i, "K8.lsTail"), oF, (i, "K8.tests")])
    (K : K8Runs L.hear i p same r₁ r₂)
    (hF : ((L.hear[oF.1]?).bind fun b => b.after.lookup oF.2) = some rF)
    (cF : ∀ s s' t, rF s = .ok s' → gF (chainSh s) = .ok t → t = chainSh s') (s s' : S)
    (t : ChainSh) (hr : L.runBehind s = .ok s')
    (hg : behindG₃ gT gF p.nU (chainSh s) = .ok t) : t = chainSh s' := by
  obtain ⟨-, s₁, s₂, a₁, aF, a₂⟩ := (runBehind_three ho K.look₁ hF K.look₂ s s').1 hr
  obtain ⟨u₁, m₁, e₁⟩ := K.bare₁
  obtain ⟨u₂, m₂, e₂⟩ := K.bare₂
  unfold behindG₃ at hg
  by_cases hb : gT (chainSh s) = true
  · rw [if_pos hb] at hg
    cases h1 : lsTailG (chainSh s) with
    | error e => rw [h1] at hg; exact nomatch hg
    | ok t₁ =>
      rw [h1] at hg
      have c₁ := lsTail_carries p u₁ m₁ s s₁ t₁ ((e₁ s s₁).1 a₁).1 h1
      subst c₁
      cases h2 : gF (chainSh s₁) with
      | error e =>
        have hg' : ((gF (chainSh s₁)).bind (testsGC p.nU)) = .ok t := hg
        rw [h2] at hg'
        exact nomatch hg'
      | ok t₂ =>
        have hg' : ((gF (chainSh s₁)).bind (testsGC p.nU)) = .ok t := hg
        rw [h2] at hg'
        have c₂ := cF s₁ s₂ t₂ aF h2
        subst c₂
        exact testsC_carries p u₂ m₂ s₂ s' t ((e₂ s₂ s').1 a₂).1 hg'
  · rw [if_neg hb] at hg
    exact nomatch hg

theorem behind₃_returns (ho : L.orderAfter = [(i, "K8.lsTail"), oF, (i, "K8.tests")])
    (K : K8Runs L.hear i p same r₁ r₂)
    (hF : ((L.hear[oF.1]?).bind fun b => b.after.lookup oF.2) = some rF)
    (cF : ∀ s s' t, rF s = .ok s' → gF (chainSh s) = .ok t → t = chainSh s') {vT vF : S → Bool}
    (retF : ∀ s t, gF (chainSh s) = .ok t → vF s = true → ∃ s', rF s = .ok s')
    (hT : ∀ s, gT (chainSh s) = true → vT s = true → L.tests s = .ok ())
    (hsame : ∀ (s : S) (q : K8Part), same s (k8PartP.set s q) = true) (s : S) (t : ChainSh)
    (hg : behindG₃ gT gF p.nU (chainSh s) = .ok t) (hv : vT s = true)
    (hvF : ∀ s₁, r₁ s = .ok s₁ → vF s₁ = true)
    (hv₂ : ∀ s₁ s₂, r₁ s = .ok s₁ → rF s₁ = .ok s₂ → valsS p.nU s₂ = true) :
    ∃ s', L.runBehind s = .ok s' := by
  obtain ⟨u₁, m₁, e₁⟩ := K.bare₁
  obtain ⟨u₂, m₂, e₂⟩ := K.bare₂
  unfold behindG₃ at hg
  by_cases hb : gT (chainSh s) = true
  · rw [if_pos hb] at hg
    cases h1 : lsTailG (chainSh s) with
    | error e => rw [h1] at hg; exact nomatch hg
    | ok t₁ =>
      rw [h1] at hg
      obtain ⟨s₁, b₁⟩ := lsTail_returns p u₁ m₁ s t₁ h1
      have w₁ : same s s₁ = true := by
        obtain ⟨q, -, rfl⟩ := (sits_lsTail p u₁ m₁ s s₁).1 b₁
        exact hsame s _
      have a₁ : r₁ s = .ok s₁ := (e₁ s s₁).2 ⟨b₁, w₁⟩
      have c₁ := lsTail_carries p u₁ m₁ s s₁ t₁ b₁ h1
      subst c₁
      have hg' : ((gF (chainSh s₁)).bind (testsGC p.nU)) = .ok t := hg
      cases h2 : gF (chainSh s₁) with
      | error e => rw [h2] at hg'; exact nomatch hg'
      | ok t₂ =>
        rw [h2] at hg'
        obtain ⟨s₂, aF⟩ := retF s₁ t₂ h2 (hvF s₁ a₁)
        have c₂ := cF s₁ s₂ t₂ aF h2
        subst c₂
        obtain ⟨s', b₂⟩ := testsC_returns p u₂ m₂ s₂ t hg' (hv₂ s₁ s₂ a₁ aF)
        have w₂ : same s₂ s' = true := by
          obtain ⟨q, Fc, -, -, rfl⟩ := (sits_tests p u₂ m₂ s₂ s').1 b₂
          exact hsame s₂ _
        exact ⟨s', (runBehind_three ho K.look₁ hF K.look₂ s s').2
          ⟨hT s hb hv, s₁, s₂, a₁, aF, (e₂ s₂ s').2 ⟨b₂, w₂⟩⟩⟩
  · rw [if_neg hb] at hg
    exact nomatch hg

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behind₃_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behind₃_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behindG₃
