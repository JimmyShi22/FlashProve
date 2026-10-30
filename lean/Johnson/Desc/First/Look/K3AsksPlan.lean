-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AsksPlan.lean: WHAT A YES OF THE LOOKUPS' LIGHT ROW ON THE DIGITS
(Johnson/Desc/First/Look/K3Asks.lean: digRow) GIVES IN THE FORM OF A LIST OF PUBLIC TESTS ON THE
PLAN: at every link digAt answers and THE LAWS' OWN Bool digB says yes, at every radius, at the
prime. One theorem, beside asks_dig (K3AsksLaw.lean), which ends in DigOK. A tie of texts. NO
SOUNDNESS IS CLAIMED.

OBJECT: the function digRow of K3Asks.lean.
USER: K03PlanOf.lean, K3Base.lean, Johnson/P2LawR/LaidArrAtHead.lean (asks_digB).
LETTERS: X, D free; rad free in the conclusion.
Compiled with the whole library.

Limits. One way. The number of links is linksOf X: that it is 25 is a fact of the goals' scope.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AsksLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks
open OnBytes OnBytes.Model

/-- **The digits' row gives the laws' own Bool at every link, at every radius.** -/
theorem asks_digB {X : Verify.Public} {D : Sent} (h : digRow X D = true)
    (rad : OracleShape → Nat) :
    ∀ i < linksOf X, ∃ x tl, First.Look.digAt X i = some (x, tl) ∧
      First.Look.digB (Params.settingOf X.P.frame) x tl D.up rad Cb.Gl.p = true := by
  intro i hi
  have h0 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  have e0 : First.Look.digAt X i = digAt X i := rfl
  cases e : digAt X i with
  | none =>
    rw [e] at h0
    exact absurd h0 (by simp)
  | some xt =>
    rw [e] at h0
    have h1 : digB (Params.settingOf X.P.frame) xt.1 xt.2 D = true := h0
    exact ⟨xt.1, xt.2, e0.trans e, digB_up h1 rad⟩

/-- Where the head's link is number 24 there are 25 links. -/
theorem links_25 {X : Verify.Public} (h : (if X.p4 then 2 else 1) * X.NGr = 24) :
    linksOf X = 25 := by
  unfold linksOf
  rw [h]

end VerifiableInference.Desc.K3Asks

#print axioms VerifiableInference.Desc.K3Asks.asks_digB
