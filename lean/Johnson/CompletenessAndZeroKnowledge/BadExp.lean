-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/BadExp.lean: the experiment that records what the honest side makes: keys and a proof; with its marginals.
-/
import Johnson.FrontRoad.CompleteUpTo

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad

section Front
variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- The experiment that records what the honest side makes: keys and a proof. -/
def badExp (A : ZKCP.Arg lam I X W IVK ISK Pf) (i : I) (x : X) (w : W) :
    ZKCP.OComp lam ((IVK × ISK) × Pf) :=
  (A.C i).bind fun keys => (A.P keys.2 x w).bind fun π => .pure (keys, π)

theorem expect_add_fn {α : Type} (p : PMF α) (F G : α → ℝ≥0∞) :
    ZKCP.expect p (fun a => F a + G a) = ZKCP.expect p F + ZKCP.expect p G := by
  unfold ZKCP.expect
  simp only [mul_add]
  exact ENNReal.tsum_add

variable (A : ZKCP.Arg lam I X W IVK ISK Pf)

theorem map_fst_session (f : ZKCP.Oracle lam) (keys : IVK × ISK) (x : X) (w : W) :
    ((((A.P keys.2 x w).bind fun π => ZKCP.OComp.pure (keys, π))).run f).map (fun o => o.1) = PMF.pure keys := by
  rw [ZKCP.run_bind, PMF.map_bind]
  show (((A.P keys.2 x w).run f).bind fun π => (PMF.pure (keys, π)).map fun o => o.1) = _
  simp only [PMF.pure_map]
  exact PMF.bind_const _ _

theorem map_snd_session (f : ZKCP.Oracle lam) (keys : IVK × ISK) (x : X) (w : W) :
    ((((A.P keys.2 x w).bind fun π => ZKCP.OComp.pure (keys, π))).run f).map (fun o => o.2) = (A.P keys.2 x w).run f := by
  rw [ZKCP.run_bind, PMF.map_bind]
  show (((A.P keys.2 x w).run f).bind fun π => (PMF.pure (keys, π)).map fun o => o.2) = _
  simp only [PMF.pure_map]
  exact PMF.bind_pure _

/-- An event on the keys alone has the committer's chance. -/
theorem prob_badExp_keys (i : I) (x : X) (w : W) (f : ZKCP.Oracle lam) (E : Set (IVK × ISK)) :
    ZKCP.prob ((badExp A i x w).run f) {o | o.1 ∈ E} = ZKCP.prob ((A.C i).run f) E := by
  have e : ((badExp A i x w).run f).map (fun o => o.1) = (A.C i).run f := by
    unfold badExp
    rw [ZKCP.run_bind, PMF.map_bind]
    simp only [map_fst_session]
    exact PMF.bind_pure _
  rw [← e, ZKCP.prob_map]
  rfl

/-- An event on the proof alone is bounded by a bound at every key. -/
theorem prob_badExp_proof (i : I) (x : X) (w : W) (f : ZKCP.Oracle lam) (E : Set Pf) {ε : ℝ≥0∞}
    (hE : ∀ keys : IVK × ISK, ZKCP.prob ((A.P keys.2 x w).run f) E ≤ ε) :
    ZKCP.prob ((badExp A i x w).run f) {o | o.2 ∈ E} ≤ ε := by
  unfold badExp
  rw [ZKCP.run_bind, ZKCP.prob_bind]
  refine le_trans (ZKCP.expect_le_on_support _ fun keys _ => ?_) (le_of_eq (ZKCP.expect_const _ ε))
  refine le_trans (le_of_eq ?_) (hE keys)
  rw [← map_snd_session A f keys x w, ZKCP.prob_map]
  rfl

end Front

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.prob_badExp_keys
#print axioms OnBytes.FrontRoad.prob_badExp_proof
