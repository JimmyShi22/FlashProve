-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/SameRun.lean: the congruence of Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTest.lean for the schemes of ZKCP/Defs.lean,
over one hash function: two schemes with one verifier whose committer and prover have the same law at
every hash function have the same completeness error and the same index privacy, in its strong form,
with the same simulator and the same bound. Nothing here is a goal.
-/
import ZKCP.CoinsFirstArg

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- Two schemes with one verifier whose committer and prover have the same law at every hash
function. -/
structure SameRun (A A' : Arg lam I X W IVK ISK Pf) : Prop where
  C : ∀ f i, (A'.C i).run f = (A.C i).run f
  P : ∀ f k x w, (A'.P k x w).run f = (A.P k x w).run f
  V : A'.V = A.V

variable {A A' : Arg lam I X W IVK ISK Pf}

theorem Pr_congr_run {α : Type} {c c' : OComp lam α} (h : ∀ f, c.run f = c'.run f)
    (E : Oracle lam → Set α) : Pr c E = Pr c' E := by
  unfold Pr PrCoins
  simp only [h]

theorem realLoop_congr (h : SameRun A A') (Z : ViewEnv lam IVK X W Pf) (f : Oracle lam)
    (isk : ISK) : ∀ (Vt : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf),
      (realLoop A' Z isk Vt n v).run f = (realLoop A Z isk Vt n v).run f
  | .halt, _, _ => rfl
  | .query q k, n, v => by
    simp only [realLoop, OComp.run]
    exact realLoop_congr h Z f isk (k (f q)) n _
  | .sample m k, n, v => by
    simp only [realLoop, OComp.run]
    exact congrArg _ (funext fun r => realLoop_congr h Z f isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
    simp only [realLoop]
    cases Z v with
    | none => rfl
    | some xw =>
      exact run_bind_congr f (h.P f isk xw.1 xw.2) fun π =>
        realLoop_congr h Z f isk (k xw.1 π) n _

theorem realExp_congr (h : SameRun A A') (Vt : IVK → AdvVerifier lam X Pf)
    (Z : ViewEnv lam IVK X W Pf) (i : I) (N : ℕ) (f : Oracle lam) :
    (realExp A' Vt Z i N).run f = (realExp A Vt Z i N).run f := by
  show ((A'.C i).bind fun key => realLoop A' Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).run f
    = ((A.C i).bind fun key => realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).run f
  exact run_bind_congr f (h.C f i) fun key => realLoop_congr h Z f key.2 _ N _

/-- **Index privacy, in its strong form, reads the honest side through its law alone.** -/
theorem strongPrivacy_congr {R : IndexedRelation I X W PP} {S : Simulator lam PP IVK X Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : SameRun A A') (hp : HasStrongIndexPrivacyWith R A S ζ) :
    HasStrongIndexPrivacyWith R A' S ζ := by
  intro i Z hZ tV Vt N hb
  obtain ⟨h1, h2⟩ := hp i Z hZ tV Vt N hb
  have e : (fun T => Pr (realExp A' Vt Z i N) (fun _ => T)) =
      fun T => Pr (realExp A Vt Z i N) (fun _ => T) :=
    funext fun T => Pr_congr_run (realExp_congr h Vt Z i N) _
  refine ⟨?_, h2⟩
  rw [e]
  exact h1

theorem completenessExp_congr (h : SameRun A A') (i : I) (x : X) (w : W) (f : Oracle lam) :
    (completenessExp A' i x w).run f = (completenessExp A i x w).run f := by
  show ((A'.C i).bind fun key => (A'.P key.2 x w).bind fun π => A'.V key.1 x π).run f =
    ((A.C i).bind fun key => (A.P key.2 x w).bind fun π => A.V key.1 x π).run f
  rw [h.V]
  exact run_bind_congr f (h.C f i) fun key =>
    run_bind_congr f (h.P f key.2 x w) fun _ => rfl

/-- **Completeness reads the honest side through its law alone.** -/
theorem completeness_congr {R : IndexedRelation I X W PP} {a : ℝ≥0∞} (h : SameRun A A')
    (hc : HasCompletenessError R A a) : HasCompletenessError R A' a := fun i x w hr =>
  (Pr_congr_run (completenessExp_congr h i x w) _).trans_le (hc i x w hr)

end ZKCP

#print axioms ZKCP.strongPrivacy_congr
#print axioms ZKCP.completeness_congr
