-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/IdealLoop.lean: a union bound along the ideal experiment of index privacy
(`ZKCP.Gen.idealLoop`), for any simulator.

Main results.
  `idealLoop_le`: steps 3 and 4 of the experiment end in a view with a bad proof with probability at
    most n · ε, against every adversary, given: an invariant `Inv k` of the simulator's state that
    an oracle query keeps and a batch takes from k to k + 1 · a bound ε on the probability that one
    batch's reply, from a state with `Inv k` and k < s1, holds a bad proof · an environment that
    names at most one own instance per batch · a starting view without a bad proof, a state with
    `Inv k`, and k + n ≤ s1.

Terms: E2E/HidingTerms.lean.

Limits. The four premises are hypotheses. Nothing is proved about any particular simulator or
scheme.

Definitions and helper lemmas.
  `BadView bad v`: some proof in the view v is bad.
  `pr_mono_support`: an inclusion of events on the support is enough.


-/
import ZKCP.Gen
import Prob.Count

set_option autoImplicit false

open scoped ENNReal

namespace AtPublicFiles.Shown
open Rom Prob
open ZKCP.Gen

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- Some proof in the view is bad. -/
def BadView (bad : Pf → Prop) (v : View S IVK X Pf) : Prop :=
  ∃ s ∈ v.sessions, ∃ y ∈ s, bad y.2

theorem pr_mono_support {α : Type} (p : PMF α) {E F : Set α}
    (h : ∀ y ∈ p.support, y ∈ E → y ∈ F) : pr p E ≤ pr p F := by
  have e : pr p E = pr p (E ∩ p.support) := (PMF.toOuterMeasure_apply_inter_support p E).symm
  rw [e]
  exact pr_mono _ fun y hy => h y hy.2 hy.1

section
variable (Sim : Simulator S PP IVK X Pf) (Z : ViewEnv S IVK X W Pf) (bad : Pf → Prop)
  (Inv : ℕ → Sim.St → Prop) (s1 : ℕ) (ε : ℝ≥0∞)
  (hans : ∀ k s o q, Inv k s → ∀ out ∈ (Sim.answer s o q).support, Inv k out.2)
  (hprv : ∀ k s xs, Inv k s → ∀ out ∈ (Sim.prove s xs).support, Inv (k + 1) out.2)
  (hpr : ∀ k s xs, Inv k s → k < s1 → xs.length ≤ 1 →
    pr (Sim.prove s xs) {out | ∃ π ∈ out.1.val, bad π} ≤ ε)
  (hZ : ∀ v b, Z v = some b → b.ownX.length ≤ 1)
include hans hprv hpr hZ

/-- **A union bound along the ideal experiment's steps 3 and 4**: under an invariant of the
simulator's state that counts the batches, and a bound ε on the probability that one batch's reply
holds a bad proof. -/
theorem idealLoop_le : ∀ (adv : AdvVerifier S X Pf) (n : ℕ) (v : View S IVK X Pf) (s : Sim.St)
    (k : ℕ), ¬ BadView bad v → Inv k s → k + n ≤ s1 →
    pr (idealLoop Sim Z adv n v s) {v' | BadView bad v'} ≤ (n : ℝ≥0∞) * ε
  | .halt, n, v, s, k, hv, _, _ => by
    classical
    show pr (PMF.pure v) _ ≤ _
    rw [pr_pure, if_neg (show v ∉ {v' | BadView bad v'} from hv)]
    exact zero_le _
  | .query o q f, n, v, s, k, hv, hi, hn =>
    pr_bind_le_of_forall _ _ _ fun out ho =>
      idealLoop_le (f out.1) n { v with trace := v.trace ++ [⟨o, q, out.1⟩] } out.2 k hv
        (hans k s o q hi out ho) hn
  | .sample m f, n, v, s, k, hv, hi, hn =>
    pr_bind_le_of_forall _ _ _ fun r _ =>
      idealLoop_le (f r) n { v with coins := v.coins ++ [r.val] } s k hv hi hn
  | .request _, 0, v, s, k, hv, _, _ => by
    classical
    show pr (PMF.pure v) _ ≤ _
    rw [pr_pure, if_neg (show v ∉ {v' | BadView bad v'} from hv)]
    exact zero_le _
  | .request f, n + 1, v, s, k, hv, hi, hn => by
    classical
    unfold idealLoop
    cases hz : Z v with
    | none =>
      show pr (PMF.pure v) _ ≤ _
      rw [pr_pure, if_neg (show v ∉ {v' | BadView bad v'} from hv)]
      exact zero_le _
    | some b =>
      refine (pr_bind_le_add _ _ _ {out | ∃ π ∈ out.1.val, bad π} (ε := (n : ℝ≥0∞) * ε)
        fun out ho hgood => ?_).trans ?_
      · refine idealLoop_le (f _) n _ out.2 (k + 1) (fun hb => ?_) (hprv k s _ hi out ho) (by omega)
        obtain ⟨l, hl, y, hy, hby⟩ := hb
        rcases List.mem_append.1 hl with hl | hl
        · exact hv ⟨l, hl, y, hy, hby⟩
        · obtain rfl := List.mem_singleton.1 hl
          exact hgood ⟨y.2, (List.of_mem_zip hy).2, hby⟩
      · rw [Nat.cast_succ, add_mul, one_mul, add_comm]
        exact add_le_add le_rfl (hpr k s _ hi (by omega) (hZ v b hz))

end

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.pr_mono_support
#print axioms AtPublicFiles.Shown.idealLoop_le
