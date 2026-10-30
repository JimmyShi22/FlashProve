-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/DeferTotal.lean: the proof of Spec.deferTotal (Rom/SpecDeferTotal.lean): deferred programming
  for an adversary with one budget for all oracles.
  (Terms: Rom/Defer.lean; deferred programming: lean/GLOSSARY.md.)

  `deferTotal`: for an adversary with at most t queries to all oracles together and at most N calls
  (`Adv.TotalBound`; N is in no bound), if every run in mode I stays within (e, M, ℓ, os)
  (`DSt.Within`, Rom/Defer.lean: no violation of the rules; at most e o plain and M o marked
  evaluations of o; marked ones only at oracles of os, each charged to a token of at least ℓ o
  bits), the outputs in mode R and mode I are within t * max over o in os of (M o / 2^(ℓ o)) + the
  sum over o in os of M o (e o + M o) / 2^(ℓ o).

  The proof repeats the induction over the adversary of Rom/DeferProof_tail.lean (adv_bound; here
  adv_boundT) with another invariant: u o still counts the adversary's queries to o, and (the sum
  over os of u o) + (what is left of the budget) ≤ t. The other lemmas of that file are used as they
  are.

  Notation:
    `A.TotalBound t N` (Rom/World.lean): at most t queries in all and at most N calls, on every path
    `tv p q` (Prob/Basic.lean; it stands in `Spec.deferTotal`, Rom/SpecDeferTotal.lean): statistical
      (total variation) distance of two discrete distributions
    `mu M ℓ os`: the largest M o / 2^(ℓ o) over the oracles of os
    `advCost C A s G` (Rom/DeferProof_tail.lean): the expected number of hits during a whole run of
      an adversary against a challenger in mode I, plus the expectation of G at its end
    `pot ℓ os a b` (Rom/DeferProof_tail.lean): Σ over the oracles of os of a (b + a) / 2^ℓ, for `a`
      marked evaluations and `b` logged points; `p.pot ℓ os`: the potential of `p : PSt S sp`
    `PSt`, `PSt.inst`, `Valid`, `Agree`, `law` (Rom/DeferProof_tail.lean)
-/
import Rom.SpecDeferTotal
import Rom.DeferProof_tail
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail

variable {S : OSpec} {sp : Split S} {e M ℓ : S.ι → ℕ} {os : Finset S.ι}

/-- the largest M o / 2^(ℓ o) over the oracles of os: a bound on the chance that one query hits a
marked evaluation, for M, ℓ as in `DSt.Within` -/
def mu (M ℓ : S.ι → ℕ) (os : Finset S.ι) : ℝ≥0∞ :=
  os.sup fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o

/-- One oracle at the end, with `a` marked evaluations and `b` logged points, at most `u` of them
the adversary's and `e₀` plain ones. Under h1 (`a ≤ M₀`), h2 (`b ≤ u + e₀`) and hμ
(`M₀ / 2 ^ ℓ₀ ≤ μ`), its term `a * (b + a) / 2 ^ ℓ₀` of the potential (`pot`,
Rom/DeferProof_tail.lean) is at most `u * μ + M₀ * (e₀ + M₀) / 2 ^ ℓ₀`. -/
theorem term_le {a b u e₀ M₀ ℓ₀ : ℕ} {μ : ℝ≥0∞} (h1 : a ≤ M₀)
    (h2 : b ≤ u + e₀) (hμ : (M₀ : ℝ≥0∞) / 2 ^ ℓ₀ ≤ μ) :
    ((a * (b + a) : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ₀) ≤
      (u : ℝ≥0∞) * μ + (M₀ : ℝ≥0∞) * (e₀ + M₀ : ℕ) / 2 ^ ℓ₀ := by
  have h3 : a * (b + a) ≤ u * M₀ + M₀ * (e₀ + M₀) :=
    calc a * (b + a) ≤ M₀ * (u + e₀ + M₀) := Nat.mul_le_mul h1 (Nat.add_le_add h2 h1)
      _ = u * M₀ + M₀ * (e₀ + M₀) := by ring
  calc
    ((a * (b + a) : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ₀) ≤
        ((u * M₀ + M₀ * (e₀ + M₀) : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ₀) := by gcongr
    _ = (u : ℝ≥0∞) * ((M₀ : ℝ≥0∞) / 2 ^ ℓ₀) + (M₀ : ℝ≥0∞) * (e₀ + M₀ : ℕ) / 2 ^ ℓ₀ := by
        simp only [div_eq_mul_inv, one_mul]
        push_cast
        ring
    _ ≤ (u : ℝ≥0∞) * μ + (M₀ : ℝ≥0∞) * (e₀ + M₀ : ℕ) / 2 ^ ℓ₀ := by gcongr

/-- One more query raises the sum over os by at most 1 (by 0 if its oracle is outside os). -/
theorem sum_update_le (os : Finset S.ι) (u : S.ι → ℕ) (o : S.ι) :
    ∑ o' ∈ os, Function.update u o (u o + 1) o' ≤ ∑ o' ∈ os, u o' + 1 := by
  by_cases ho : o ∈ os
  · rw [← Finset.add_sum_erase os _ ho, ← Finset.add_sum_erase os u ho, Function.update_self]
    have : ∑ o' ∈ os.erase o, Function.update u o (u o + 1) o' = ∑ o' ∈ os.erase o, u o' :=
      Finset.sum_congr rfl fun o' ho' => Function.update_of_ne (Finset.ne_of_mem_erase ho') _ _
    omega
  · have : ∑ o' ∈ os, Function.update u o (u o + 1) o' = ∑ o' ∈ os, u o' :=
      Finset.sum_congr rfl fun o' ho' => Function.update_of_ne (fun h : o' = o => ho (h ▸ ho')) _ _
    omega

/-- The bound for a run, with one budget: u o counts the adversary's queries to o so far, t' is what
is left. (not all hypotheses are named here: see the statement below) -/
theorem adv_boundT {Out In α : Type} (C : Chall S sp Out In) (t : ℕ) (A : Adv S Out In α) :
    ∀ (τ : C.τ) (p : PSt S sp) (u : S.ι → ℕ) (t' N : ℕ), A.TotalBound t' N → Valid ℓ os u p →
      ∑ o ∈ os, u o + t' ≤ t →
      (∀ w, Agree p.slots w → ∀ x ∈ (interact (C.world true) A (τ, p.inst w)).support,
        x.2.2.Within e M ℓ os) →
      expect (law p.slots) (fun w => advCost C A (τ, p.inst w) fun _ => 0) + p.pot ℓ os
        ≤ (t : ℝ≥0∞) * mu M ℓ os + ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o := by
  induction A with
  | halt a =>
    intro τ p u t' N _ hv hb hs
    simp only [advCost]
    rw [expect_zero, zero_add]
    obtain ⟨w, hw⟩ := exists_agree p.slots
    have hW : (p.inst w).Within e M ℓ os :=
      hs w hw (a, (τ, p.inst w)) (by rw [interact]; exact (PMF.mem_support_pure_iff _ _).2 rfl)
    calc p.pot ℓ os ≤ ∑ o ∈ os, ((u o : ℝ≥0∞) * mu M ℓ os + (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o) := by
          refine Finset.sum_le_sum fun o ho =>
            term_le ?_ ?_ (Finset.le_sup (f := fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) ho)
          · rw [← aCount_inst p.evs w o]; exact hW.2.2.1 o
          · have := hv.count o
            have h3 : p.nPlain o ≤ e o := hW.2.1 o
            omega
      _ = (∑ o ∈ os, (u o : ℝ≥0∞)) * mu M ℓ os +
            ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ (t : ℝ≥0∞) * mu M ℓ os + ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o := by
          have hu : (∑ o ∈ os, (u o : ℝ≥0∞)) ≤ (t : ℝ≥0∞) := by
            exact_mod_cast le_trans (Nat.le_add_right _ t') hb
          gcongr
  | sample n k ih =>
    intro τ p u t' N hB hv hb hs
    simp only [advCost]
    rw [expect_comm]
    refine expect_add_const_le _ _ _ _ fun r _ =>
      ih r τ p u t' N (hB r) hv hb fun w hw x hx => hs w hw x ?_
    rw [interact]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hx⟩
  | query o q k ih =>
    intro τ p u t' N hB hv hb hs
    cases t' with
    | zero => exact absurd hB (by simp [Adv.TotalBound])
    | succ t' =>
      simp only [advCost]
      have hcomm : expect (law p.slots) (fun w => expect (lazyAnswer (p.inst w).table o q) fun y =>
            advCost C (k y.1) (τ, withT (p.inst w) y.2) fun _ => 0)
          = expect (lazyAnswer p.table o q) fun y => expect (law p.slots) fun w =>
            advCost C (k y.1) (τ, (p.log ⟨o, q⟩ y.2 p.nPlain).inst w) fun _ => 0 :=
        expect_comm (law p.slots) (lazyAnswer p.table o q) fun w y =>
          advCost C (k y.1) (τ, withT (p.inst w) y.2) fun _ => 0
      rw [expect_add, hcomm, add_comm (expect (law p.slots) _) _, add_assoc]
      refine expect_add_const_le _ _ _ _ fun y hy => ?_
      refine le_trans (add_le_add le_rfl
        (le_trans (add_le_add (hitQ_bound hv ⟨o, q⟩) le_rfl) (pot_log_le hv ⟨o, q⟩ y.2 p.nPlain)))
        (ih y.1 τ (p.log ⟨o, q⟩ y.2 p.nPlain) (Function.update u o (u o + 1)) t' N
          (hB y.1) ?_ ?_ ?_)
      · exact valid_log hv ⟨o, q⟩ y.2 _ (fun k' hk' => lazy_support hy k' hk')
          (count_bump_left ⟨o, q⟩ hv.count)
      · have := sum_update_le os u o
        omega
      · intro w hw x hx
        refine hs w hw x ?_
        rw [interact]
        exact (PMF.mem_support_bind_iff _ _ _).2
          ⟨(y.1, (τ, withT (p.inst w) y.2)), (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩, hx⟩
  | call m k ih =>
    intro τ p u t' N hB hv hb hs
    cases N with
    | zero => exact absurd hB (by cases t' <;> simp [Adv.TotalBound])
    | succ N =>
      have hB' : ∀ a, (k a).TotalBound t' N := by cases t' <;> exact hB
      simp only [advCost]
      refine step_bound (e := e) (M := M) u _ (fun y => advCost C (k y.1.1) (y.1.2, y.2) fun _ => 0)
        (fun y =>
          ∀ x ∈ (interact (C.world true) (k y.1.1) (y.1.2, y.2)).support, x.2.2.Within e M ℓ os)
        (fun y hy => ?_) (fun a p' hv' hq' => ?_) (C.step τ m)
        p hv fun w hw y hy x hx => hs w hw x ?_
      · obtain ⟨x, hx⟩ := (interact (C.world true) (k y.1.1) (y.1.2, y.2)).support_nonempty
        exact ⟨x.2.2, interact_ext C _ _ x hx, hy x hx⟩
      · exact ih a.1 a.2 p' u t' N (hB' a.1) hv' hb hq'
      · rw [interact]
        exact (PMF.mem_support_bind_iff _ _ _).2
          ⟨(y.1.1, (y.1.2, y.2)), (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩, hx⟩

/-- Deferred programming for a total budget. -/
theorem deferTotal : Spec.deferTotal := by
  intro S sp Out In α C s₀ A t e M ℓ N os hB hW
  refine (tv_le_hits C s₀ A).trans ?_
  have hv : Valid ℓ os (fun _ => 0) (⟨Table.empty S, [], [], [], fun _ => 0, []⟩ : PSt S sp) :=
    ⟨⟨fun t => by simp, fun x hx => by simp at hx, fun x hx => by simp at hx⟩,
      fun w _ k hk => absurd rfl hk, fun x hx => by simp at hx, fun o => by simp [qCount]⟩
  have h := adv_boundT (e := e) (M := M) C t A s₀
    ⟨Table.empty S, [], [], [], fun _ => 0, []⟩ (fun _ => 0) t N hB hv
    (by simp) (fun w hw x hx => by
      cases hw
      exact hW x hx)
  rw [E_nil] at h
  exact le_trans (le_add_right le_rfl) h

end DeferTail
end Rom
