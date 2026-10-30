-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2.lean: the proof of the lemma on deferred programming of the random oracle
(`Spec.defer2`, CompileK/SpecDefer2.lean).

Main names:
  `adv_boundT2`: the bound for a run: the analogue of `adv_boundT` (Rom/DeferTotal.lean), with the
    counts by class and the hypothesis along the adversary.
  `defer2`: the last step, on `tv_le_hits` (Rom/DeferProof_tail.lean: the distance of the two modes
    is at most the expected number of hits in mode I).

`advCost` (Rom/DeferProof_tail.lean) is the expected number of hits of a run in mode I, plus the
expectation of a pay-off at its end, here 0. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs, in the random-oracle model, on Lean's three
axioms.

Notation: `cl`: `PtCls S K` (CompileK/SpecDefer2.lean): classes of points; `J`: `K → Bool`;
`J κ = true`: κ is a joint class (CompileK/SpecDefer2.lean); `ks`: `Finset K`: a finite set of
classes; `ℓ`: `K → ℕ`; in `DSt.Ok2 cl J ℓ ks d` (the head of CompileK/SpecDefer2.lean): lengths:
|charged| ≥ ℓ, in a joint class |charged| + |b| ≥ ℓ; `e`: `S.ι → ℕ`, `M`: `K → ℕ`; in
`DSt.CntK2 cl e M` (the head of CompileK/SpecDefer2.lean), the counts, at a halt: plain evaluations
of o at most e o, marked evaluations of class κ at most M κ; `t`, `N`: natural numbers; in
`A.TotalBound t N`, a hypothesis of `Spec.defer2` (`Adv.TotalBound`, Rom/World.lean): at most t
queries in all and at most N calls, on every path; `adv_boundT2` has `A.TotalBound t' N`.
-/
import CompileK.Defer2Step
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail2
open DeferTail

variable {S : OSpec} {sp : Split S} {K : Type} [DecidableEq K] {cl : PtCls S K} {J : K → Bool}
  {ℓ : K → ℕ} {ks : Finset K} {e : S.ι → ℕ} {M : K → ℕ}

/-- the largest M κ / 2^(ℓ κ) over the classes of ks -/
def muK (M ℓ : K → ℕ) (ks : Finset K) : ℝ≥0∞ := ks.sup fun κ => (M κ : ℝ≥0∞) / 2 ^ ℓ κ

theorem sum_update_leK (ks : Finset K) (u : K → ℕ) (κ : K) :
    ∑ o' ∈ ks, Function.update u κ (u κ + 1) o' ≤ ∑ o' ∈ ks, u o' + 1 := by
  by_cases ho : κ ∈ ks
  · rw [← Finset.add_sum_erase ks _ ho, ← Finset.add_sum_erase ks u ho, Function.update_self]
    have : ∑ o' ∈ ks.erase κ, Function.update u κ (u κ + 1) o' = ∑ o' ∈ ks.erase κ, u o' :=
      Finset.sum_congr rfl fun o' ho' => Function.update_of_ne (Finset.ne_of_mem_erase ho') _ _
    omega
  · have : ∑ o' ∈ ks, Function.update u κ (u κ + 1) o' = ∑ o' ∈ ks, u o' :=
      Finset.sum_congr rfl fun o' ho' => Function.update_of_ne (fun h : o' = κ => ho (h ▸ ho')) _ _
    omega

theorem aCountK_inst {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p)
    (w : List Bits) (κ : K) :
    ((p.inst w).evs.filter fun v => decide (cl.of ⟨v.o, v.pt⟩ = κ)).length =
      aCountK cl p.evs κ := by
  show ((p.evs.map fun x => x.inst w).filter fun v => decide (cl.of ⟨v.o, v.pt⟩ = κ)).length = _
  rw [List.filter_map, List.length_map]
  unfold aCountK
  congr 1
  refine List.filter_congr fun x hx => ?_
  show decide (cl.of (x.key w) = κ) = decide (clsOf cl x = κ)
  rw [(hv.ev x hx).cst w]

/-- The bound for a run: u κ counts the adversary's queries of class κ so far, t' is what is left.
Under the hypotheses below, the expectation of `advCost` plus `potP` is at most the bound of
`Spec.defer2`. -/
theorem adv_boundT2 {Out In α : Type} (C : Chall S sp Out In) (t : ℕ) (A : Adv S Out In α) :
    ∀ (τ : C.τ) (p : PSt S sp) (u : K → ℕ) (t' N : ℕ), A.TotalBound t' N →
      Valid2 cl J ℓ ks u p → ∑ κ ∈ ks, u κ + t' ≤ t →
      (∀ w,
        Agree p.slots w → AdvAlw C cl J (DSt.Ok2 cl J ℓ ks) (DSt.CntK2 cl e M) A (τ, p.inst w)) →
      expect (law p.slots) (fun w => advCost C A (τ, p.inst w) fun _ => 0) + potP cl ℓ ks p ≤
        (t : ℝ≥0∞) * muK M ℓ ks + ∑ κ ∈ ks, (M κ : ℝ≥0∞) * (e (cl.orc κ) + M κ : ℕ) / 2 ^ ℓ κ := by
  induction A with
  | halt a =>
    intro τ p u t' N _ hv hb hs
    simp only [advCost]
    rw [expect_zero, zero_add]
    obtain ⟨w, hw⟩ := exists_agree p.slots
    have hW : (p.inst w).CntK2 cl e M := hs w hw
    calc
      potP cl ℓ ks p ≤
          ∑ κ ∈ ks,
            ((u κ : ℝ≥0∞) * muK M ℓ ks + (M κ : ℝ≥0∞) * (e (cl.orc κ) + M κ : ℕ) / 2 ^ ℓ κ) := by
          refine Finset.sum_le_sum fun κ hκ =>
            term_le ?_ ?_ (Finset.le_sup (f := fun κ => (M κ : ℝ≥0∞) / 2 ^ ℓ κ) hκ)
          · rw [← aCountK_inst hv w κ]; exact hW.2 κ
          · have := hv.count κ
            have h3 : p.nPlain (cl.orc κ) ≤ e (cl.orc κ) := hW.1 _
            omega
      _ = (∑ κ ∈ ks, (u κ : ℝ≥0∞)) * muK M ℓ ks +
            ∑ κ ∈ ks, (M κ : ℝ≥0∞) * (e (cl.orc κ) + M κ : ℕ) / 2 ^ ℓ κ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ (t : ℝ≥0∞) * muK M ℓ ks +
            ∑ κ ∈ ks, (M κ : ℝ≥0∞) * (e (cl.orc κ) + M κ : ℕ) / 2 ^ ℓ κ := by
          have hu : (∑ κ ∈ ks, (u κ : ℝ≥0∞)) ≤ (t : ℝ≥0∞) := by
            exact_mod_cast le_trans (Nat.le_add_right _ t') hb
          gcongr
  | sample n k ih =>
    intro τ p u t' N hB hv hb hs
    simp only [advCost]
    rw [expect_comm]
    exact expect_add_const_le _ _ _ _ fun r _ => ih r τ p u t' N (hB r) hv hb fun w hw => hs w hw r
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
      refine le_trans
        (add_le_add le_rfl
          (le_trans (add_le_add (hitQ2 hv ⟨o, q⟩) le_rfl) (potP_log_le hv ⟨o, q⟩ y.2 p.nPlain)))
        (ih y.1 τ (p.log ⟨o, q⟩ y.2 p.nPlain)
          (Function.update u (cl.of ⟨o, q⟩) (u (cl.of ⟨o, q⟩) + 1)) t' N (hB y.1) ?_ ?_ ?_)
      · exact valid2_log hv ⟨o, q⟩ y.2 _ (fun k' hk' => lazy_support hy k' hk')
          (fun u₀ h0 => ⟨_, count_bump_left ⟨o, q⟩ h0⟩) (countK_bump_left ⟨o, q⟩ hv.count)
      · have := sum_update_leK ks u (cl.of ⟨o, q⟩)
        omega
      · exact fun w hw => hs w hw y hy
  | call m k ih =>
    intro τ p u t' N hB hv hb hs
    cases N with
    | zero => exact absurd hB (by cases t' <;> simp [Adv.TotalBound])
    | succ N =>
      have hB' : ∀ a, (k a).TotalBound t' N := by cases t' <;> exact hB
      simp only [advCost]
      exact step_bound2 u _
        (fun y : (In × C.τ) × DSt S => advCost C (k y.1.1) (y.1.2, y.2) fun _ => 0)
        (fun y : (In × C.τ) × DSt S =>
          AdvAlw C cl J (DSt.Ok2 cl J ℓ ks) (DSt.CntK2 cl e M) (k y.1.1) (y.1.2, y.2))
        (fun a p' hv' hq' => ih a.1 a.2 p' u t' N (hB' a.1) hv' hb hq') (C.step τ m)
        p hv fun w hw => hs w hw

/-- Deferred programming, by classes, with joint charges. -/
theorem defer2 : Spec.defer2 := by
  intro S sp K _ Out In α C s₀ A t e M ℓ N ks cl J hB hW
  refine (tv_le_hits C s₀ A).trans ?_
  have hv0 : Valid (fun _ => 0) (ks.image cl.orc) (fun _ => 0)
      (⟨Table.empty S, [], [], [], fun _ => 0, []⟩ : PSt S sp) :=
    ⟨⟨fun t => by simp, fun x hx => by simp at hx, fun x hx => by simp at hx⟩,
      fun w _ k hk => absurd rfl hk, fun x hx => by simp at hx, fun o => by simp [qCount]⟩
  have hv : Valid2 cl J ℓ ks (fun _ => 0)
      (⟨Table.empty S, [], [], [], fun _ => 0, []⟩ : PSt S sp) :=
    ⟨⟨_, hv0⟩, fun x hx => by simp at hx, fun κ => by simp [qCountK]⟩
  have h := adv_boundT2 (e := e) (M := M) C t A s₀
    ⟨Table.empty S, [], [], [], fun _ => 0, []⟩ (fun _ => 0) t N hB hv
    (by simp) (fun w hw => by
      cases hw
      exact hW)
  rw [E_nil] at h
  exact le_trans (le_add_right le_rfl) h

end DeferTail2
end Rom
