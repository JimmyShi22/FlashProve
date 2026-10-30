-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Prob.lean: a probability bound for the proof of the lemma on deferred programming of
the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean): two hidden coordinates: an event that,
for every choice of the other values, holds for at most one pair of values of two hidden tokens of
L₁ and L₂ bits has probability at most 2^-(L₁ + L₂); so a point that is jointly injective in two
distinct hidden tokens meets a target that depends on neither with at most that probability.

Theorems `E_two_le`, `point_prob2`: the analogues for two tokens of `E_one_le`, `point_prob`
(Rom/DeferProof_tail.lean; there also `Slot.hid`, `law`). Nothing assumed beyond the hypotheses of
the statements and whatever the arguments hold as proofs.
-/
import Rom.DeferTotal

set_option autoImplicit false

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail2
open DeferTail

variable {S : OSpec}

/-- Two hidden coordinates. -/
theorem E_two_le {ss : List Slot} {t₁ t₂ L₁ L₂ : ℕ} (h₁ : ss[t₁]? = some (Slot.hid L₁))
    (h₂ : ss[t₂]? = some (Slot.hid L₂)) (G : List Bits → Prop)
    (hG : ∀ w : List Bits, w.length = ss.length →
      ∀ (u₁ u₁' : Fin L₁ → Bool) (u₂ u₂' : Fin L₂ → Bool),
        G ((w.set t₁ (List.ofFn u₁)).set t₂ (List.ofFn u₂)) →
        G ((w.set t₁ (List.ofFn u₁')).set t₂ (List.ofFn u₂')) → u₁ = u₁' ∧ u₂ = u₂') :
    expect (law ss) (fun w => ind (G w)) ≤ 1 / 2 ^ (L₁ + L₂) := by
  classical
  have hl₁ : t₁ < ss.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (not_lt.1 hcon)] at h₁
    simp at h₁
  -- some value of the second token serves
  let G₁ : List Bits → Prop := fun w => ∃ u₂ : Fin L₂ → Bool, G (w.set t₂ (List.ofFn u₂))
  have inner : ∀ w ∈ (law ss).support,
      expect (PMF.uniformOfFintype (Fin L₂ → Bool)) (fun u => ind (G (w.set t₂ (List.ofFn u)))) ≤
        1 / 2 ^ L₂ * ind (G₁ w) := by
    intro w hw
    have hl := ((mem_support_law ss w).1 hw).length
    by_cases hg : G₁ w
    · rw [ind_pos hg, mul_one]
      have hw₁ : w.set t₁ (List.ofFn fun i : Fin L₁ => (gv w t₁).getD i false) = w := by
        have hok := ((mem_support_law ss w).1 hw).ok h₁
        obtain ⟨u, hu⟩ := ok_hid hok
        have e : (List.ofFn fun i : Fin L₁ => (gv w t₁).getD i false) = gv w t₁ := by
          rw [← hu]
          congr 1
          funext i
          simp
        rw [e]
        have : gv w t₁ = w[t₁]'(hl ▸ hl₁) := by
          simp [gv, List.getD, List.getElem?_eq_getElem (hl ▸ hl₁)]
        rw [this, List.set_getElem_self]
      have h := pr_unif_le_of_cnt_le (C := Fin L₂ → Bool)
        (P := fun u => G (w.set t₂ (List.ofFn u))) (k := 1)
        (cnt_le_one fun u u' a b =>
          (hG w hl _ _ u u' (by rw [hw₁]; exact a) (by rw [hw₁]; exact b)).2)
      rw [pr_eq_expect] at h
      have e : (fun u : Fin L₂ → Bool => ind (G (w.set t₂ (List.ofFn u)))) =
          fun u =>
            if u ∈ {c : Fin L₂ → Bool | G (w.set t₂ (List.ofFn c))} then (1 : ℝ≥0∞) else 0 := by
        funext u
        by_cases hu : G (w.set t₂ (List.ofFn u))
        · rw [ind_pos hu]; exact (if_pos (show u ∈ {c : Fin L₂ → Bool | G (w.set t₂ (List.ofFn c))} from hu)).symm
        · rw [ind_neg hu]; exact (if_neg (show u ∉ {c : Fin L₂ → Bool | G (w.set t₂ (List.ofFn c))} from hu)).symm
      rw [e]
      simpa using h
    · rw [ind_neg hg, mul_zero]
      refine le_of_eq (expect_ind_false _ _ fun u hu => hg ⟨u, hu⟩)
  rw [E_resample L₂ ss t₂ _ h₂]
  refine (expect_mono_support _ inner).trans ?_
  rw [expect_const_mul]
  have h3 : expect (law ss) (fun w => ind (G₁ w)) ≤ 1 / 2 ^ L₁ := by
    refine E_one_le h₁ G₁ fun w hl u u' a b => ?_
    obtain ⟨x, hx⟩ := a
    obtain ⟨x', hx'⟩ := b
    exact (hG w hl u u' x x' hx hx').1
  calc
    1 / 2 ^ L₂ * expect (law ss) (fun w => ind (G₁ w)) ≤ 1 / 2 ^ L₂ * (1 / 2 ^ L₁) :=
      mul_le_mul' le_rfl h3
    _ = 1 / 2 ^ (L₁ + L₂) := by
      rw [pow_add, one_div, one_div, one_div,
        ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), mul_comm]

/-- a point that is jointly injective in two distinct hidden tokens of L and L' bits meets a target
that depends on neither with probability at most 2^-(L + L') -/
theorem point_prob2 {ss : List Slot} {o : S.ι} (c b : Tok) (pt : Bits → List Bits → S.Dom o)
    (inj2 : ∀ v v' x x', pt v [x] = pt v' [x'] → v = v' ∧ x = x') (hne : c ≠ b) {L L' : ℕ}
    (hc : ss[c]? = some (Slot.hid L)) (hb : ss[b]? = some (Slot.hid L')) (k : List Bits → Pt S)
    (hk : ∀ w v, k (w.set c v) = k w) (hk' : ∀ w v, k (w.set b v) = k w) :
    expect (law ss) (fun w => ind ((⟨o, pt (gv w c) ([b].map (gv w))⟩ : Pt S) = k w)) ≤
      1 / 2 ^ (L + L') := by
  have hcl : c < ss.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (not_lt.1 hcon)] at hc
    simp at hc
  have hbl : b < ss.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (not_lt.1 hcon)] at hb
    simp at hb
  refine E_two_le hc hb _ fun w hl u₁ u₁' u₂ u₂' h1 h2 => ?_
  have e1 : ∀ (x : Bits) (y : Bits), gv ((w.set c x).set b y) c = x := fun x y => by
    rw [gv_set_ne hne.symm, gv_set_same (hl ▸ hcl)]
  have e2 : ∀ (x : Bits) (y : Bits), gv ((w.set c x).set b y) b = y := fun x y =>
    gv_set_same (by rw [List.length_set]; exact hl ▸ hbl) y
  simp only [List.map_cons, List.map_nil, e1, e2, hk, hk'] at h1 h2
  have h3 := h1.trans h2.symm
  have h4 : pt (List.ofFn u₁) [List.ofFn u₂] = pt (List.ofFn u₁') [List.ofFn u₂'] :=
    eq_of_heq (Sigma.mk.inj_iff.1 h3).2
  obtain ⟨a1, a2⟩ := inj2 _ _ _ _ h4
  exact ⟨List.ofFn_injective a1, List.ofFn_injective a2⟩

end DeferTail2
end Rom
