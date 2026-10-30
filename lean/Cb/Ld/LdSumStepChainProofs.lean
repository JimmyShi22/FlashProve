-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepChainProofs.lean: the proofs of the statements of Cb/Ld/LdSumStepChain.lean (all the
rounds of a fold on words). Nothing is assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
One round: `lds_back` and the union bound over the list. All rounds: induction on the chain, from
the last round to the first.
-/
import Cb.Ld.LdSumStepChain

set_option autoImplicit false

namespace Cb
open Prob LdCode

section
variable (E : Type) [Field E] (P : Type) [Fintype P]

theorem ldh_badAt_cnt [Finite E] : Spec.ldh_badAt_cnt E P := by
  intro D D' H e L bad κ hList Φ Φ' hκ f hbad
  cases nonempty_fintype E
  have h1 : cnt (fun γ => ∃ w : D.MR, (D.Near e f (D.enc w.1 w.2) ∧ ¬ Φ w) ∧ Φ' γ (H.foldW γ w)) ≤
      L * κ :=
    lds_cnt_list E D.MR (fun w => D.Near e f (D.enc w.1 w.2) ∧ ¬ Φ w)
      (fun w γ => Φ' γ (H.foldW γ w)) L κ
      ((cnt_mono fun w hw => hw.1).trans (hList f)) fun w hw => hκ w hw.2
  exact (cnt_le_add fun γ hγ => hγ).trans (Nat.add_le_add hbad h1)

theorem ldh_good : Spec.ldh_good E P := by
  intro D D' H d e hL hd hH he Φ Φ' f γ hbad w' hn hc
  obtain ⟨hnear, hfold⟩ :=
    lds_back E P D D' H d e hL hd hH he f γ (fun hx => hbad (Or.inl hx)) w' hn
  refine ⟨hnear, by_contra fun hΦ => hbad (Or.inr ⟨_, ⟨hnear, hΦ⟩, ?_⟩), hfold⟩
  rw [hfold]
  exact hc

theorem ldh_chain : Spec.ldh_chain E P := by
  intro d e he D D'' c
  induction c with
  | nil D =>
    intro _ cl γ f _ w hn hc
    exact ⟨hn, hc, rfl⟩
  | cons H t ih =>
    intro hOK cl γ f hbad w hn hc
    obtain ⟨hL, hd, hH, ht⟩ := hOK
    have hb1 : ¬ H.BadAt e cl.1 (t.first (cl.2 γ.1)) f γ.1 := fun h => hbad (Or.inl h)
    have hb2 : ¬ t.Bad e (cl.2 γ.1) γ.2 (H.fold γ.1 f) := fun h => hbad (Or.inr h)
    obtain ⟨n1, c1, f1⟩ := ih ht (cl.2 γ.1) γ.2 (H.fold γ.1 f) hb2 w hn hc
    obtain ⟨n0, c0, f0⟩ :=
      ldh_good E P _ _ H d e hL hd hH he cl.1 (t.first (cl.2 γ.1)) f γ.1 hb1 _ n1 c1
    refine ⟨n0, c0, ?_⟩
    show t.foldAllW γ.2 (H.foldW γ.1 (H.back d γ.1 f (t.backAll d γ.2 (H.fold γ.1 f) w))) = w
    rw [f0, f1]

omit [Field E] [Fintype P] in
theorem ldh_endH : Spec.ldh_endH := by
  intro k
  induction k with
  | zero =>
    intro h hk
    show h = 0
    omega
  | succ k ih =>
    intro h hk
    exact ih (h - 1) (by omega)

theorem step_laws (C Z Zw : LdCode E P) (d e : ℕ) (hOK : Spec.CodesOK E P C Z Zw d e) (k h : ℕ) :
    (Halving.step C Z Zw k h).Laws d := by
  cases h with
  | zero => exact lss_stepB_laws E P C Z Zw k 0 d hOK.1.2.1 hOK.1.2.2 hOK.2.1.2.1 hOK.2.1.2.2
  | succ h => exact lss_stepA_laws E P C Z Zw k h d

theorem ldh_stg_ok : Spec.ldh_stg_ok E P := by
  intro C Z Zw d e hOK k
  induction k with
  | zero => exact fun _ => trivial
  | succ k ih =>
    intro h
    exact ⟨lss_stg_laws E P C Z Zw k (h - 1) hOK.1.1 hOK.1.2.1 hOK.1.2.2,
      lss_stg_dist E P C Z Zw k (h - 1) d hOK.2.1.1 hOK.2.1.2.1 hOK.2.1.2.2,
      step_laws E P C Z Zw d e hOK k h,
      ih (h - 1)⟩

theorem ldh_step_cnt [Finite E] : Spec.ldh_step_cnt E P := by
  intro C Z Zw k h d e L b bs bw κ hOK hb hm hList Φ Φ' hκ f
  refine ldh_badAt_cnt E P _ _ (Halving.step C Z Zw k h) e L _ κ hList Φ Φ' hκ f ?_
  obtain ⟨⟨hC, hZ, hW⟩, -, -⟩ := hOK
  cases h with
  | zero =>
    have h1 := ldc_exc_pair_cnt E P _ _ _ _ (Halving.il C (consB k))
      (Halving.idle ((Z.il (Fin 0 → Bool)).pair (Zw.il (Fin 0 → Bool)))) e b 0 f
      (lds_exc_cnt E P _ _ _ e b (ld_laws_il E P C _ hC) hb _)
      (le_of_eq (cnt_false fun γ => lds_exc_idle E P _ e _ γ))
    exact h1
  | succ h =>
    obtain ⟨hbs, hbw⟩ := hm (Nat.succ_pos h)
    have h1 := ldc_exc_pair_cnt E P _ _ _ _ (Halving.il C (consB k))
      ((Halving.il Z (consB h)).pair (Halving.il Zw (consB h))) e b (bs + bw) f
      (lds_exc_cnt E P _ _ _ e b (ld_laws_il E P C _ hC) hb _)
      (ldc_exc_pair_cnt E P _ _ _ _ (Halving.il Z (consB h)) (Halving.il Zw (consB h)) e bs bw _
        (lds_exc_cnt E P _ _ _ e bs (ld_laws_il E P Z _ hZ) hbs _)
        (lds_exc_cnt E P _ _ _ e bw (ld_laws_il E P Zw _ hW) hbw _))
    rw [if_pos (Nat.succ_pos h)]
    exact h1

omit [Field E] in
theorem ldh_rename_near : Spec.ldh_rename_near E P := by
  intro D D' N hN e f w
  have key : ∀ x,
      D.T f x ≠ D.T (D.enc w.1 w.2) x ↔
      D'.T (N.word f) x ≠ D'.T (D'.enc (N.mr w).1 (N.mr w).2) x := by
    intro x
    rw [Ne, Ne, hN.t_iff, hN.enc]
  exact Eq.to_iff (congrArg (fun c => c ≤ e) (cnt_congr key))

omit [Field E] [Fintype P] in
theorem ldh_one_laws : Spec.ldh_one_laws E P := by
  intro C R _ _ u
  refine ⟨fun f g x => ?_, fun _ => rfl, fun w => ?_, fun _ => rfl⟩
  · constructor
    · intro h
      exact funext fun α => congrFun h (u.default, α)
    · intro h
      funext α
      have hα : α = (u.default, α.2) := Prod.ext (u.uniq α.1) rfl
      rw [hα]
      exact congrFun h α.2
  · refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
    · show w.1 (u.default, j.2) = w.1 j
      rw [← u.uniq j.1]
    · show w.2 (u.default, q.2) = w.2 q
      rw [← u.uniq q.1]

omit [Field E] [Fintype P] in
theorem ldh_pair_laws : Spec.ldh_pair_laws E P := by
  intro D₁ D₁' D₂ D₂' N₁ N₂ h₁ h₂
  refine ⟨fun f g x => ?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [t_pair_eq_iff, t_pair_eq_iff, h₁.t_iff, h₂.t_iff]
    exact Iff.rfl
  · funext x α
    cases α with
    | inl α => exact congrFun (congrFun (h₁.enc (fstM w)) x) α
    | inr α => exact congrFun (congrFun (h₂.enc (sndM w)) x) α
  · show mkM (N₁.mrInv (N₁.mr (fstM w))) (N₂.mrInv (N₂.mr (sndM w))) = w
    rw [h₁.left, h₂.left, mkM_fst_snd]
  · show mkM (N₁.mr (N₁.mrInv (fstM w))) (N₂.mr (N₂.mrInv (sndM w))) = w
    rw [h₁.right, h₂.right, mkM_fst_snd]

omit [Field E] [Fintype P] in
theorem ldh_last_laws : Spec.ldh_last_laws E P := fun C Z Zw _ h =>
  ldh_pair_laws E P _ _ _ _ _ _ (ldh_one_laws E P C _ _)
    (ldh_pair_laws E P _ _ _ _ _ _ (ldh_one_laws E P Z _ (uniqRows h))
      (ldh_one_laws E P Zw _ (uniqRows h)))

end
end Cb
