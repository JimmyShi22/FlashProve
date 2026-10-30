-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatProofs.lean: the proofs of the statements of Cb/Ld/LdBat.lean (batching by a zero-evader:
the bounds on the number of bad seeds; the batching inside the existential relaxation).

Named tools: `batGap` (value minus target, for each claim), `bat_holds_iff` (the new claim holds if
and only if the combination of the gaps is 0), `all_iff_gap` (all claims hold if and only if all
gaps are 0), `cnt_bat_at`. Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdBat.lean):
  `ldBat_fwd`: from all claims to the new claim, at every seed.
  `ldBat_cnt_one`, `ldBat_cnt_list`: the bounds on the number of bad seeds.
  `ldBat_slf`: the combination for linear forms.
  `ldBat_ok_line`: the coefficients (1 - ρ, ρ) as a zero-evader.
  `ldBat_ex`: the batching inside the existential relaxation.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBat
import Cb.Ld.LdRelProofs
import Cb.Ld.LdSwitchWordsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

section Tools
variable {E M B D : Type} [Field E] [Fintype B] {S : B → Type}

/-- value minus target -/
def batGap (v : ∀ b, Vf E (S b) M) (x : (B → E) × (∀ b, S b)) (m : M) : B → E := fun b =>
  v b (x.2 b) m - x.1 b

theorem bat_holds_iff (Z : D → B → E) (v : ∀ b, Vf E (S b) M)
    (x : (B → E) × (∀ b, S b)) (m : M) (ρ : D) :
    (Vf.bat Z v).Holds (batNx Z x ρ) m ↔ ∑ b, Z ρ b * batGap v x m b = 0 := by
  have h : ∑ b, Z ρ b * batGap v x m b = ∑ b, Z ρ b * v b (x.2 b) m - ∑ b, Z ρ b * x.1 b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => mul_sub _ _ _
  rw [h, sub_eq_zero]
  exact Iff.rfl

omit [Fintype B] in
theorem all_iff_gap (v : ∀ b, Vf E (S b) M) (x : (B → E) × (∀ b, S b)) (m : M) :
    Vf.All v x m ↔ batGap v x m = 0 :=
  ⟨fun h => funext fun b => sub_eq_zero.2 (h b), fun h b => sub_eq_zero.1 (congrFun h b)⟩

/-- If `Z.OK`, then for one message there are at most err seeds at which the new claim holds though
not all old ones do. -/
theorem cnt_bat_at (Z : Evader E B) (hZ : Z.OK) (v : ∀ b, Vf E (S b) M)
    (x : (B → E) × (∀ b, S b)) (m : M) :
    cnt (fun ρ : Z.D => (Vf.bat Z.ze v).Holds (batNx Z.ze x ρ) m ∧ ¬ Vf.All v x m) ≤ Z.err := by
  by_cases hg : Vf.All v x m
  · rw [cnt_false fun _ h => h.2 hg]
    exact Nat.zero_le _
  · exact (cnt_mono fun ρ h => (bat_holds_iff Z.ze v x m ρ).1 h.1).trans
      (hZ _ fun h0 => hg ((all_iff_gap v x m).2 h0))

end Tools

theorem ldBat_fwd : Spec.ldBat_fwd := by
  intro E M B D _ _ S Z v x m ρ h
  rw [bat_holds_iff, (all_iff_gap v x m).1 h]
  simp

theorem ldBat_cnt_one : Spec.ldBat_cnt_one := by
  intro E M B _ _ S Z v x Q hZ hQ
  by_cases hex : ∃ m, Q m
  · obtain ⟨m₀, h₀⟩ := hex
    refine (cnt_mono fun ρ h => ?_).trans (cnt_bat_at Z hZ v x m₀)
    obtain ⟨m, hm, h1, h2⟩ := h
    rw [hQ m m₀ hm h₀] at h1 h2
    exact ⟨h1, h2⟩
  · rw [cnt_false fun _ h => hex ⟨h.choose, h.choose_spec.1⟩]
    exact Nat.zero_le _

theorem ldBat_cnt_list : Spec.ldBat_cnt_list := by
  intro E M B _ _ _ S Z v x Lst L hZ hL
  exact cnt_exists_list_le Lst L Z.err hL
    (fun m ρ => (Vf.bat Z.ze v).Holds (batNx Z.ze x ρ) m ∧ ¬ Vf.All v x m)
    fun m _ => cnt_bat_at Z hZ v x m

theorem ldBat_slf : Spec.ldBat_slf := by
  intro E J B D _ _ _ S Z sl
  funext x m
  exact ld_slf_bat E J B D S Z sl x m

theorem ldBat_ok_line : Spec.ldBat_ok_line := by
  intro E _ _ v hv
  refine cnt_le_one fun a b ha hb => ?_
  rw [Fintype.sum_bool] at ha hb
  simp only [if_true, Bool.false_eq_true, if_false] at ha hb
  by_contra hab
  have h1 : (a - b) * (v true - v false) = 0 := by linear_combination ha - hb
  have h2 : v true = v false := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hab))
  have h3 : v false = 0 := by rw [h2] at ha; linear_combination ha
  exact hv (funext fun c => by cases c <;> simp [h2, h3])

theorem ldBat_ex : Spec.ldBat_ex := by
  intro E P B Kc _ _ _ _ C S sl Z e L core q hZ hL
  have hval : ∀ (x : E × ((∀ b, S b) × Z.D)) (m : C.J → E),
      (Slf.bat Z.ze sl).Holds x m ↔ (Vf.bat Z.ze fun b => (sl b).val).Holds x m := by
    intro x m
    have h := congrFun (congrFun (ldBat_slf E C.J B Z.D S Z.ze sl) x.2) m
    exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩
  refine pieceTr_of_piece _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w) _ q q
    (piece_draw Kc _ _ C.ext C.N.Wit Z.D (batNx Z.ze) (C.relsAll sl e core)
      (C.rels (Slf.bat Z.ze sl) e core) (L * Z.err) q ?_ (fun _ _ _ h => h) (fun _ => rfl) ?_)
  · intro x y w ρ h
    exact ⟨h.1, (hval _ _).2 (ldBat_fwd E _ B Z.D S Z.ze (fun b => (sl b).val) x w.1 ρ h.2)⟩
  · intro x y _
    have hl : ListLE (fun w : C.N.Wit => C.Near e y (C.enc w.1 w.2)) L :=
      ood_list_of_cnt _ _ L (hL y)
    refine (cnt_mono fun ρ h => ?_).trans
      (cnt_exists_list_le _ L Z.err hl
        (fun (w : C.N.Wit) ρ =>
          (Vf.bat Z.ze fun b => (sl b).val).Holds (batNx Z.ze x ρ) w.1 ∧
          ¬ Vf.All (fun b => (sl b).val) x w.1)
        fun w _ => cnt_bat_at Z hZ _ x w.1)
    obtain ⟨w, hB, hA⟩ := h
    exact ⟨w, hB.1, (hval _ _).1 hB.2, fun hall => hA ⟨hB.1, hall⟩⟩

end Cb
