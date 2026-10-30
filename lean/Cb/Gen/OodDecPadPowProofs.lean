-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecPadPowProofs.lean: the proofs of the statements of Cb/Gen/OodDecPadPow.lean (several
sample rows with pads for one vector).

Every theorem here is "name : Cb.Spec.name".
-/
import Cb.Gen.OodDecPadPow
import Cb.Gen.OodDecPadProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood Finset

theorem ood_val_padPow : Spec.ood_val_padPow := by
  intro E μ J₀ P B _ _ _ _ _ _ _ _ pl w b s ρ v i
  classical
  rw [pad_val_raw]
  show ∑ n : J₀ ⊕ Fin s × P,
      (Sum.elim (fun j => eqk (ρ i).1 (pl j))
          (fun n : Fin s × P => if n.1 = i then b (ρ i).2 * w n.2 else 0) n) * v n = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  refine congrArg₂ (· + ·) rfl ?_
  rw [Fintype.sum_prod_type, sum_eq_single i]
  · rw [mul_sum]
    exact sum_congr rfl fun p _ => by rw [if_pos rfl, mul_assoc]; rfl
  · intro i' _ hne
    exact sum_eq_zero fun p _ => by rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

theorem ood_okOn_padPow : Spec.ood_okOn_padPow := by
  intro F E μ J₀ P B _ _ _ _ _ _ _ _ _ _ pl w b s hpl hb hb0 hw v hV hv
  classical
  have h1 := ood_okOn_pad F E μ J₀ P B pl w b hpl hb hw
  have hVi : ∀ i, PadInF F (padBlock i v) := fun i p => hV (i, p)
  show cnt (fun ρ : Fin s → (μ → E) × B => (Sample.padPow E μ J₀ P B pl w b s).val ρ v = 0) ≤
    (Sample.pad E μ J₀ P B pl w b).err ^ s
  refine (cnt_mono
    (Q := fun ρ : Fin s → (μ → E) × B =>
        ∀ i, (Sample.pad E μ J₀ P B pl w b).val (ρ i) (padBlock i v) = 0) fun ρ hρ i =>
          funext fun _ =>
            (ood_val_padPow E μ J₀ P B pl w b s ρ v i).symm.trans (congrFun hρ i)).trans ?_
  rw [cnt_forall_pi (A := fun _ : Fin s => (μ → E) × B) fun i ρi =>
      (Sample.pad E μ J₀ P B pl w b).val ρi (padBlock i v) = 0]
  by_cases ha : (fun j => v (Sum.inl j)) = 0
  · obtain ⟨n, hn⟩ : ∃ n : Fin s × P, v (Sum.inr n) ≠ 0 := by
      by_contra hcon
      refine hv (funext fun x => ?_)
      cases x with
      | inl j => exact congrFun ha j
      | inr n => exact by_contra fun h => hcon ⟨n, h⟩
    refine le_trans (le_of_eq (prod_eq_zero (mem_univ n.1) (cnt_false fun ρi hρi => ?_)))
      (Nat.zero_le _)
    have h2 := (pad_val_raw pl w b ρi (padBlock n.1 v)).symm.trans (congrFun hρi ())
    have h3 : ∑ j, eqk ρi.1 (pl j) * padBlock n.1 v (Sum.inl j) = 0 := sum_eq_zero fun j _ => by
      show eqk ρi.1 (pl j) * v (Sum.inl j) = 0
      rw [congrFun ha j]
      exact mul_zero _
    rw [h3, zero_add] at h2
    have h4 : ∑ p, w p * padBlock n.1 v (Sum.inr p) = 0 :=
      (mul_eq_zero.mp h2).resolve_left (hb0 ρi.2)
    have hV' : ∀ p, ∃ x : F, algebraMap F E x = padBlock n.1 v (Sum.inr p) := hVi n.1
    choose c hc using hV'
    have h5 : padVal w c = 0 := (sum_congr rfl fun p _ => by rw [hc]).trans h4
    have hc0 : c = 0 := hw (h5.trans (padVal_zero w).symm)
    refine hn ?_
    have h6 := hc n.2
    rw [hc0, Pi.zero_apply, map_zero] at h6
    exact h6.symm
  · refine (prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ =>
      h1 (padBlock i v) (hVi i) fun h0 => ha (funext fun j => congrFun h0 (Sum.inl j))).trans ?_
    rw [prod_const, card_univ, Fintype.card_fin]

theorem ood_private_padPow : Spec.ood_private_padPow := by
  intro F E μ J₀ P B _ _ _ _ _ _ _ _ _ _ _ pl w b s hw ρ hρ a
  classical
  let e : (Fin s × P → F) ≃ (Fin s → E) :=
    (Equiv.curry (Fin s) P F).trans
      (Equiv.piCongrRight fun i =>
        (Equiv.ofBijective _ hw).trans
          ((Equiv.mulLeft₀ (b (ρ i).2) (hρ i)).trans
            (Equiv.addLeft (∑ j, eqk (ρ i).1 (pl j) * a j))))
  have hfun : (fun c : Fin s × P → F => (Sample.padPow E μ J₀ P B pl w b s).val ρ (withPad a c)) =
      e := by
    funext c i
    rw [ood_val_padPow, pad_val_raw]
    rfl
  refine (congrArg (fun g => PMF.map g _) hfun).trans ?_
  exact map_unif_equiv_any _ _ e

theorem ood_privateSim_padPow : Spec.ood_privateSim_padPow := by
  intro F E μ J₀ P B _ _ _ _ _ _ _ _ _ _ _ pl w b s hw hb
  exact ood_privateSim F E J₀ (Fin s × P) _ fun ρ _ a =>
    ood_private_padPow F E μ J₀ P B pl w b s hw ρ (fun i => hb (ρ i).2) a

theorem ood_padBasis_one : Spec.ood_padBasis_one := by
  intro E _
  have h : ∀ c : Unit → E, padVal (F := E) (fun _ : Unit => (1 : E)) c = c () := fun c => by
    show ∑ i : Unit, (1 : E) * algebraMap E E (c i) = c ()
    rw [Fintype.sum_unique, one_mul]
    rfl
  exact ⟨fun c c' hc => funext fun _ => (h c).symm.trans (hc.trans (h c')),
    fun x => ⟨fun _ => x, h _⟩⟩

end Cb
