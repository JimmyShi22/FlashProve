-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldSwProofs.lean: the proofs of the statements of Cb/Ld/LdBldSw.lean (the parts of a code
switch, built from numbers: the pad with filler entries (told under "Why:" in that head), the
placing, the sample, the zero-evader of the batching). Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.

How: `bldSw_fill`: the property of a zero-evader goes along the re-bracketing; privacy: seed by
seed, draw the filler entries first: for each of their values the pad alone makes the answer
uniform.
Limits: what the head of Cb/Ld/LdBldSw.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldSw
import Cb.Gen.OodDecPadProofs
import Cb.Gen.OodDecPadPowProofs
import Cb.Gen.OodDecSendProofs
import Prob.LawKit

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood Cb.Bld

theorem bldSw_pad_one : Spec.bldSw_pad_one := by
  rintro E J₀ P _ _ _ Z ⟨μ, B, _, _, _, _, pl, w, b, -, -, -, hw, -⟩
  classical
  have h1 : Fintype.card (P → E) = Fintype.card E := Fintype.card_of_bijective hw
  rw [Fintype.card_fun] at h1
  exact Nat.pow_right_injective
    (Fintype.one_lt_card : 1 < Fintype.card E) (h1.trans (pow_one _).symm)

theorem bldSw_of_pad : Spec.bldSw_of_pad := by
  rintro E J₀ P _ _ _ Z ⟨μ, B, i1, i2, i3, i4, pl, w, b, rfl, hpl, hb, hw, h0⟩
  refine ⟨Empty, P, μ, B, inferInstance, i1, i2, i3, i4, (Equiv.emptySum Empty P).symm,
    Sum.elim pl fun e => e.elim, w, b, ?_, ?_, hb, hw, h0⟩
  · show Sample.mk _ _ _ _ = Sample.mk _ _ _ _
    congr 1
    funext ρ s j
    rcases j with j | j <;> rfl
  · rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (hpl h)
    · exact y.elim
    · exact x.elim
    · exact x.elim

/-- the entries of a vector with pad, after the re-bracketing -/
theorem Ood.fillBr_withPad {E J₀ Qo Fl P : Type} [Field E] (σ : Qo ≃ Fl ⊕ P)
    (a : J₀ → E) (c : Qo → E) :
    (fun j => withPad (F := E) a c ((fillBr σ).symm j)) =
      withPad (F := E) (Sum.elim a fun f => c (σ.symm (Sum.inl f))) fun p =>
        c (σ.symm (Sum.inr p)) := by
  funext j
  rcases j with (j | f) | p <;> rfl

theorem bldSw_fill : Spec.bldSw_fill := by
  rintro E J₀ Qo _ _ _ _ Z ⟨Fl, P, μ, B, _, _, _, _, _, σ, pl, w, b, rfl, hpl, hb, hw, h0⟩
  classical
  haveI : Fintype Fl :=
    Fintype.ofInjective (fun f => σ.symm (Sum.inl f)) fun x y h => Sum.inl.inj (σ.symm.injective h)
  refine ⟨fun v hv => ?_, ?_⟩
  · have h1 := ood_okOn_comap E _ _ (Sample.pad E μ (J₀ ⊕ Fl) P B pl w b) (fillBr σ) (PadInF E)
      (ood_okOn_pad E E μ _ _ B pl w b hpl hb hw.1)
    exact h1 v (fun _ => ⟨_, rfl⟩) hv
  · refine ood_privateSim E E J₀ Qo _ fun ρ _ a => ?_
    let ε : (Qo → E) ≃ (Fl → E) × (P → E) :=
      (Equiv.arrowCongr σ (Equiv.refl E)).trans (Equiv.sumArrowEquivProdArrow Fl P E)
    have hf : (fun c : Qo → E =>
          ((Sample.pad E μ (J₀ ⊕ Fl) P B pl w b).comap (fillBr σ)).val ρ (withPad a c)) =
        (fun x : (Fl → E) × (P → E) =>
            (Sample.pad E μ (J₀ ⊕ Fl) P B pl w b).val ρ (withPad (Sum.elim a x.1) x.2)) ∘ ε := by
      funext c
      rw [ood_val_comap E _ _ (Sample.pad E μ (J₀ ⊕ Fl) P B pl w b) (fillBr σ) ρ, fillBr_withPad]
      rfl
    rw [hf, ← PMF.map_comp, map_unif_equiv ε, map_unif_prod]
    refine Eq.trans
      (congrArg (PMF.bind (unif (Fl → E)))
        (funext fun x => ood_private_pad E E μ (J₀ ⊕ Fl) P B pl w b hw ρ (h0 ρ.2) (Sum.elim a x)))
      ?_
    exact PMF.bind_const _ _

theorem Bld.swIn_inj {J₀ Fl : Type} : Function.Injective (swIn : J₀ ⊕ Fl → J₀ ⊕ (Fl ⊕ Unit)) := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · cases h
  · cases h
  · exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj h))

open Classical in
theorem bldSw_zo : Spec.bldSw_zo := fun E _ Fl _ _ _ place mv cor hc =>
  ⟨Fl, Unit, Fin mv, Eˣ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, Equiv.refl _, fun n => cor (place (swIn n)), fun _ => 1,
    Units.val, rfl, fun _ _ h => swIn_inj (place.injective (hc h)),
    Units.val_injective, ood_padBasis_one E, fun β => β.ne_zero⟩

theorem bldSw_zb : Spec.bldSw_zb := fun _ _ _ _ gb num hn =>
  Evader.Form.comap _ num hn (Evader.Form.eqPt (Fin gb))

open Classical in
theorem bldSw_fix : Spec.bldSw_fix := by
  intro E J₀ Fl Jn _ _ _ _ place mv cor ρ a x
  obtain ⟨z, β⟩ : (Fin mv → E) × Eˣ := ρ
  have key : ∀ c : E, (swZo E place mv cor).val (z, β) (Sum.elim a (Sum.elim x fun _ => c)) ()
      = Alg.mle (placed (fun n => cor (place (swIn n))) (Sum.elim a x)) z + (β : E) * c := by
    intro c
    have e1 := congrFun
      (ood_val_comap E _ _
        (Sample.pad E (Fin mv) (J₀ ⊕ Fl) Unit Eˣ
          (fun n => cor (place (swIn n))) (fun _ => 1) Units.val)
        (fillBr (Equiv.refl (Fl ⊕ Unit))) (z, β) (Sum.elim a (Sum.elim x fun _ => c))) ()
    have e2 : (fun j =>
          (Sum.elim a (Sum.elim x fun _ => c) : J₀ ⊕ (Fl ⊕ Unit) → E)
            ((fillBr (Equiv.refl (Fl ⊕ Unit))).symm j)) =
        Sum.elim (Sum.elim a x) fun _ => c := by
      funext j
      rcases j with (j | f) | u <;> rfl
    rw [e2, ood_val_pad] at e1
    refine e1.trans ?_
    have e3 : (fun j => (Sum.elim (Sum.elim a x) fun _ => c : (J₀ ⊕ Fl) ⊕ Unit → E) (Sum.inl j)) =
        Sum.elim a x := rfl
    rw [e3]
    simp
  have hf : (fun c : E =>
        (swZo E place mv cor).val (z, β) (Sum.elim a (Sum.elim x fun _ => c)) ()) =
      ((Equiv.mulLeft₀ (β : E) β.ne_zero).trans
        (Equiv.addLeft (Alg.mle (placed (fun n => cor (place (swIn n))) (Sum.elim a x)) z))) := by
    funext c
    exact key c
  rw [hf]
  exact Equiv.bijective _

open Classical in
theorem bldSw_nums : Spec.bldSw_nums := by
  intro E J₀ Fl Jn R _ _ place mv cor gb num
  refine ⟨?_, ?_, ?_, ?_⟩
  · show max
        (Fintype.card (Fin mv) * Fintype.card E ^ (Fintype.card (Fin mv) - 1) * Fintype.card Eˣ)
        (Fintype.card E ^ Fintype.card (Fin mv)) = _
    rw [Fintype.card_fin, Fintype.card_units]
  · show Fintype.card ((Fin mv → E) × Eˣ) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_units]
  · show Fintype.card (Fin gb) * Fintype.card E ^ (Fintype.card (Fin gb) - 1) = _
    rw [Fintype.card_fin]
  · show Fintype.card (Fin gb → E) = _
    rw [Fintype.card_fun, Fintype.card_fin]

theorem bldSw_frac : Spec.bldSw_frac := by
  intro E J₀ Fl Jn R _ _ place mv cor gb num
  obtain ⟨h1, h2, h3, h4⟩ := bldSw_nums E J₀ Fl Jn R place mv cor gb num
  have hq : 1 < Fintype.card E := Fintype.one_lt_card
  rw [h1, h2, h3, h4]
  generalize Fintype.card E = q at hq
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hp : 1 ≤ p := by omega
  rw [Nat.add_sub_cancel]
  refine ⟨fun hm => ?_, fun hg => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, mv = n + 1 := ⟨mv - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    rw [Nat.add_sub_cancel]
    have hle : (p + 1) ^ (n + 1) ≤ (n + 1) * (p + 1) ^ n * p := by
      have h5 : p + 1 ≤ (n + 1) * p := by nlinarith
      calc (p + 1) ^ (n + 1) = (p + 1) ^ n * (p + 1) := pow_succ _ _
        _ ≤ (p + 1) ^ n * ((n + 1) * p) := Nat.mul_le_mul_left _ h5
        _ = (n + 1) * (p + 1) ^ n * p := by ring
    rw [max_eq_left hle]
    ring
  · obtain ⟨n, rfl⟩ : ∃ n, gb = n + 1 := ⟨gb - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring

theorem bldSw_cor : Spec.bldSw_cor := by
  intro J _ mv h x y hxy
  have hx : (Fintype.equivFin J x).val < 2 ^ mv := lt_of_lt_of_le (Fintype.equivFin J x).2 h
  have hy : (Fintype.equivFin J y).val < 2 ^ mv := lt_of_lt_of_le (Fintype.equivFin J y).2 h
  have e : (Fintype.equivFin J x).val = (Fintype.equivFin J y).val := by
    rw [← Alg.num_bits hx, ← Alg.num_bits hy]
    exact congrArg Alg.num hxy
  exact (Fintype.equivFin J).injective (Fin.ext e)

theorem bldSw_sw : Spec.bldSw_sw := by
  intro E P P' _ _ _ _ Y _ Cnew Fl _ _ place mv cor ts gb num hc hn e
  have hF : (swZo E place mv cor).PadFillForm := bldSw_zo E _ Fl _ place mv cor hc
  have hB : (swZb E gb num).Form := bldSw_zb E _ gb num hn
  have hO := bldSw_fill E _ _ _ hF
  exact ⟨hO.1, evForm_ok E _ _ hB, hO.2, hF, hB⟩

end Cb
