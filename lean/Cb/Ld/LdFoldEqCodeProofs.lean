-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFoldEqCodeProofs.lean: the proofs of the statements of Cb/Ld/LdFoldEqCode.lean (the encoded
index under a code with encoder). No axiom beyond Lean's three, no hypothesis beyond those in the
statements' own text; BCHKS46 is a hypothesis in the text of Spec.ldFc_mca_bchks.
Main names (statements and hypotheses: Cb/Ld/LdFoldEqCode.lean):
  `ldFc_mcaFor_iff`, `ldFc_mca_prox`, `ldFc_mca_third`, `ldFc_mca_bchks`: agreement (`X.MCAeq`)
  `ldFc_list_prox`, `ldFc_list_johnson`, `ldFc_list_unique`: the list
  `ldFc_overF`: words over the small field
  `ldFc_binds`, `ldFc_binds_pad`: the number of seeds with a collision
  `ldFc_cnt_third`, `ldFc_cnt_johnson`: the number of bad points of the fold
Limits: what the head of Cb/Ld/LdFoldEqCode.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFoldEqCode
import Cb.Ld.LdFoldEqProofs
import Cb.Gen.CodeListRows

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

theorem card_cube_unit (j : ℕ) : Nat.card ((Fin j → Bool) × Unit) = 2 ^ j := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_unit, Nat.mul_one]

section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

theorem ldFc_mcaFor_iff : Spec.ldFc_mcaFor_iff F E := by
  intro C₀ R _ e bad
  have key : ∀ (f₀ f₁ : R → Fin C₀.n → E) (θ : E),
      (∃ S : Finset (Fin C₀.n),
        C₀.n ≤ S.card + e ∧
        C₀.OnCode E (fun a j => f₀ a j + θ * f₁ a j) S ∧
        ¬ (C₀.OnCode E f₀ S ∧ C₀.OnCode E f₁ S)) ↔
      (∃ S : Finset (Fin C₀.n),
        Fintype.card (Fin C₀.n) ≤ S.card + e ∧
        (∀ a, f₀ a + θ • f₁ a ∈ Code.agreeOn (C₀.codeE E) S) ∧
        ¬ ((∀ a, f₀ a ∈ Code.agreeOn (C₀.codeE E) S) ∧
          ∀ a, f₁ a ∈ Code.agreeOn (C₀.codeE E) S)) := by
    intro f₀ f₁ θ
    refine exists_congr fun S => ?_
    rw [Fintype.card_fin, C₀.onCode_iff, C₀.onCode_iff, C₀.onCode_iff]
    rfl
  constructor
  · intro h f₀ f₁
    exact (le_of_eq (cnt_congr (key f₀ f₁)).symm).trans (h f₀ f₁)
  · intro h f₀ f₁
    exact (le_of_eq (cnt_congr (key f₀ f₁))).trans (h f₀ f₁)

theorem ldFc_mca_prox : Spec.ldFc_mca_prox F E := by
  intro C₀ hp J _ pl v Z eM rank ok L bad e' hP hok
  refine ldFe_mca_sum (LdIx.ofEnc E C₀ hp pl v Z eM rank) e' (fun j => bad e' (2 ^ j)) fun j _ => ?_
  have h := hP.mca e' hok ((Fin j → Bool) × Unit)
  rw [card_cube_unit] at h
  exact (ldFc_mcaFor_iff F E C₀ _ e' _).mp h

theorem ldFc_mca_third : Spec.ldFc_mca_third F E := by
  intro C₀ hp J _ pl v Z eM rank e' hd h3
  have h := ldFc_mca_prox F E C₀ hp J pl v Z eM rank _ _ _ e' (prox_third F E C₀ hd) h3
  rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at h

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem ldFc_mca_bchks : Spec.ldFc_mca_bchks F E := by
  intro H n k msg r e₀ mca₀ x hx hk hp J _ pl v Z eM rank e' he hJ
  have h := ldFc_mca_prox F E (Code.RS.code x (k + 1) msg r e₀ mca₀) hp J pl v Z eM rank _ _ _ e'
    (rs_prox H F E n k msg r e₀ mca₀ x hx hk) ⟨he, hJ⟩
  rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at h

theorem ldFc_list_prox : Spec.ldFc_list_prox F E := fun _ _ _ _ e' hP hok R _ f =>
  ood_list_of_cnt _ _ _ (hP.list e' hok R f)

omit [Fintype E] in
theorem ldFc_list_johnson : Spec.ldFc_list_johnson F E := fun C₀ e' hd hJ R f S hS => by
  have h := johnson_tables E (Fin C₀.n) (Fin C₀.k) (C₀.GE E) C₀.d e' (HasDist.map (E := E) hd)
    (by rwa [Fintype.card_fin]) R f S hS
  rwa [Fintype.card_fin] at h

omit [Fintype E] in
theorem ldFc_list_unique : Spec.ldFc_list_unique F E := fun _ _ hd h2 _ _ _ hS =>
  Finset.card_le_one.mpr fun _ ha _ hb =>
    DecodesTo.unique (HasDist.map (E := E) hd) h2 (hS _ ha) (hS _ hb)

omit [Fintype E] in
theorem ldFc_overF : Spec.ldFc_overF F E := by
  intro C₀ e hd he R f₀ M h
  have h1 := erase_agr E (Fin C₀.n) (Fin C₀.k) R (C₀.GE E) C₀.d e (HasDist.map (E := E) hd) he _ M h
  have h2 := erase_lift F E (Fin C₀.n) (Fin C₀.k) R C₀.G C₀.d hd
    (agr (C₀.GE E) (fun a => Code.liftWord E (f₀ a)) M) f₀
  have h3 : (erase? C₀.G C₀.d (agr (C₀.GE E) (fun a => Code.liftWord E (f₀ a)) M) f₀).map
        (fun M a => Code.liftWord E (M a)) = some M := h2.symm.trans h1
  obtain ⟨M₀, hM₀, hM⟩ := Option.map_eq_some_iff.mp h3
  refine ⟨M₀, ?_, hM.symm⟩
  exact erase_decodesTo F (Fin C₀.n) (Fin C₀.k) R C₀.G C₀.d e hd _ f₀ M₀ hM₀
    ((decodesTo_iff_agr E _ _ R (C₀.GE E) e _ M).mp h)

omit [Fintype E] in
theorem ldFc_binds : Spec.ldFc_binds F E := by
  intro C₀ hp J₀ P _ _ pl v Z eM rank L f₀ hd he hZ hL
  have hcnt : cnt ((LdIx.ofEnc E C₀ hp pl v Z eM rank).Coll fun a => Code.liftWord E (f₀ a)) ≤
      L.choose 2 * Z.err := by
    refine ood_cnt_clash_on E ((Fin v → Bool) × (J₀ ⊕ P)) (Z.rows (Fin v → Bool))
      (fun u => ∀ a, PadInF F fun j => u (a, j)) _ L (ood_list_view E _ _ _ _ (C₀.GE E) eM _ _ L hL)
      (ood_okOn_rows E (J₀ ⊕ P) (Fin v → Bool) Z (PadInF F) hZ) ?_
    rintro u u' ⟨M, hM, rfl⟩ ⟨M', hM', rfl⟩ a i
    obtain ⟨M₀, -, rfl⟩ := ldFc_overF F E C₀ eM hd he _ f₀ M hM
    obtain ⟨M₀', -, rfl⟩ := ldFc_overF F E C₀ eM hd he _ f₀ M' hM'
    exact ⟨M₀ a (Fin.castLE hp (pl (Sum.inr i))) - M₀' a (Fin.castLE hp (pl (Sum.inr i))),
      map_sub _ _ _⟩
  refine ⟨hcnt, ?_⟩
  have h2 : 2 * L.choose 2 ≤ L ^ 2 := by
    rw [Nat.choose_two_right, sq]
    exact (Nat.mul_div_le _ 2).trans (Nat.mul_le_mul_left L (Nat.sub_le L 1))
  calc 2 * cnt _ ≤ 2 * (L.choose 2 * Z.err) := Nat.mul_le_mul_left 2 hcnt
    _ = (2 * L.choose 2) * Z.err := (Nat.mul_assoc _ _ _).symm
    _ ≤ L ^ 2 * Z.err := Nat.mul_le_mul_right _ h2

theorem ldFc_binds_pad :
    Spec.ldFc_binds_pad F
      E := fun C₀ hp μ J₀ P B _ _ _ _ _ _ pl v plc w b eM rank L f₀ hd he h1 h2 h3 hL =>
  ldFc_binds F E C₀ hp J₀ P pl v _ eM rank L f₀ hd he
    (ood_okOn_pad F E μ J₀ P B plc w b h1 h2 h3) hL

theorem ldFc_cnt_third :
    Spec.ldFc_cnt_third F E := fun C₀ hp J _ pl v Z eM rank e' f rec hd heM he h3 hc =>
  ldFe_cnt (LdIx.ofEnc E C₀ hp pl v Z eM rank) C₀.d e' _ 1 f rec (HasDist.map (E := E) hd) heM he
    (ldFc_mca_third F E C₀ hp J pl v Z eM rank e' hd h3)
    (ldFc_list_unique F E C₀ e' hd (by omega) _ f) hc

theorem ldFc_cnt_johnson :
    Spec.ldFc_cnt_johnson F E := fun C₀ hp _ _ pl v Z eM rank e' bad f rec hd heM he hJ hm hc =>
  ldFe_cnt (LdIx.ofEnc E C₀ hp pl v Z eM rank) C₀.d e' bad _ f rec (HasDist.map (E := E) hd)
    heM he hm (ldFc_list_johnson F E C₀ e' hd hJ _ f) hc

end
end Cb
