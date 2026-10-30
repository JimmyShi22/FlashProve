-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeEraseProofs.lean: the proofs of the statements of Cb/Gen/CodeErase.lean. Nothing is
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

The statements that assume a distance all use one fact: if G has the distance d, two tables of
messages whose codewords agree on more than n - d positions are equal (`agreesOn_unique`; under a
reading: `rd_unique`, from `CodeRep.dist_under'`).
-/
import Cb.Gen.CodeErase
import Cb.Gen.CodeRepProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks

section Mat
variable (E : Type) [Field E]

theorem agreesOn_unique : Spec.agreesOn_unique E := by
  intro ι κ R _ _ G d hd S hS f M M' h h'
  funext a
  by_contra hne
  have h1 := hd.le_cnt_ne hne
  have h2 := cnt_add_card_le (P := fun j => G.mulVec (M a) j ≠ G.mulVec (M' a) j) (S := S)
    (fun j hj hc => hc (by rw [← h j hj a, ← h' j hj a]))
  omega

theorem erase_iff : Spec.erase_iff E := by
  intro ι κ R _ _ G d hd S f M
  constructor
  · intro h
    by_cases hc : Fintype.card ι < S.card + d ∧ ∃ M, AgreesOn G S f M
    · unfold erase? at h
      rw [dif_pos hc] at h
      exact ⟨hc.1, Option.some.inj h ▸ hc.2.choose_spec⟩
    · unfold erase? at h
      rw [dif_neg hc] at h
      cases h
  · rintro ⟨hS, hM⟩
    have hc : Fintype.card ι < S.card + d ∧ ∃ M, AgreesOn G S f M := ⟨hS, M, hM⟩
    unfold erase?
    rw [dif_pos hc]
    exact congrArg some (agreesOn_unique E ι κ R G d hd S hS f _ _ hc.2.choose_spec hM)

theorem erase_none_iff : Spec.erase_none_iff E := by
  intro ι κ R _ _ G d S f
  by_cases hc : Fintype.card ι < S.card + d ∧ ∃ M, AgreesOn G S f M
  · unfold erase?
    rw [dif_pos hc]
    exact ⟨fun h => (by cases h), fun h => absurd hc h⟩
  · unfold erase?
    rw [dif_neg hc]
    exact ⟨fun _ => hc, fun _ => rfl⟩

theorem mem_agr {E ι κ R : Type} [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E)
    (f : R → ι → E) (M : R → κ → E) (j : ι) :
    j ∈ agr G f M ↔ ∀ a, f a j = G.mulVec (M a) j := by
  simp only [agr, Finset.mem_filter, Finset.mem_univ, true_and, not_off_iff]

theorem agreesOn_iff_subset : Spec.agreesOn_iff_subset E := fun _ _ _ _ _ G _ f M =>
  ⟨fun h j hj => (mem_agr G f M j).mpr (h j hj), fun h j hj => (mem_agr G f M j).mp (h hj)⟩

theorem decodesTo_iff_agr : Spec.decodesTo_iff_agr E := by
  intro ι κ R _ _ G e f M
  have h1 := cnt_add_cnt_not (Off G f M)
  have h2 : (agr G f M).card = cnt (fun j => ¬ Off G f M j) := by
    classical
    unfold agr
    convert (cnt_eq_card_filter (fun j => ¬ Off G f M j)).symm
  unfold DecodesTo
  omega

theorem erase_of_subset : Spec.erase_of_subset E := fun ι κ R _ _ G d hd S f M hS hl =>
  (erase_iff E ι κ R G d hd S f M).mpr ⟨hl, (agreesOn_iff_subset E ι κ R G S f M).mpr hS⟩

theorem erase_agr : Spec.erase_agr E := by
  intro ι κ R _ _ G d e hd he f M h
  have h1 := (decodesTo_iff_agr E ι κ R G e f M).mp h
  exact erase_of_subset E ι κ R G d hd _ f M (Finset.Subset.refl _) (by omega)

theorem erase_decodesTo : Spec.erase_decodesTo E := by
  intro ι κ R _ _ G d e hd S f M h hS
  have h1 := (agreesOn_iff_subset E ι κ R G S f M).mp ((erase_iff E ι κ R G d hd S f M).mp h).2
  have h2 := Finset.card_le_card h1
  exact (decodesTo_iff_agr E ι κ R G e f M).mpr (by omega)

theorem erase_combs : Spec.erase_combs E := by
  intro ι κ R R' _ _ _ G d hd S f M c h
  obtain ⟨hl, hM⟩ := (erase_iff E ι κ R G d hd S f M).mp h
  refine (erase_iff E ι κ R' G d hd S _ _).mpr ⟨hl, fun j hj b => ?_⟩
  show (∑ a, c b a • f a) j = G.mulVec (∑ a, c b a • M a) j
  rw [mulVec_comb, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, Pi.smul_apply, hM j hj a]

theorem erase_line : Spec.erase_line E := by
  intro ι κ R _ _ G d hd S f₀ f₁ M₀ M₁ c₀ c₁ h₀ h₁
  obtain ⟨hl, hM₀⟩ := (erase_iff E ι κ R G d hd S f₀ M₀).mp h₀
  obtain ⟨-, hM₁⟩ := (erase_iff E ι κ R G d hd S f₁ M₁).mp h₁
  refine (erase_iff E ι κ R G d hd S _ _).mpr ⟨hl, fun j hj a => ?_⟩
  show (c₀ • f₀ a + c₁ • f₁ a) j = G.mulVec (c₀ • M₀ a + c₁ • M₁ a) j
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.add_apply, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hM₀ j hj a, hM₁ j hj a]

theorem erase_comp : Spec.erase_comp E := by
  intro ι κ R R' _ _ G d hd S f M σ h
  obtain ⟨hl, hM⟩ := (erase_iff E ι κ R G d hd S f M).mp h
  exact (erase_iff E ι κ R' G d hd S _ _).mpr ⟨hl, fun j hj b => hM j hj (σ b)⟩

theorem erase_anti : Spec.erase_anti E := by
  intro ι κ R _ _ G d hd S S' f M hSS hl h
  obtain ⟨-, hM⟩ := (erase_iff E ι κ R G d hd S' f M).mp h
  exact (erase_iff E ι κ R G d hd S f M).mpr ⟨hl, fun j hj a => hM j (hSS hj) a⟩

end Mat

theorem erase_lift : Spec.erase_lift := by
  intro F E _ _ _ ι κ R _ _ G d hd S f
  rcases h : erase? G d S f with _ | M₀
  · rw [Option.map_none]
    rw [erase_none_iff] at h ⊢
    rintro ⟨hl, M, hM⟩
    obtain ⟨φ, hφ⟩ := Code.exists_form_algebraMap F E
    refine h ⟨hl, fun a i => φ (M a i), fun j hj a => ?_⟩
    have h1 := congrArg φ (hM j hj a)
    rw [Code.form_mulVec_map] at h1
    rw [← h1]
    exact (hφ (f a j)).symm
  · rw [Option.map_some]
    obtain ⟨hl, hM⟩ := (erase_iff F ι κ R G d hd S f M₀).mp h
    refine (erase_iff E ι κ R _ d (HasDist.map (E := E) hd) S _ _).mpr ⟨hl, fun j hj a => ?_⟩
    rw [Code.mulVec_map_liftWord]
    exact congrArg (algebraMap F E) (hM j hj a)

section Rd
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
open CodeRep

theorem rd_unique {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {A : Type}
    {C : A → Code.Enc F} {T : Reading C} {D : ℕ} (hT : Spec.RdOK F T D) {R : A → Type}
    {S : Finset T.P} (hS : Fintype.card T.P < S.card + D) {f : ∀ a, R a → Fin (C a).n → E}
    {M M' : ∀ a, R a → Fin (C a).k → E} (h : T.AgreesOn E S f M) (h' : T.AgreesOn E S f M') :
    M = M' := by
  by_contra hne
  have h1 := dist_under' (E := E) hT.1 hT.2.1 hT.2.2 hne
  have h2 := cnt_add_card_le
    (P := fun x =>
        ∃ a r, ((C a).GE E).mulVec (M a r) (T.pos a x) ≠ ((C a).GE E).mulVec (M' a r) (T.pos a x))
    (S := S) (fun x hx ⟨a, r, hc⟩ => hc (by rw [← h x hx a r, ← h' x hx a r]))
  omega

theorem rd_erase_iff : Spec.rd_erase_iff F E := by
  intro A C T D hT R S f M
  constructor
  · intro h
    by_cases hc : Fintype.card T.P < S.card + D ∧ ∃ M, T.AgreesOn E S f M
    · unfold Reading.erase? at h
      rw [dif_pos hc] at h
      exact ⟨hc.1, Option.some.inj h ▸ hc.2.choose_spec⟩
    · unfold Reading.erase? at h
      rw [dif_neg hc] at h
      cases h
  · rintro ⟨hS, hM⟩
    have hc : Fintype.card T.P < S.card + D ∧ ∃ M, T.AgreesOn E S f M := ⟨hS, M, hM⟩
    unfold Reading.erase?
    rw [dif_pos hc]
    exact congrArg some (rd_unique hT hS hc.2.choose_spec hM)

theorem rd_mem_agr {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {A : Type}
    {C : A → Code.Enc F} (T : Reading C) {R : A → Type} (f : ∀ a, R a → Fin (C a).n → E)
    (M : ∀ a, R a → Fin (C a).k → E) (x : T.P) :
    x ∈ T.agr E f M ↔ ∀ a r, f a r (T.pos a x) = ((C a).GE E).mulVec (M a r) (T.pos a x) := by
  simp only [Reading.agr, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a r
    by_contra hc
    exact h ⟨a, r, hc⟩
  · exact fun h ⟨a, r, hc⟩ => hc (h a r)

theorem rd_decodesTo_iff_agr : Spec.rd_decodesTo_iff_agr F E := by
  intro A C T R e f M
  have h1 := cnt_add_cnt_not (T.Off E f M)
  have h2 : (T.agr E f M).card = cnt (fun x => ¬ T.Off E f M x) := by
    classical
    unfold Reading.agr
    convert (cnt_eq_card_filter (fun x => ¬ T.Off E f M x)).symm
  unfold Reading.DecodesTo
  omega

theorem rd_erase_agr : Spec.rd_erase_agr F E := by
  intro A C T D e hT he R f M h
  have h1 := (rd_decodesTo_iff_agr F E A C T R e f M).mp h
  exact (rd_erase_iff F E A C T D hT R _ f M).mpr ⟨by omega, fun x hx => (rd_mem_agr T f M x).mp hx⟩

theorem rd_erase_decodesTo : Spec.rd_erase_decodesTo F E := by
  intro A C T D e hT R S f M h hS
  have h1 := ((rd_erase_iff F E A C T D hT R S f M).mp h).2
  have h2 : S ⊆ T.agr E f M := fun x hx => (rd_mem_agr T f M x).mpr (h1 x hx)
  have h3 := Finset.card_le_card h2
  exact (rd_decodesTo_iff_agr F E A C T R e f M).mpr (by omega)

theorem rd_erase_line : Spec.rd_erase_line F E := by
  intro A C T D hT R S f₀ f₁ M₀ M₁ c₀ c₁ h₀ h₁
  obtain ⟨hl, hM₀⟩ := (rd_erase_iff F E A C T D hT R S f₀ M₀).mp h₀
  obtain ⟨-, hM₁⟩ := (rd_erase_iff F E A C T D hT R S f₁ M₁).mp h₁
  refine (rd_erase_iff F E A C T D hT R S _ _).mpr ⟨hl, fun x hx a r => ?_⟩
  show (c₀ • f₀ a r + c₁ • f₁ a r) (T.pos a x) =
    ((C a).GE E).mulVec (c₀ • M₀ a r + c₁ • M₁ a r) (T.pos a x)
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.add_apply, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hM₀ x hx a r, hM₁ x hx a r]

theorem rd_erase_comps : Spec.rd_erase_comps F E := by
  intro A C T D hT R S hS f M
  have hlarge : ∀ a, Fintype.card (Fin (C a).n) < (S.image (T.pos a)).card + (C a).d := by
    intro a
    have h0 := Finset.card_le_univ S
    have h1 := image_large hT.1 (e := Fintype.card T.P - S.card) (S := S) (by omega) a
    have h2 : (Fintype.card T.P - S.card) / T.mult a < (C a).d :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_le (by omega) (hT.2.2 a))
    rw [Fintype.card_fin]
    omega
  rw [rd_erase_iff F E A C T D hT R S f M]
  constructor
  · rintro ⟨-, h⟩ a
    refine (erase_iff E _ _ _ _ _ (HasDist.map (E := E) (hT.2.1 a)) _ _ _).mpr
      ⟨hlarge a, fun j hj r => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
    exact h x hx a r
  · intro h
    refine ⟨hS, fun x hx a r => ?_⟩
    exact ((erase_iff E _ _ _ _ _ (HasDist.map (E := E) (hT.2.1 a)) _ _ _).mp (h a)).2
      _ (Finset.mem_image_of_mem _ hx) r

theorem rd_erase_one : Spec.rd_erase_one F E := by
  intro C₀ hd R₀ S f M
  have hT : Spec.RdOK F (Reading.one C₀) C₀.d :=
    ⟨one_even F C₀, fun _ => hd, fun _ => le_of_eq (Nat.one_mul _).symm⟩
  rw [rd_erase_iff F E Unit _ (Reading.one C₀) C₀.d hT (fun _ => R₀) S (fun _ => f) (fun _ => M)]
  refine Iff.trans ?_ (erase_iff E _ _ _ (C₀.GE E) C₀.d (HasDist.map (E := E) hd) S f M).symm
  exact and_congr Iff.rfl ⟨fun h j hj a => h j hj () a, fun h j hj _ a => h j hj a⟩

end Rd
end Cb
