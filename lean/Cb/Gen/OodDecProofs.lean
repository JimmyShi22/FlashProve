-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecProofs.lean: the proofs of the statements of Cb/Gen/OodDec.lean (decoding beyond half
the distance, with samples of the message).

The theorems are "ood_* : Cb.Spec.ood_*"; `Ood.Sample.val_sub` and `Ood.exists_several_iff` are
auxiliary. The one proof with content is `ood_cnt_clash`: the list is finite, a bad seed is bad for
one of its at most (L choose 2) two-element subsets, and each of these has at most k bad seeds.
-/
import Cb.Gen.OodDec
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

theorem ood_pick_iff : Spec.ood_pick_iff := by
  intro U D Y Lst ev ρ y u
  unfold pick
  by_cases h : ∃ u, Cand Lst ev ρ y u
  · by_cases hc : Coll Lst ev ρ y
    · rw [dif_pos h, if_pos hc]
      refine ⟨(fun h0 => nomatch h0), ?_⟩
      rintro ⟨_, huniq⟩
      obtain ⟨a, b, hne, ha, hb⟩ := hc
      exact absurd ((huniq a ha).trans (huniq b hb).symm) hne
    · rw [dif_pos h, if_neg hc]
      constructor
      · intro h0
        have hs : Cand Lst ev ρ y h.choose := h.choose_spec
        rw [Val.one.inj h0] at hs
        exact ⟨hs, fun u' hu' => by_contra fun hne => hc ⟨u', u, hne, hu', hs⟩⟩
      · rintro ⟨_, huniq⟩
        exact congrArg Val.one (huniq _ h.choose_spec)
  · rw [dif_neg h]
    exact ⟨(fun h0 => nomatch h0), fun h0 => absurd ⟨u, h0.1⟩ h⟩

theorem ood_pick_none_iff : Spec.ood_pick_none_iff := by
  intro U D Y Lst ev ρ y
  unfold pick
  by_cases h : ∃ u, Cand Lst ev ρ y u
  · rw [dif_pos h]
    refine ⟨fun h0 => ?_, fun h0 => absurd h.choose_spec (h0 _)⟩
    by_cases hc : Coll Lst ev ρ y
    · rw [if_pos hc] at h0
      exact nomatch h0
    · rw [if_neg hc] at h0
      exact nomatch h0
  · rw [dif_neg h]
    exact ⟨fun _ u hu => h ⟨u, hu⟩, fun _ => rfl⟩

theorem ood_pick_several_iff : Spec.ood_pick_several_iff := by
  intro U D Y Lst ev ρ y
  unfold pick
  by_cases h : ∃ u, Cand Lst ev ρ y u
  · by_cases hc : Coll Lst ev ρ y
    · rw [dif_pos h, if_pos hc]
      exact ⟨fun _ => hc, fun _ => rfl⟩
    · rw [dif_pos h, if_neg hc]
      exact ⟨(fun h0 => nomatch h0), fun h0 => absurd h0 hc⟩
  · rw [dif_neg h]
    exact ⟨(fun h0 => nomatch h0), fun ⟨u, _, _, hu, _⟩ => absurd ⟨u, hu⟩ h⟩

theorem ood_pick_good : Spec.ood_pick_good := by
  intro U D Y Lst ev ρ hcl y u
  exact (ood_pick_iff U D Y Lst ev ρ y u).trans ⟨fun h => h.1,
    fun h =>
      ⟨h, fun u' hu' => by_contra fun hne => hcl ⟨u', u, hu'.1, h.1, hne, hu'.2.trans h.2.symm⟩⟩⟩

theorem ood_clash_iff : Spec.ood_clash_iff := by
  intro U D Y Lst ev ρ
  constructor
  · rintro ⟨u, u', hu, hu', hne, he⟩
    exact ⟨ev ρ u, u, u', hne, ⟨hu, rfl⟩, ⟨hu', he.symm⟩⟩
  · rintro ⟨y, u, u', hne, hu, hu'⟩
    exact ⟨u, u', hu.1, hu'.1, hne, hu.2.trans hu'.2.symm⟩

theorem ood_cnt_clash : Spec.ood_cnt_clash := by
  intro U D Y _ Lst ev L k hL hk
  classical
  have hfin : {u | Lst u}.Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (L + 1)
    have := hL S fun u hu => hS (Finset.mem_coe.mpr hu)
    omega
  have hmem : ∀ u, u ∈ hfin.toFinset ↔ Lst u := fun u => hfin.mem_toFinset
  have hScard : hfin.toFinset.card ≤ L := hL _ fun u hu => (hmem u).mp hu
  have hp : ∀ p ∈ hfin.toFinset.powersetCard 2,
      cnt (fun ρ => ∃ u u', p = {u, u'} ∧ u ≠ u' ∧ ev ρ u = ev ρ u') ≤ k := by
    intro p hp
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hp
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha : Lst a := (hmem a).mp (hsub (by simp))
    have hb : Lst b := (hmem b).mp (hsub (by simp))
    refine (cnt_mono fun ρ => ?_).trans (hk a b ha hb hab)
    rintro ⟨u, u', hpe, hne, he⟩
    have hu : u ∈ ({a, b} : Finset U) := by rw [hpe]; simp
    have hu' : u' ∈ ({a, b} : Finset U) := by rw [hpe]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with h1 | h1 <;> rcases hu' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [← h1, ← h2]; exact he
    · rw [← h1, ← h2]; exact he.symm
    · exact absurd (h1.trans h2.symm) hne
  have h1 : cnt (Clash Lst ev) ≤
      cnt (fun ρ =>
        ∃ p ∈ hfin.toFinset.powersetCard 2, ∃ u u', p = {u, u'} ∧ u ≠ u' ∧ ev ρ u = ev ρ u') := by
    refine cnt_mono fun ρ => ?_
    rintro ⟨u, u', hu, hu', hne, he⟩
    refine ⟨{u, u'}, Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, Finset.card_pair hne⟩, u, u', rfl,
      hne, he⟩
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]; exact (hmem _).mpr hu
    · rw [Finset.mem_singleton.mp hx]; exact (hmem _).mpr hu'
  refine h1.trans ((cnt_exists_mem_le _ _).trans ((Finset.sum_le_sum hp).trans ?_))
  rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  exact Nat.mul_le_mul_right k (Nat.choose_le_choose 2 hScard)

/-- The answers of a difference of vectors are the difference of the answers. -/
theorem Ood.Sample.val_sub {E J : Type} [Field E] [Fintype J] (Z : Sample E J)
    (ρ : Z.D) (u u' : J → E) :
    Z.val ρ (u - u') = Z.val ρ u - Z.val ρ u' := by
  funext s
  simp only [Sample.val, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ood_cnt_clash_sample : Spec.ood_cnt_clash_sample := by
  intro E J _ _ Z Lst L hL hZ
  refine ood_cnt_clash (J → E) Z.D (Z.S → E) Lst Z.val L Z.err hL fun u u' _ _ hne => ?_
  refine (cnt_mono fun ρ hρ => ?_).trans (hZ (u - u') (sub_ne_zero.mpr hne))
  rw [Sample.val_sub, hρ, sub_self]

theorem ood_cnt_clash_sq : Spec.ood_cnt_clash_sq := by
  intro E J _ _ Z Lst L hL hZ
  have h := ood_cnt_clash_sample E J Z Lst L hL hZ
  have h2 : 2 * L.choose 2 ≤ L ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (L * (L - 1) / 2) ≤ L * (L - 1) := Nat.mul_div_le _ _
      _ ≤ L * L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = L ^ 2 := (sq L).symm
  calc 2 * cnt (Clash Lst Z.val) ≤ 2 * (L.choose 2 * Z.err) := Nat.mul_le_mul_left _ h
    _ = (2 * L.choose 2) * Z.err := (Nat.mul_assoc _ _ _).symm
    _ ≤ L ^ 2 * Z.err := Nat.mul_le_mul_right _ h2

/-- Auxiliary: "some answer gets the value several" is `Clash`. -/
theorem Ood.exists_several_iff {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ : D) :
    (∃ y, pick Lst ev ρ y = .several) ↔ Clash Lst ev ρ :=
  ((ood_clash_iff U D Y Lst ev ρ).trans
    (exists_congr fun y => (ood_pick_several_iff U D Y Lst ev ρ y).symm)).symm

theorem ood_cnt_several : Spec.ood_cnt_several := by
  intro E J _ _ Z Lst L hL hZ
  rw [cnt_congr (Q := Clash Lst Z.val) fun ρ => exists_several_iff Lst Z.val ρ]
  exact ⟨ood_cnt_clash_sample E J Z Lst L hL hZ, ood_cnt_clash_sq E J Z Lst L hL hZ⟩

theorem ood_list_mono : Spec.ood_list_mono := fun _ _ _ _ hsub hL S hS =>
  hL S fun u hu => hsub u (hS u hu)

theorem ood_list_image : Spec.ood_list_image := by
  intro T U P view L hL S hS
  classical
  rcases isEmpty_or_nonempty T with hT | hT
  · rcases S.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · simp
    · obtain ⟨t, _⟩ := hS u hu
      exact hT.elim t
  choose! g hg using hS
  have hinj : Set.InjOn g S := fun u hu u' hu' h =>
    (hg u (Finset.mem_coe.mp hu)).2.symm.trans
      ((congrArg view h).trans (hg u' (Finset.mem_coe.mp hu')).2)
  rw [← Finset.card_image_of_injOn hinj]
  refine hL _ fun t ht => ?_
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  exact (hg u hu).1

theorem ood_list_pi : Spec.ood_list_pi := by
  intro A _ _ T P L hL S hS
  classical
  have hsub : S ⊆ Fintype.piFinset fun a => S.image fun t => t a := fun t ht =>
    Fintype.mem_piFinset.mpr fun a => Finset.mem_image_of_mem _ ht
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => hL a _ fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  exact hS t ht a

theorem ood_list_of_cnt : Spec.ood_list_of_cnt := fun _ _ _ _ h S hS => (card_le_cnt S hS).trans h

theorem ood_ok_one : Spec.ood_ok_one := by
  intro E J _ _ Z hZ v hv
  exact (cnt_mono fun ρ hρ => congrFun hρ ()).trans (hZ v hv)

theorem ood_ok_pow : Spec.ood_ok_pow := by
  intro E J _ _ Z s hZ v hv
  show cnt (fun ρ : Fin s → Z.D => (Sample.pow Z s).val ρ v = 0) ≤ Z.err ^ s
  refine (cnt_mono (Q := fun ρ : Fin s → Z.D => ∀ i, ∑ j, Z.ze (ρ i) j * v j = 0)
    fun ρ hρ i => congrFun hρ i).trans ?_
  rw [cnt_forall_pow (fun ρ : Z.D => ∑ j, Z.ze ρ j * v j = 0) s]
  exact Nat.pow_le_pow_left (hZ v hv) s

theorem ood_decS_iff : Spec.ood_decS_iff := by
  intro E ι κ R J _ _ _ _ G e view Z f ρ y u
  refine (ood_pick_iff _ _ _ (InList G e view f) Z.val ρ y u).trans ⟨fun h =>
      ⟨h.1.1, h.1.2, fun M' h1 h2 => h.2 _ ⟨⟨M', h1, rfl⟩, h2⟩⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, ?_⟩⟩
  rintro u' ⟨⟨M', h1, rfl⟩, h2⟩
  exact h.2.2 M' h1 h2

theorem ood_decS_good : Spec.ood_decS_good := by
  intro E ι κ R J _ _ _ _ G e view Z f ρ hcl y u
  exact ood_pick_good _ _ _ (InList G e view f) Z.val ρ hcl y u

theorem ood_lt_cnt_off : Spec.ood_lt_cnt_off := by
  intro E ι κ R J _ _ _ _ G e view Z f ρ hcl M hne
  exact not_le.mp fun hc =>
    hne ((ood_decS_good E ι κ R J G e view Z f ρ hcl _ _).mpr ⟨⟨M, hc, rfl⟩, rfl⟩)

theorem ood_list_view : Spec.ood_list_view := by
  intro E ι κ R J _ _ _ G e view f L hL
  exact ood_list_image _ _ (DecodesTo G e f) view L hL

theorem ood_cnt_clashS : Spec.ood_cnt_clashS := by
  intro E ι κ R J _ _ _ _ G e view Z f L hL hZ
  exact ood_cnt_clash_sample
    E J Z (InList G e view f) L (ood_list_view E ι κ R J G e view f L hL) hZ

theorem ood_cnt_severalS : Spec.ood_cnt_severalS := by
  intro E ι κ R J _ _ _ _ G e view Z f L hL hZ
  exact ood_cnt_several E J Z (InList G e view f) L (ood_list_view E ι κ R J G e view f L hL) hZ

theorem ood_main : Spec.ood_main := by
  intro E ι κ R J _ _ _ _ G e view Z f L hL hZ
  refine (cnt_mono fun ρ => ?_).trans (ood_cnt_clashS E ι κ R J G e view Z f L hL hZ)
  rintro ⟨y, M, hM, hy, hne⟩
  by_contra hcl
  exact hne ((ood_decS_good E ι κ R J G e view Z f ρ hcl y (view M)).mpr ⟨⟨M, hM, rfl⟩, hy⟩)

theorem ood_decS_near : Spec.ood_decS_near := by
  intro E ι κ R J _ _ _ _ G d e e' view Z f M hd he hee hM ρ
  exact (ood_decS_iff E ι κ R J G e view Z f ρ _ _).mpr
    ⟨⟨M, hM.mono he, rfl⟩,
      rfl,
      fun M' h1 _ => congrArg view (funext fun _ => DecodesTo.row_unique hd hee h1 hM rfl)⟩

theorem ood_decS_mulVec : Spec.ood_decS_mulVec := by
  intro E ι κ R J _ _ _ _ G d e view Z M hd he ρ
  exact ood_decS_near E ι κ R J G d e 0 view Z _ M hd (Nat.zero_le e) (by omega)
    (decodesTo_mulVec G 0 M) ρ

theorem ood_decS_imp : Spec.ood_decS_imp := by
  intro E ι κ R R' J _ _ _ _ G e view Z f M f' M' hM himp ρ hcl
  exact (ood_decS_good E ι κ R' J G e view Z f' ρ hcl _ _).mpr ⟨⟨M', hM.of_imp himp, rfl⟩, rfl⟩

theorem ood_decS_comp : Spec.ood_decS_comp := by
  intro E ι κ R R' J _ _ _ _ G e view Z f M σ hM ρ hcl
  exact (ood_decS_good E ι κ R' J G e view Z _ ρ hcl _ _).mpr ⟨⟨_, hM.comp σ, rfl⟩, rfl⟩

theorem ood_decS_combs : Spec.ood_decS_combs := by
  intro E ι κ R R' J _ _ _ _ _ G e view Z f M c hM ρ hcl
  exact (ood_decS_good E ι κ R' J G e view Z _ ρ hcl _ _).mpr ⟨⟨_, hM.combs c, rfl⟩, rfl⟩

theorem ood_decS_unique : Spec.ood_decS_unique := by
  intro E ι κ R J _ _ _ _ G d e view Z f ρ y u hd h2
  refine ⟨(ood_decS_iff E ι κ R J G e view Z f ρ y u).trans ⟨?_, ?_⟩, fun hs => ?_⟩
  · rintro ⟨⟨M, hM, hu⟩, hy, _⟩
    exact ⟨⟨M, hM⟩, by rw [hM.dec_eq hd h2]; exact hu, hy⟩
  · rintro ⟨hdec, hu, hy⟩
    refine ⟨⟨_, hdec.decodesTo_dec, hu⟩, hy, fun M' h1 _ => ?_⟩
    rw [← hu, h1.dec_eq hd h2]
  · obtain ⟨u₁, u₂, hne, ⟨⟨M₁, h1, rfl⟩, _⟩, ⟨⟨M₂, h2', rfl⟩, _⟩⟩ :=
      (ood_pick_several_iff _ _ _ (InList G e view f) Z.val ρ y).mp hs
    exact hne (congrArg view (h1.unique hd h2 h2'))

theorem ood_list_fam : Spec.ood_list_fam := by
  intro E A J ι κ R _ _ _ _ _ G e view f L hL
  exact ood_list_image _ _ (fun M : ∀ a, R a → κ a → E => ∀ a, DecodesTo (G a) (e a) (f a) (M a))
    view _ (ood_list_pi A (fun a => R a → κ a → E) (fun a => DecodesTo (G a) (e a) (f a)) L hL)

theorem ood_cnt_severalF : Spec.ood_cnt_severalF := by
  intro E A J ι κ R _ _ _ _ _ _ G e view Z f L hL hZ
  exact ood_cnt_several E J Z (InListFam G e view f) _ (ood_list_fam E A J ι κ R G e view f L hL) hZ

theorem ood_decF_good : Spec.ood_decF_good := by
  intro E A J ι κ R _ _ _ _ G e view Z f ρ hs y u
  exact ood_pick_good _ _ _ (InListFam G e view f) Z.val ρ
    (fun hcl => hs ((exists_several_iff _ _ ρ).mpr hcl)) y u

theorem ood_whole_inj : Spec.ood_whole_inj := by
  intro E κ R M M' h
  funext a i
  exact congrFun h (a, i)

end Cb
