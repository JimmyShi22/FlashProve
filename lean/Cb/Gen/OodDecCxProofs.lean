-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecCxProofs.lean: the proofs of the statements of Cb/Gen/OodDecCx.lean (the decoder with
samples for a code complex).

The theorems "ood_* : Cb.Spec.ood_*" are at the end; before them auxiliary declarations, which no
statement reads, among them: `Comp.msgOf` (the message read off full messages), and that a word
close to an encoding decodes, as a table over E, to the full messages that the encoder forms
(`Comp.fullOf`; `Comp.decodesTo_of_close`).

Main names, each under the hypotheses of its statement (Cb/Gen/OodDecCx.lean):
  `ood_cx_cnt`: the seeds at which some answers get the value "several" number at most ((∏ L a)
    choose 2) err (L a: the assumed bound on the list of full messages of the component a; err:
    `Sample.err`); twice their number is at most (∏ L a)² err.
  `ood_cx_johnson`: the first of these bounds, with the Johnson bound for the lists.
  `ood_cx_close`: at every seed, the distance of the generator being at least d a (`HasDist`): a
    word within e' a ≤ e a symbols of an encoding of m, with e a + e' a < d a, and the answers of m:
    `Cx.decS` returns m.
  `ood_cx_guard`: at the codes' own radii the value is never "several", and if it is "one m" then
    the decoder of `Cx.enc` (Cb/Gen/Code.lean) returns m with some randomness.

Limits: see "Limits" in the head of Cb/Gen/OodDecCx.lean.
-/
import Cb.Gen.OodDecCx
import Cb.Gen.OodDecProofs
import Cb.Gen.JohnsonListProofs
import Cb.Gen.CodeProofsComp
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop Cb.Ood

section
variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [Algebra F E]

/-- the message, read off full messages -/
def Comp.msgOf (c : Comp F) (M : c.R → Fin c.code.k → E) : c.Msg E := fun i j =>
  Kf.ofE (msgPart c.code (M i) j)

theorem Comp.decodesTo_of_close (c : Comp F) (e : ℕ) (y : (c.ext E).Str) (m : c.Msg E) (r : c.Rnd E)
    (h : cnt (fun p => y p ≠ (c.enc E).enc m r p) ≤ e) :
    DecodesTo (c.code.GE E) e (c.tab y) (c.fullOf m r) := by
  refine le_trans (cnt_mono ?_) h
  rintro p ⟨i, hi⟩ hp
  refine hi ?_
  show (y p i).toE = _
  rw [hp]
  exact toE_encK c.code (m i) (r i) p

omit [Fintype F] [Fintype E] in
theorem Comp.msgOf_fullOf (c : Comp F) (hp : c.code.msg + c.code.r ≤ c.code.k)
    (m : c.Msg E) (r : c.Rnd E) : c.msgOf (c.fullOf m r) = m := by
  funext i j
  show Kf.ofE (msgPart c.code (c.code.fm (fun j => (m i j).toE) fun t => (r i t).toE) j) = m i j
  rw [msgPart_fm hp, Kf.ofE_toE]

omit [Fintype F] [Fintype E] in
theorem Cx.ents_inj (K : Cx F) : Function.Injective (K.ents (E := E)) := by
  intro m m' h
  funext a i j
  have h1 : (m a i j).toE = (m' a i j).toE := congrFun h ⟨a, i, j⟩
  calc m a i j = Kf.ofE (m a i j).toE := (Kf.ofE_toE _).symm
    _ = Kf.ofE (m' a i j).toE := by rw [h1]
    _ = m' a i j := Kf.ofE_toE _

theorem Ood.two_mul_le_sq {c L k : ℕ} (h : c ≤ L.choose 2 * k) : 2 * c ≤ L ^ 2 * k := by
  have h2 : 2 * L.choose 2 ≤ L ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (L * (L - 1) / 2) ≤ L * (L - 1) := Nat.mul_div_le _ _
      _ ≤ L * L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = L ^ 2 := (sq L).symm
  calc 2 * c ≤ 2 * (L.choose 2 * k) := Nat.mul_le_mul_left _ h
    _ = (2 * L.choose 2) * k := (Nat.mul_assoc _ _ _).symm
    _ ≤ L ^ 2 * k := Nat.mul_le_mul_right _ h2

theorem Cx.cnt_several_le (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (L : ℕ)
    (hL : ListLE (K.Near E e y) L) (hZ : Z.OK) :
    cnt (fun ρ : Z.D => ∃ v, K.decS E e Z y ρ v = .several) ≤ L.choose 2 * Z.err := by
  refine (le_of_eq
    (cnt_congr (Q := Clash (K.Near E e y) (K.ans Z)) fun ρ =>
      exists_several_iff (K.Near E e y) (K.ans Z) ρ)).trans ?_
  refine ood_cnt_clash _ Z.D _ _ _ L Z.err hL fun m m' _ _ hne => ?_
  refine (cnt_mono fun ρ hρ => ?_).trans
    (hZ (K.ents m - K.ents m') (sub_ne_zero.mpr fun h => hne (K.ents_inj h)))
  rw [Sample.val_sub]
  exact sub_eq_zero.mpr hρ

end

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

theorem ood_cx_one_iff : Spec.ood_cx_one_iff F E := by
  intro K e Z y ρ v m
  exact (ood_pick_iff _ _ _ (K.Near E e y) (K.ans Z) ρ v m).trans ⟨fun h =>
      ⟨h.1.1, h.1.2, fun m' h1 h2 => h.2 m' ⟨h1, h2⟩⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, fun m' hm' => h.2.2 m' hm'.1 hm'.2⟩⟩

theorem ood_cx_none_iff : Spec.ood_cx_none_iff F E := by
  intro K e Z y ρ v
  exact (ood_pick_none_iff _ _ _ (K.Near E e y) (K.ans Z) ρ v).trans
    ⟨fun h m h1 h2 => h m ⟨h1, h2⟩, fun h m hm => h m hm.1 hm.2⟩

theorem ood_cx_several_iff : Spec.ood_cx_several_iff F E := by
  intro K e Z y ρ v
  exact (ood_pick_several_iff _ _ _ (K.Near E e y) (K.ans Z) ρ v).trans
    ⟨fun ⟨m, m', hne, h1, h2⟩ => ⟨m, m', hne, h1.1, h2.1, h1.2, h2.2⟩,
      fun ⟨m, m', hne, h1, h2, h3, h4⟩ => ⟨m, m', hne, ⟨h1, h3⟩, ⟨h2, h4⟩⟩⟩

theorem ood_cx_good : Spec.ood_cx_good F E := by
  intro K e Z y ρ hs v m
  exact ood_pick_good _ _ _ (K.Near E e y) (K.ans Z) ρ
    (fun hcl => hs ((exists_several_iff _ _ ρ).mpr hcl)) v m

theorem ood_comp_list : Spec.ood_comp_list F E := by
  intro c e y L hp hL
  refine ood_list_mono _ _ _ L (fun m hm => ?_)
    (ood_list_image _ _ (DecodesTo (c.code.GE E) e (c.tab y)) c.msgOf L hL)
  obtain ⟨r, hr⟩ := hm
  exact ⟨c.fullOf m r, c.decodesTo_of_close e y m r hr, c.msgOf_fullOf hp m r⟩

theorem ood_cx_list : Spec.ood_cx_list F E := by
  intro K e y L hp hL
  exact ood_list_pi K.A (fun a => (K.comp a).Msg E) (fun a => (K.comp a).Near E (e a) (y a)) L
    fun a => ood_comp_list F E (K.comp a) (e a) (y a) (L a) (hp a) (hL a)

theorem ood_cx_cnt : Spec.ood_cx_cnt F E := by
  intro K e Z y L hp hL hZ
  have h := K.cnt_several_le e Z y _ (ood_cx_list F E K e y L hp hL) hZ
  exact ⟨h, two_mul_le_sq h⟩

theorem ood_cx_johnson : Spec.ood_cx_johnson F E := by
  intro K e Z y hp hd hJ hZ
  refine (ood_cx_cnt F E K e Z y _ hp (fun a S hS => ?_) hZ).1
  have h := johnson_tables E (Fin (K.comp a).code.n) (Fin (K.comp a).code.k) ((K.comp a).code.GE E)
    (K.comp a).code.d (e a) (HasDist.map (E := E) (hd a)) (by rw [Fintype.card_fin]; exact hJ a)
    (K.comp a).R ((K.comp a).tab (y a)) S hS
  rwa [Fintype.card_fin] at h

theorem ood_cx_close : Spec.ood_cx_close F E := by
  intro K e e' Z y m hp hd hle hlt hm ρ
  refine (ood_pick_iff _ _ _ (K.Near E e y) (K.ans Z) ρ _ m).mpr
    ⟨⟨fun a => ?_, rfl⟩, fun m' hm' => funext fun a => ?_⟩
  · obtain ⟨r, hr⟩ := hm a
    exact ⟨r, hr.trans (hle a)⟩
  · obtain ⟨r, hr⟩ := hm a
    obtain ⟨r', hr'⟩ := hm'.1 a
    have h1 := (K.comp a).decodesTo_of_close (e a) (y a) (m' a) r' hr'
    have h2 := (K.comp a).decodesTo_of_close (e' a) (y a) (m a) r hr
    have h3 : (K.comp a).fullOf (m' a) r' = (K.comp a).fullOf (m a) r :=
      funext fun _ => DecodesTo.row_unique (HasDist.map (E := E) (hd a)) (hlt a) h1 h2 rfl
    exact ((K.comp a).msgOf_fullOf (hp a) (m' a) r').symm.trans
      ((congrArg (K.comp a).msgOf h3).trans ((K.comp a).msgOf_fullOf (hp a) (m a) r))

theorem ood_cx_enc : Spec.ood_cx_enc F E := by
  intro K e Z m r hp hd hlt ρ
  exact ood_cx_close F E K e (fun _ => 0) Z _ m hp hd (fun a => Nat.zero_le _) (fun a => hlt a)
    (fun a => ⟨r a, le_of_eq (cnt_false fun p hp => hp rfl)⟩) ρ

theorem ood_cx_guard : Spec.ood_cx_guard F E := by
  intro K Z y ρ v hK
  have key : ∀ m, K.Near E (fun a => (K.comp a).code.e) y m →
      ∃ r, (K.enc E).dec y = some (m, r) := fun m hm => by
    have hm' : ∀ a, ∃ r : (K.comp a).Rnd E,
        cnt (fun p => y a p ≠ ((K.comp a).enc E).enc (m a) r p) ≤ (K.comp a).code.e := hm
    choose r hr using hm'
    exact ⟨r, (dec_fam_iff K.A _ (fun a => (K.comp a).enc E) y (m, r)).2 fun a =>
        comp_close F E (K.comp a) (hK a) (y a) (m a) (r a) (hr a)⟩
  refine ⟨fun hs => ?_, fun m hm => key m ((ood_cx_one_iff F E K _ Z y ρ v m).mp hm).1⟩
  obtain ⟨m, m', hne, hm, hm', _, _⟩ := (ood_cx_several_iff F E K _ Z y ρ v).mp hs
  obtain ⟨r, hr⟩ := key m hm
  obtain ⟨r', hr'⟩ := key m' hm'
  rw [hr] at hr'
  exact hne (congrArg Prod.fst (Option.some.inj hr'))

end
end Cb
