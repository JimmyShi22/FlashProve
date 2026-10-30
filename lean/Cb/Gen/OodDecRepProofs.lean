-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecRepProofs.lean: the proofs of the statements of Cb/Gen/OodDecRep.lean (the decoder with
samples for a code complex under a reading).

The theorems "ood_cxU_* : Cb.Spec.ood_cxU_*" are at the end; before them auxiliary declarations,
which no statement reads, among them: `Cx.tabs`, `Cx.fulls` (short names for the tables of the words
and for the full messages that the encoder forms), "a symbol differs from the encoding if and only
if the column is off", and the count of bad seeds for any list of messages of a complex.

Main names, each under the hypotheses of its statement (Cb/Gen/OodDecRep.lean):
  `ood_cxU_cnt`: the counting lemma (`ood_cnt_clash`, Cb/Gen/OodDec.lean), under a bound L on the
    list of families of full messages under the reading: the seeds at which some answers have a
    collision number at most (L choose 2) err (`Sample.err`); twice their number is at most L² err.
    For a sample map with the property on a set V of vectors that holds all differences of messages
    (`Sample.OKOn`; V = everything gives `Sample.OK`).
  `ood_cxU_johnson`: the first of these bounds, for the same sample maps, with L = `listMax` from
    the distance alone: an even reading, a lower bound d a on the distance of each generator
    (`HasDist`), D ≤ mult a · d a for all components, the radius below the Johnson radius for
    (number of long positions, D). It does not multiply over the components.
  `ood_cxU_good`: without a collision: `Cx.decMinU` returns m if and only if m is in the list and
    has the answers; and `Cx.decMinU` is `Cx.pickU` (with none for "none").
  `ood_cxU_close`: at every seed, for T, d a and D as in `ood_cxU_johnson`: words within e' ≤ e long
    positions of an encoding of m, with e + e' < D, and the answers of m: `Cx.decMinU` returns m.

Limits: see "Limits" in the head of Cb/Gen/OodDecRep.lean.
-/
import Cb.Gen.OodDecRep
import Cb.Gen.OodDecCxProofs
import Cb.Gen.OodDecMinProofs
import Cb.Gen.OodDecPadProofs
import Cb.Gen.CodeRepProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop Cb.Ood

section
variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [Algebra F E]

abbrev Cx.tabs (K : Cx F) (y : (K.ext E).Str) : ∀ a, (K.comp a).R → Fin (K.cods a).n → E := fun a =>
  (K.comp a).tab (y a)
abbrev Cx.fulls (K : Cx F) (w : K.Msg E × K.Rnd E) : ∀ a, (K.comp a).R → Fin (K.cods a).k → E :=
  fun a => (K.comp a).fullOf (w.1 a) (w.2 a)

theorem Comp.ne_enc_iff_off (c : Comp F) (y : (c.ext E).Str) (m : c.Msg E)
    (r : c.Rnd E) (p : Fin c.code.n) :
    y p ≠ (c.enc E).enc m r p ↔ Blocks.Off (c.code.GE E) (c.tab y) (c.fullOf m r) p := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine ⟨i, fun heq => hi ?_⟩
    have h1 : (y p i).toE = ((c.enc E).enc m r p i).toE :=
      heq.trans (toE_encK c.code (m i) (r i) p).symm
    calc y p i = Kf.ofE (y p i).toE := (Kf.ofE_toE _).symm
      _ = Kf.ofE ((c.enc E).enc m r p i).toE := by rw [h1]
      _ = (c.enc E).enc m r p i := Kf.ofE_toE _
  · rintro ⟨i, hi⟩ hp
    refine hi ?_
    show (y p i).toE = _
    rw [hp]
    exact toE_encK c.code (m i) (r i) p

theorem Cx.distU_eq (K : Cx F) (T : Reading K.cods) (y : (K.ext E).Str) (w : K.Msg E × K.Rnd E) :
    K.distU E T y w = cnt (T.Off E (K.tabs y) (K.fulls w)) :=
  cnt_congr fun x =>
    exists_congr fun a => (K.comp a).ne_enc_iff_off (y a) (w.1 a) (w.2 a) (T.pos a x)

theorem Cx.decodesTo_of_distU (K : Cx F) (T : Reading K.cods) {y : (K.ext E).Str}
    {w : K.Msg E × K.Rnd E} {e : ℕ} (h : K.distU E T y w ≤ e) :
    T.DecodesTo E e (K.tabs y) (K.fulls w) := by
  rw [K.distU_eq] at h
  exact h

omit [Fintype F] [Fintype E] in
theorem Cx.cnt_clash_on (K : Cx F) (Z : Sample E K.Ent) (V : (K.Ent → E) → Prop)
    (Lst : K.Msg E → Prop) (L : ℕ) (hL : ListLE Lst L) (hZ : Z.OKOn V)
    (hV : ∀ m m' : K.Msg E, V (K.ents m - K.ents m')) :
    cnt (Clash Lst (K.ans Z)) ≤ L.choose 2 * Z.err := by
  refine ood_cnt_clash _ Z.D _ _ _ L Z.err hL fun m m' _ _ hne => ?_
  refine (cnt_mono fun ρ hρ => ?_).trans
    (hZ (K.ents m - K.ents m') (hV m m') (sub_ne_zero.mpr fun h => hne (K.ents_inj h)))
  rw [Sample.val_sub]
  exact sub_eq_zero.mpr hρ

end

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

theorem ood_cxU_dist : Spec.ood_cxU_dist F E := fun K T y w => K.distU_eq T y w

theorem ood_cxU_list : Spec.ood_cxU_list F E := by
  intro K T e y L hp hL
  refine ood_list_mono _ _ _ L (fun m hm => ?_)
    (ood_list_image _ _ _
      (fun (M : ∀ a, (K.comp a).R → Fin (K.comp a).code.k → E) =>
        (fun a => (K.comp a).msgOf (M a) : K.Msg E))
      L hL)
  obtain ⟨w, hw, rfl⟩ := hm
  exact ⟨K.fulls w,
    K.decodesTo_of_distU T hw,
    funext fun a => (K.comp a).msgOf_fullOf (hp a) (w.1 a) (w.2 a)⟩

theorem ood_cxU_cnt : Spec.ood_cxU_cnt F E := by
  intro K T e Z V y L hp hL hZ hV
  have h : cnt (fun ρ : Z.D => ∃ v, K.CollU E T e Z y ρ v) ≤ L.choose 2 * Z.err :=
    (le_of_eq (cnt_congr fun ρ => (ood_clash_iff _ _ _ (K.NearU E T e y) (K.ans Z) ρ).symm)).trans
      (K.cnt_clash_on Z V _ L (ood_cxU_list F E K T e y L hp hL) hZ hV)
  exact ⟨h, two_mul_le_sq h⟩

theorem ood_cxU_johnson : Spec.ood_cxU_johnson F E := by
  intro K T D e Z V y hp hT hd hD hJ hZ hV
  refine (ood_cxU_cnt F E K T e Z V y _ hp (ood_list_of_cnt _ _ _ ?_) hZ hV).1
  exact list_le_johnson F E K.A K.cods T hT hd D hD e hJ (fun a => (K.comp a).R) (K.tabs y)

theorem ood_cxU_good : Spec.ood_cxU_good F E := by
  intro K T rank e Z y ρ v hc
  exact ⟨fun m => ood_decMin_good _ _ _ _ (K.distU E T y) rank Prod.fst (K.ans Z) e ρ v hc m,
    (ood_decMin_pick _ _ _ _ (K.distU E T y) rank Prod.fst (K.ans Z) e ρ v).2 hc⟩

theorem ood_cxU_close : Spec.ood_cxU_close F E := by
  intro K T rank D e e' Z y m hp hT hd hD hle hlt hm ρ
  obtain ⟨w, hw, rfl⟩ := hm
  have hall : ∀ m', K.NearU E T e y m' → m' = w.1 := by
    rintro m' ⟨w', hw', rfl⟩
    have h1 : cnt (T.Off E (K.tabs y) (K.fulls w')) ≤ e := K.decodesTo_of_distU T hw'
    have h2 : cnt (T.Off E (K.tabs y) (K.fulls w)) ≤ e' := K.decodesTo_of_distU T hw
    have h3 : K.fulls w' = K.fulls w := by
      by_contra hne
      have h4 := dist_under F E K.A K.cods T hT hd D hD (fun a => (K.comp a).R) _ _ hne
      have h6 : D ≤
          cnt (T.Off E (K.tabs y) (K.fulls w')) + cnt (T.Off E (K.tabs y) (K.fulls w)) := by
        refine h4.trans (cnt_le_add fun x hx => ?_)
        obtain ⟨a, i, hx⟩ := hx
        by_cases hc : K.tabs y a i (T.pos a x) =
          ((K.cods a).GE E).mulVec (K.fulls w' a i) (T.pos a x)
        · exact Or.inr ⟨a, i, fun hc' => hx (hc.symm.trans hc')⟩
        · exact Or.inl ⟨a, i, hc⟩
      omega
    funext a
    exact ((K.comp a).msgOf_fullOf (hp a) (w'.1 a) (w'.2 a)).symm.trans
      ((congrArg (K.comp a).msgOf (congrFun h3 a)).trans
        ((K.comp a).msgOf_fullOf (hp a) (w.1 a) (w.2 a)))
  refine (ood_decMin_good _ _ _ _ (K.distU E T y) rank Prod.fst (K.ans Z) e ρ _ ?_ w.1).mpr
    ⟨⟨w, hw.trans hle, rfl⟩, rfl⟩
  rintro ⟨u, u', hne, hu, hu'⟩
  exact hne ((hall u hu.1).trans (hall u' hu'.1).symm)

theorem ood_cxU_enc : Spec.ood_cxU_enc F E := by
  intro K T rank D e Z m r hp hT hd hD he ρ
  exact ood_cxU_close F E K T rank D e 0 Z _ m hp hT hd hD (Nat.zero_le _) (by omega)
    ⟨(m, r), le_of_eq (cnt_false fun x hx => hx.elim fun a h => h rfl), rfl⟩ ρ

theorem ood_cxU_near_comp : Spec.ood_cxU_near_comp F E := by
  intro K T e y m hT hm a
  obtain ⟨w, hw, rfl⟩ := hm
  refine ⟨w.2 a, ?_⟩
  rw [Nat.le_div_iff_mul_le (hT a).1, mul_comm,
    ← CodeRep.cnt_comp_even (T.pos a) (T.mult a) (hT a).2
      (fun p => y a p ≠ ((K.comp a).enc E).enc (w.1 a) (w.2 a) p)]
  exact (cnt_mono fun x hx => ⟨a, hx⟩).trans hw

theorem ood_cxU_one : Spec.ood_cxU_one F E := by
  intro c e y m
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2 (), (cnt_mono fun p hp => ⟨(), hp⟩).trans hw⟩
  · rintro ⟨r, hr⟩
    refine ⟨(m, fun _ => r), (cnt_mono fun x hx => ?_).trans hr, rfl⟩
    obtain ⟨a, ha⟩ := hx
    cases a
    exact ha

end
end Cb
