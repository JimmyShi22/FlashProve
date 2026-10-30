-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigProofs.lean: the proofs of the statements of Cb/Ld/LdSig.lean, on list decoding with a
sample (a seed, and the prover's answers: a few linear functionals of the message; in this library's
terms oracle messages, statements that carry their samples, the relaxation by decoding with a
sample), but for `Spec.sig_two`, which is proved at a small code in Cb/Ld/LdSigTest.lean.

The order. Tools: the list in the terms of the abstract decoder (`Within`, Cb/Gen/OodDecMin.lean):
`OMsg.within_eq`; `LdCode.near_eq`; the distance from an encoding (`OMsg.dist_self`,
`OMsg.dist_pos`). Then the statements on one oracle message, then those on signatures and joints.
Nothing is defined here that a statement reads.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSig
import Cb.Ld.LdRelJohnsonProofs
import Cb.Gen.OodDecMinProofs
import Cb.Gen.OodDecPadProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

section Tools
variable {E : Type} [Field E]

theorem OMsg.within_eq (o : OMsg E) (f : o.Str) :
    Within (o.dist f) (Prod.fst : o.Wit → o.Msg) o.e = o.InList f := by
  funext m
  refine propext ⟨?_, ?_⟩
  · rintro ⟨⟨m', r⟩, hd, rfl⟩
    exact ⟨r, hd⟩
  · rintro ⟨r, hr⟩
    exact ⟨(m, r), hr, rfl⟩

/-- Under `hL` and `hd`: two pairs whose encodings are within k and k' long positions of one word, k
+ k' below d, are equal. -/
theorem LdCode.near_eq {P : Type} [Fintype P] (C : LdCode E P) {d k k' : ℕ} (hL : C.Laws)
    (hd : C.Dist d) (hk : k + k' < d) (g : C.Word) (w w' : (C.J → E) × (C.Q → E))
    (h : C.Near k g (C.enc w.1 w.2)) (h' : C.Near k' g (C.enc w'.1 w'.2)) : w = w' := by
  by_contra hne
  have h1 := ld_dist_ne E P C d hL hd w w' hne
  have h3 : cnt (fun x => C.T (C.enc w.1 w.2) x ≠ C.T (C.enc w'.1 w'.2) x) ≤
      cnt (fun x => C.T g x ≠ C.T (C.enc w.1 w.2) x) +
        cnt (fun x => C.T g x ≠ C.T (C.enc w'.1 w'.2) x) :=
    cnt_le_add fun x hx => by
      by_cases hc : C.T g x = C.T (C.enc w.1 w.2) x
      · exact Or.inr fun hc' => hx (hc.symm.trans hc')
      · exact Or.inl hc
  have h4 : cnt (fun x => C.T g x ≠ C.T (C.enc w.1 w.2) x) ≤ k := h
  have h5 : cnt (fun x => C.T g x ≠ C.T (C.enc w'.1 w'.2) x) ≤ k' := h'
  omega

omit [Field E] in
theorem OMsg.dist_self (o : OMsg E) (f : o.Str) (w : o.Wit) (hf : o.upW f = o.C.enc w.1 w.2) :
    o.dist f w = 0 := by
  unfold OMsg.dist
  rw [hf]
  exact cnt_false fun _ h => h rfl

theorem OMsg.dist_pos (o : OMsg E) (hL : o.C.Laws) (hd : o.C.Dist 1) (f : o.Str) (w t : o.Wit)
    (hf : o.upW f = o.C.enc w.1 w.2) (hne : t ≠ w) : 1 ≤ o.dist f t := by
  unfold OMsg.dist
  rw [hf]
  exact ld_dist_ne E o.P o.C 1 hL hd w t (Ne.symm hne)

end Tools

section
variable (E : Type) [Field E]

theorem sig_inList_iff : Spec.sig_inList_iff E := fun o f m => by rw [o.within_eq f]

omit [Field E] in
theorem sig_dist_near : Spec.sig_dist_near E := fun _ _ _ _ => Iff.rfl

theorem sig_dec_cand : Spec.sig_dec_cand E := by
  intro o f σ m h
  have h1 := ood_decMin_cand _ _ _ _ (o.dist f) o.rank Prod.fst o.Z.val o.e σ.1 σ.2 m h
  rw [o.within_eq f] at h1
  exact h1

theorem sig_dec_none : Spec.sig_dec_none E := by
  intro o f σ
  have h1 :=
    ood_decMin_none_iff _ _ _ _ (o.dist f) o.rank (Prod.fst : o.Wit → o.Msg) o.Z.val o.e σ.1 σ.2
  rw [o.within_eq f] at h1
  exact h1

theorem sig_dec_good : Spec.sig_dec_good E := by
  intro o f ρ hc v m
  have h0 : ¬ Coll (Within (o.dist f) (Prod.fst : o.Wit → o.Msg) o.e) o.Z.val ρ v := by
    rw [o.within_eq f]
    exact not_coll_of_not_clash hc v
  have h1 :=
    ood_decMin_good _ _ _ _ (o.dist f) o.rank (Prod.fst : o.Wit → o.Msg) o.Z.val o.e ρ v h0 m
  rw [o.within_eq f] at h1
  exact h1

theorem sig_dec_enc : Spec.sig_dec_enc E := by
  intro o hL hd f w ρ hf
  have h0 := o.dist_self f w hf
  have hF : First (o.dist f) o.rank (Prod.fst : o.Wit → o.Msg) o.Z.val ρ (o.Z.val ρ w.1) w := by
    refine ⟨rfl, fun t' _ => ?_⟩
    by_cases ht : t' = w
    · subst ht
      exact Or.inr ⟨rfl, le_refl _⟩
    · have := o.dist_pos hL hd f w t' hf ht
      exact Or.inl (by omega)
  have h : ∃ t,
      First (o.dist f) o.rank (Prod.fst : o.Wit → o.Msg) o.Z.val ρ (o.Z.val ρ w.1) t ∧
      o.dist f t ≤ o.e :=
    ⟨w, hF, by omega⟩
  have hc : h.choose = w := by
    by_contra hne
    have h1 := o.dist_pos hL hd f w h.choose hf hne
    have h2 := h.choose_spec.1.2 w rfl
    omega
  show decMin (o.dist f) o.rank (Prod.fst : o.Wit → o.Msg) o.Z.val o.e ρ (o.Z.val ρ w.1) = some w.1
  unfold decMin
  rw [dif_pos h, hc]

theorem sig_dec_close : Spec.sig_dec_close E := by
  intro o d e' hL hd he hlt f m hm ρ
  obtain ⟨r, hr⟩ := hm
  have hall : ∀ m', o.InList f m' → m' = m := by
    rintro m' ⟨r', hr'⟩
    exact congrArg Prod.fst (o.C.near_eq hL hd hlt (o.upW f) (m', r') (m, r) hr' hr)
  have hc : ¬ o.Clash f ρ := by
    rintro ⟨u, u', hu, hu', hne, _⟩
    exact hne ((hall u hu).trans (hall u' hu').symm)
  exact (sig_dec_good E o f ρ hc _ m).2 ⟨⟨r, le_trans hr he⟩, rfl⟩

theorem sig_rows : Spec.sig_rows E := fun _ _ _ => ⟨fun h s => congrFun h s, fun h => funext h⟩

theorem sig_list_of_code [Finite E] : Spec.sig_list_of_code E := fun o L h f =>
  ld_msgs_list E o.P o.C o.e L h (o.upW f)

theorem sig_evades_of_okOn : Spec.sig_evades_of_okOn E := by
  intro o V hZ hV f m m' hm hm' hne
  refine (cnt_mono fun ρ hρ => ?_).trans (hZ (m - m') (hV f m m' hm hm') (sub_ne_zero.mpr hne))
  rw [Sample.val_sub, hρ, sub_self]

theorem sig_evades_of_ok : Spec.sig_evades_of_ok E := fun o hZ =>
  sig_evades_of_okOn E o (fun _ => True) (ood_okOn_of_ok E o.C.J o.Z _ hZ) fun _ _ _ _ _ => trivial

theorem sig_cnt_clash : Spec.sig_cnt_clash E := by
  intro o L hL hE f
  have h : cnt (o.Clash f) ≤ L.choose 2 * o.Z.err :=
    ood_cnt_clash o.Msg o.Z.D (o.Z.S → E) (o.InList f) o.Z.val L o.Z.err (hL f)
      fun u u' hu hu' hne => hE f u u' hu hu' hne
  refine ⟨h, ?_⟩
  have h2 : 2 * L.choose 2 ≤ L ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (L * (L - 1) / 2) ≤ L * (L - 1) := Nat.mul_div_le _ _
      _ ≤ L * L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = L ^ 2 := (sq L).symm
  calc 2 * cnt (o.Clash f) ≤ 2 * (L.choose 2 * o.Z.err) := Nat.mul_le_mul_left _ h
    _ = (2 * L.choose 2) * o.Z.err := (Nat.mul_assoc _ _ _).symm
    _ ≤ L ^ 2 * o.Z.err := Nat.mul_le_mul_right _ h2

theorem sig_no_clash_unique : Spec.sig_no_clash_unique E := by
  rintro o d hL hd h2 f ρ ⟨u, u', ⟨r, hr⟩, ⟨r', hr'⟩, hne, _⟩
  exact hne (congrArg Prod.fst (o.C.near_eq hL hd (by omega) (o.upW f) (u, r) (u', r') hr hr'))

theorem sig_dec_unique : Spec.sig_dec_unique E := by
  intro o d hL hd h2 f σ m
  refine ⟨sig_dec_good E o f σ.1 (sig_no_clash_unique E o d hL hd h2 f σ.1) σ.2 m, ?_⟩
  rintro m' ⟨r, hr⟩ ⟨r', hr'⟩
  exact congrArg Prod.fst (o.C.near_eq hL hd (by omega) (o.upW f) (m', r') (m, r) hr' hr)

theorem sig_over_sub : Spec.sig_over_sub E := by
  intro S Kc St Wp E₀ A hL hd hA x y w h
  obtain ⟨hE, hAns, hr⟩ := h
  refine ⟨fun i => ?_, hA _ _ _ hr⟩
  have h1 := sig_dec_enc E (S.om i) (hL i) (hd i) (y.2 i) (w.1 i) (x.2 i).1 (hE i)
  have h2 : (S.om i).Z.val (x.2 i).1 (w.1 i).1 = (x.2 i).2 := hAns i
  rw [h2] at h1
  exact h1

theorem sig_sent_sub : Spec.sig_sent_sub E := by
  intro o Kc X W W' E₀ A back hL hd hA x y w h
  obtain ⟨hE, hAns, hr⟩ := h
  refine ⟨?_, hA _ _ _ hr⟩
  have h1 := sig_dec_enc E o hL hd y.2 w.1 x.2.1 hE
  rw [hAns] at h1
  exact h1

theorem sig_over_det : Spec.sig_over_det E := fun _ _ _ _ _ _ _ _ _ _ h h' =>
  funext fun i => Option.some.inj ((h.1 i).symm.trans (h'.1 i))

theorem sig_over_cf : Spec.sig_over_cf E := by
  intro S Kc St Wp E₀ A a w hcf
  have h : ∀ i,
      S.decs a.1.2 a.2.2 i = some (w.1 i).1 ↔
      (S.om i).Cand (a.2.2 i) (a.1.2 i) (w.1 i).1 := fun i =>
    sig_dec_good E (S.om i) (a.2.2 i) (a.1.2 i).1 (hcf i) (a.1.2 i).2 (w.1 i).1
  exact ⟨fun hw => ⟨fun i => (h i).1 (hw.1 i), hw.2⟩, fun hw => ⟨fun i => (h i).2 (hw.1 i), hw.2⟩⟩

theorem sig_cf_add : Spec.sig_cf_add E := fun _ _ _ _ _ _ =>
  ⟨fun h => ⟨fun a => h (some a), h none⟩, fun h a => match a with
    | none => h.2
    | some a => h.1 a⟩

theorem sig_sent_one : Spec.sig_sent_one E := fun _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨⟨fun h => ⟨h.1 (), h.2.1 (), h.2.2⟩, fun h => ⟨fun _ => h.1, fun _ => h.2.1, h.2.2⟩⟩,
   ⟨fun h => ⟨h.1 (), h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩,
   ⟨fun h => ⟨h.2, h.1 ()⟩, fun h => ⟨fun _ => h.2, h.1⟩⟩⟩

theorem sig_copies : Spec.sig_copies E := by
  intro S St St' E₀ E₀' R hC a τ b hcf hb
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hb
  show S.CF xo.2 (R.imp a.2 τ).2
  rw [hC.1 _ _ _ _ hx, hC.2]
  exact hcf

end
end Cb
