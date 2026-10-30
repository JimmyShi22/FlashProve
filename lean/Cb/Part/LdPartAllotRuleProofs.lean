-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartAllotRuleProofs.lean: the proofs of the statements of Cb/Part/LdPartAllotRule.lean
("allotted ⇒ pending", for arbitrary parameters). Nothing is stated here that is not stated there,
but for: the two embeddings of entries behind a sending are injective and apart.
-/
import Cb.Part.LdPartAllotRule

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable {E : Type}

theorem Sig.atNew_inj (S N : Sig E) : Function.Injective (S.atNew N) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 (show (⟨.inr a, j⟩ : (S.sum N).Ent) = ⟨.inr b, k⟩ from h)
  obtain rfl := Sum.inr.inj h1
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

theorem Sig.atOld_inj (S N : Sig E) : Function.Injective (S.atOld N) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 (show (⟨.inl a, j⟩ : (S.sum N).Ent) = ⟨.inl b, k⟩ from h)
  obtain rfl := Sum.inl.inj h1
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

theorem Sig.atOld_ne (S N : Sig E) (n : S.Ent) (n' : N.Ent) :
    S.atOld N n ≠ S.atNew N n' := fun h => by
  have h1 : (Sum.inl n.1 : S.O ⊕ N.O) = Sum.inr n'.1 := congrArg Sigma.fst h
  cases h1

end

section
variable (E Kc : Type) [Field E] [Fintype E]

omit [Field E] [Fintype E] in
theorem ldRule_jd : Spec.ldRule_jd E Kc := by
  intro a X β h
  induction h with
  | base β hx => exact hx
  | pair β₁ β₂ Rd Rr h1 h2 h3 _ _ i1 i2 => exact .pair β₁ β₂ Rd Rr h1 h2 h3 i1 i2
  | less β Rd Rr h1 h2 h3 _ ih => exact .less β Rd Rr h1 h2 h3 ih
  | reMk β Mk' e _ ih => exact .reMk β Mk' e ih
  | same β own val h1 h2 _ ih => exact .same β own val h1 h2 ih

omit [Field E] [Fintype E] in
theorem ldRule_recast : Spec.ldRule_recast E Kc := by
  intro a X β β' hX hβ h
  obtain ⟨h1, h2, h3, h4, e, h5⟩ := h
  have s1 : LdPend.JD X ⟨β'.Rd, β'.Rr, β.own, β.Mk, β.val⟩ :=
    .less β β'.Rd β'.Rr h1 h2 (fun n hn => h3 n ((h4 n).1 hn)) (.base β hβ)
  have s2 : LdPend.JD X ⟨β'.Rd, β'.Rr, β.own, β'.Mk, fun M => β.val (e.symm M)⟩ :=
    .reMk (⟨β'.Rd, β'.Rr, β.own, β.Mk, β.val⟩ : LdPend a) β'.Mk e s1
  have s3 : LdPend.JD X ⟨β'.Rd, β'.Rr, β'.own, β'.Mk, β'.val⟩ := .same (⟨β'.Rd, β'.Rr, β.own, β'.Mk, fun M => β.val (e.symm M)⟩ : LdPend a) β'.own β'.val h4 (fun M n hn => by
    have h6 := h5 (e.symm M) n hn
    rw [e.apply_symm_apply] at h6
    exact h6) s2
  exact hX β' s3

theorem ldRule_castMany : Spec.ldRule_castMany E Kc := by
  intro F _ _ _ a d Y Ix _ _ pl hpl Rd Rr hN hR hrd Mk _ _ vf hvf
  have hj : Function.Injective fun x => Y.entF (pl x) := Y.entF_injective.comp hpl
  have hi : Function.Injective fun x => a.S.atNew d.N (Y.entF (pl x)) := (a.S.atNew_inj d.N).comp hj
  have hown : ∀ n : d.tgt.S.Ent,
      a.S.sumP d.N (fun _ => False) (Y.ownP pl) n ↔
      plOwn (fun x => a.S.atNew d.N (Y.entF (pl x))) n := by
    rintro ⟨o | o, j⟩
    · exact ⟨fun h => h.elim, fun ⟨x, hx⟩ => a.S.atOld_ne d.N ⟨o, j⟩ _ hx.symm⟩
    · exact ⟨fun ⟨i, hi'⟩ => ⟨i, (congrArg (a.S.atNew d.N) hi').symm⟩,
        fun ⟨x, hx⟩ =>
          ⟨x, (a.S.atNew_inj d.N
              (show a.S.atNew d.N (Y.entF (pl x)) = a.S.atNew d.N ⟨o, j⟩ from hx)).symm⟩⟩
  refine ⟨?_, ?_, ?_, hown, (Equiv.ofBijective vf hvf).symm, ?_⟩
  · rintro ⟨o | o, j⟩ h
    · exact h
    · exact hN ⟨o, j⟩ h
  · rintro (o | o) h
    · exact h
    · exact (hR o h).elim
  · rintro n ⟨x, rfl⟩
    exact hrd x
  · intro M n hn
    obtain ⟨x, rfl⟩ := (hown n).1 hn
    have e1 : Y.valP pl M (Y.entF (pl x)) = M x := hj.extend_apply _ _ x
    have e2 : plVal (fun x => a.S.atNew d.N (Y.entF (pl x))) vf
          ((Equiv.ofBijective vf hvf).symm M) (a.S.atNew d.N (Y.entF (pl x))) =
        vf ((Equiv.ofBijective vf hvf).symm M) x :=
      hi.extend_apply _ _ x
    have e3 : vf ((Equiv.ofBijective vf hvf).symm M) = M :=
      Equiv.ofBijective_apply_symm_apply vf hvf M
    exact e1.trans (e2.trans (congrFun e3 x)).symm

theorem ldRule_castOne : Spec.ldRule_castOne E Kc := by
  intro F _ _ _ a d Y o Ix _ _ pl hpl Rd Rr hN hR hrd Mk _ _ vf hvf
  have hj : Function.Injective fun x => Y.entO o (pl x) := (Y.entO_inj o).comp hpl
  have hi : Function.Injective fun x => a.S.atNew d.N (Y.entO o (pl x)) :=
    (a.S.atNew_inj d.N).comp hj
  have hown : ∀ n : d.tgt.S.Ent,
      a.S.sumP d.N (fun _ => False) (Y.ownO o pl) n ↔
      plOwn (fun x => a.S.atNew d.N (Y.entO o (pl x))) n := by
    rintro ⟨o' | o', j⟩
    · exact ⟨fun h => h.elim, fun ⟨x, hx⟩ => a.S.atOld_ne d.N ⟨o', j⟩ _ hx.symm⟩
    · exact ⟨fun ⟨i, hi'⟩ => ⟨i, congrArg (a.S.atNew d.N) hi'⟩,
        fun ⟨x, hx⟩ =>
          ⟨x, a.S.atNew_inj d.N
              (show a.S.atNew d.N (Y.entO o (pl x)) = a.S.atNew d.N ⟨o', j⟩ from hx)⟩⟩
  refine ⟨?_, ?_, ?_, hown, (Equiv.ofBijective vf hvf).symm, ?_⟩
  · rintro ⟨o' | o', j⟩ h
    · exact h
    · exact hN ⟨o', j⟩ h
  · rintro (o' | o') h
    · exact h
    · exact fun e => hR (e ▸ h)
  · rintro n ⟨x, rfl⟩
    exact hrd x
  · intro M n hn
    obtain ⟨x, rfl⟩ := (hown n).1 hn
    have e1 : Y.valO o pl M (Y.entO o (pl x)) = M x := hj.extend_apply _ _ x
    have e2 : plVal (fun x => a.S.atNew d.N (Y.entO o (pl x))) vf
          ((Equiv.ofBijective vf hvf).symm M) (a.S.atNew d.N (Y.entO o (pl x))) =
        vf ((Equiv.ofBijective vf hvf).symm M) x :=
      hi.extend_apply _ _ x
    have e3 : vf ((Equiv.ofBijective vf hvf).symm M) = M :=
      Equiv.ofBijective_apply_symm_apply vf hvf M
    exact e1.trans (e2.trans (congrFun e3 x)).symm

theorem ldRule_many : Spec.ldRule_many E Kc := by
  intro F _ _ _ a d Q Y dat rst bk₀ w0 hS hQ Nm pl hpl X hX hL Rd Rr hN hR hrd
  refine ⟨(a.S.atNew_inj d.N).comp (Y.entF_injective.comp hpl),
    hrd,
    fun Ix _ nm hnm Mk _ _ vf hvf => ?_⟩
  classical
  exact ldRule_recast E Kc _ X _ _ hX
    (hL _ ⟨F, inferInstance, inferInstance, inferInstance, Y, dat, rst, bk₀, w0, hS, hQ,
        Or.inl ⟨Ix, inferInstance, inferInstance, inferInstance, fun x => pl (nm x),
            _, _, hpl.comp hnm, rfl⟩⟩)
    (ldRule_castMany E Kc F a d Y Ix (fun x => pl (nm x)) (hpl.comp hnm) Rd Rr hN hR
      (fun x => hrd _) Mk vf hvf)

theorem ldRule_one : Spec.ldRule_one E Kc := by
  intro F _ _ _ a d Q Y dat rst bk₀ w0 hS hQ o Nm pl hpl X hX hL Rd Rr hN hR hrd
  refine ⟨(a.S.atNew_inj d.N).comp ((Y.entO_inj o).comp hpl),
    hrd,
    fun Ix _ nm hnm Mk _ _ vf hvf => ?_⟩
  classical
  exact ldRule_recast E Kc _ X _ _ hX
    (hL _ ⟨F, inferInstance, inferInstance, inferInstance, Y, dat, rst, bk₀, w0, hS, hQ,
        Or.inr ⟨o, Ix, inferInstance, inferInstance, fun x => pl (nm x), _, _, hpl.comp hnm, rfl⟩⟩)
    (ldRule_castOne E Kc F a d Y o Ix (fun x => pl (nm x)) (hpl.comp hnm) Rd Rr hN hR
      (fun x => hrd _) Mk vf hvf)

theorem ldRule_pair : Spec.ldRule_pair E Kc := by
  intro a X Rd Rr Nm₁ Nm₂ at₁ at₂ hX h₁ h₂ hap
  have hinj : Function.Injective (Sum.elim at₁ at₂) := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (h₁.inj h)
    · exact (hap x y h).elim
    · exact (hap y x h.symm).elim
    · exact congrArg Sum.inr (h₂.inj h)
  have hrd : ∀ x, Rd (Sum.elim at₁ at₂ x) := by
    rintro (x | x)
    · exact h₁.rd x
    · exact h₂.rd x
  refine ⟨hinj, hrd, fun Ix _ nm hnm Mk _ _ vf hvf => ?_⟩
  classical
  let p : Ix → Prop := fun i => ∃ x, nm i = Sum.inl x
  have hq : ∀ i : {i // ¬ p i}, ∃ y, nm i.1 = Sum.inr y := fun i => by
    rcases h : nm i.1 with x | y
    · exact (i.2 ⟨x, h⟩).elim
    · exact ⟨y, rfl⟩
  let n₁ : {i // p i} → Nm₁ := fun i => i.2.choose
  let n₂ : {i // ¬ p i} → Nm₂ := fun i => (hq i).choose
  have e₁ : ∀ i, nm i.1 = Sum.inl (n₁ i) := fun i => i.2.choose_spec
  have e₂ : ∀ i, nm i.1 = Sum.inr (n₂ i) := fun i => (hq i).choose_spec
  have j₁ : Function.Injective n₁ := fun i i' h => Subtype.ext (hnm (by rw [e₁, e₁, h]))
  have j₂ : Function.Injective n₂ := fun i i' h => Subtype.ext (hnm (by rw [e₂, e₂, h]))
  have a₁ : ∀ i, at₁ (n₁ i) = Sum.elim at₁ at₂ (nm i.1) := fun i =>
    (congrArg (Sum.elim at₁ at₂) (e₁ i)).symm
  have a₂ : ∀ i, at₂ (n₂ i) = Sum.elim at₁ at₂ (nm i.1) := fun i =>
    (congrArg (Sum.elim at₁ at₂) (e₂ i)).symm
  have b₁ := h₁.pend _ n₁ j₁ ({i // p i} → E) (fun M => M) Function.bijective_id
  have b₂ := h₂.pend _ n₂ j₂ ({i // ¬ p i} → E) (fun M => M) Function.bijective_id
  have bp := LdPend.JD.pair _ _ Rd Rr (fun _ h => ⟨h, h⟩) (fun _ h => ⟨h, h⟩)
    (fun n hn => by
      rcases hn with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact h₁.rd _
      · exact h₂.rd _) (.base _ b₁) (.base _ b₂)
  have hi : Function.Injective fun x => Sum.elim at₁ at₂ (nm x) := hinj.comp hnm
  let ee : ({i // p i} → E) × ({i // ¬ p i} → E) ≃ Mk :=
    (Equiv.piEquivPiSubtypeProd p fun _ => E).symm.trans (Equiv.ofBijective vf hvf).symm
  have hee : ∀ M, vf (ee M) = (Equiv.piEquivPiSubtypeProd p fun _ => E).symm M := fun M =>
    Equiv.ofBijective_apply_symm_apply vf hvf _
  have hval : ∀ (M : ({i // p i} → E) × ({i // ¬ p i} → E)) (n : a.S.Ent),
      (plOwn (fun x => at₁ (n₁ x)) n ∨ plOwn (fun x => at₂ (n₂ x)) n) →
      (if plOwn (fun x => at₁ (n₁ x)) n then
            plVal (fun x => at₁ (n₁ x)) (fun M : {i // p i} → E => M) M.1 n
          else plVal (fun x => at₂ (n₂ x)) (fun M : {i // ¬ p i} → E => M) M.2 n) =
        plVal (fun x => Sum.elim at₁ at₂ (nm x)) vf (ee M) n := by
    intro M n hn
    rcases hn with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [if_pos ⟨i, rfl⟩]
      have l1 : plVal (fun x => at₁ (n₁ x)) (fun M : {i // p i} → E => M) M.1 (at₁ (n₁ i)) =
          M.1 i :=
        (h₁.inj.comp j₁).extend_apply _ _ i
      have l2 : plVal (fun x => Sum.elim at₁ at₂ (nm x)) vf (ee M) (Sum.elim at₁ at₂ (nm i.1)) =
          vf (ee M) i.1 :=
        hi.extend_apply _ _ i.1
      have l3 : (Equiv.piEquivPiSubtypeProd p fun _ => E).symm M i.1 = M.1 i := dif_pos i.2
      have r : plVal (fun x => Sum.elim at₁ at₂ (nm x)) vf (ee M) (at₁ (n₁ i)) = M.1 i := by
        rw [a₁ i, l2, hee, l3]
      exact l1.trans r.symm
    · have hno : ¬ plOwn (fun x => at₁ (n₁ x)) (at₂ (n₂ i)) := fun ⟨i', h'⟩ => hap _ _ h'
      rw [if_neg hno]
      have l1 : plVal (fun x => at₂ (n₂ x)) (fun M : {i // ¬ p i} → E => M) M.2 (at₂ (n₂ i)) =
          M.2 i :=
        (h₂.inj.comp j₂).extend_apply _ _ i
      have l2 : plVal (fun x => Sum.elim at₁ at₂ (nm x)) vf (ee M) (Sum.elim at₁ at₂ (nm i.1)) =
          vf (ee M) i.1 :=
        hi.extend_apply _ _ i.1
      have l3 : (Equiv.piEquivPiSubtypeProd p fun _ => E).symm M i.1 = M.2 i := dif_neg i.2
      have r : plVal (fun x => Sum.elim at₁ at₂ (nm x)) vf (ee M) (at₂ (n₂ i)) = M.2 i := by
        rw [a₂ i, l2, hee, l3]
      exact l1.trans r.symm
  refine ldRule_recast E Kc a X _ _ hX (hX _ bp) ⟨fun _ h => h, fun _ h => h, ?_, ?_, ee, hval⟩
  · rintro n ⟨x, rfl⟩
    exact hrd _
  · intro n
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨i.1, (a₁ i).symm⟩
      · exact ⟨i.1, (a₂ i).symm⟩
    · rintro ⟨i, rfl⟩
      by_cases hp : p i
      · exact Or.inl ⟨⟨i, hp⟩, a₁ ⟨i, hp⟩⟩
      · exact Or.inr ⟨⟨i, hp⟩, a₂ ⟨i, hp⟩⟩

omit [Fintype E] in
theorem ldRule_less : Spec.ldRule_less E Kc := fun a X _ Rd' _ Rr' _ at' hX h h1 h2 h3 =>
  ⟨h.inj, h3,
    fun Ix _ nm hnm Mk _ _ vf hvf =>
      ldRule_recast E Kc a X _
        ⟨Rd', Rr', plOwn fun x => at' (nm x), Mk, plVal (fun x => at' (nm x)) vf⟩ hX
        (h.pend Ix nm hnm Mk vf hvf)
        ⟨h1, h2, fun _ ⟨_, hx⟩ => hx ▸ h3 _, fun _ => Iff.rfl, Equiv.refl _, fun _ _ _ => rfl⟩⟩

omit [Fintype E] in
theorem ldRule_sub : Spec.ldRule_sub E Kc := fun _ _ _ _ _ _ _ f h hf =>
  ⟨h.inj.comp hf, fun _ => h.rd _,
    fun Ix _ nm hnm Mk _ _ vf hvf => h.pend Ix (fun x => f (nm x)) (hf.comp hnm) Mk vf hvf⟩

omit [Fintype E] in
theorem ldRule_mono : Spec.ldRule_mono E Kc := fun _ _ _ _ _ _ _ hX h =>
  ⟨h.inj, h.rd, fun Ix _ nm hnm Mk _ _ vf hvf => hX _ (h.pend Ix nm hnm Mk vf hvf)⟩

omit [Fintype E] in
theorem ldRule_as :
    Spec.ldRule_as E Kc := fun a X Rd Rr _ at' hX h Ix _ nm hnm Mk _ _ vf hvf own val ho hv =>
  ldRule_recast E Kc a X _ ⟨Rd, Rr, own, Mk, val⟩ hX (h.pend Ix nm hnm Mk vf hvf)
    ⟨fun _ h' => h', fun _ h' => h', fun n hn => by
      obtain ⟨x, rfl⟩ := (ho n).1 hn
      exact h.rd _, fun n => (ho n).symm, Equiv.refl _, fun M n hn => by
      obtain ⟨x, rfl⟩ := hn
      have l : plVal (fun x => at' (nm x)) vf M (at' (nm x)) = vf M x :=
        (h.inj.comp hnm).extend_apply _ _ x
      exact l.trans (hv M x).symm⟩

end
end Cb
