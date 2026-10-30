-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdMFree.lean: for toys: a family of standard oracle messages some of whose entries are
free (masks): its layout, and the layout's conditions from the messages' own.

This file gives, for small example instances, a layout of the messages of a family of oracle
messages: which entries of each message are data, which are free, for the prover's coins, and which
is the pad.

Definitions, one statement (`Cb.Spec.stdMFamF_ok`) and its proof. It widens
Cb/Obj/LdObjectSendersStdM.lean (no free entry).

Main names:
  `M : O → StdM E P`: a finite family of standard oracle messages (Cb/Obj/LdObjectToyKit.lean:
    entries "Dt" and one pad entry; the row with a pad as sample).
  `free a i`: which of the entries "Dt" of the member a are free: coins of the sender, masks of
    coming blocks. All others are data. (A member all of whose entries are free is mask-only.)
  `stdMFamLF M free`: the layout (Cb/Ld/LdSendStdL.lean: `N.StdL E`) of the family `stdMFam M`, in
    the plain format.
  `Spec.stdMFamF_ok`: (∀ a, (M a).OK (L a) (t a)) (`StdM.OK`, Cb/Obj/LdObjectToyKit.lean) ⇒
    `(stdMFamLF M free).OK t` (`Sig.StdL.OK`: what it asks: the head of Cb/Ld/LdSendStdL.lean); data
    and free entries stand at the places (M a).place (inl i).
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectSendersStdM
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E P O : Type} [Field E] [Fintype E] [Fintype P] [Fintype O] [DecidableEq O]
  (M : O → StdM E P) (free : ∀ a, (M a).Dt → Prop) [∀ a, DecidablePred (free a)]

/-- the entries "Dt" as (data, free entries) -/
def stdMSp (a : O) : (M a).Dt ≃ {i // ¬ free a i} ⊕ {i // free a i} :=
  ((Equiv.sumComm _ _).trans (Equiv.sumCompl (free a))).symm

/-- the entries of a message: (data, free entries), the pad -/
def stdMNuF (a : O) : (M a).Cm.J ≃ ({i // ¬ free a i} ⊕ {i // free a i}) ⊕ Unit :=
  (M a).place.symm.trans (Equiv.sumCongr (stdMSp M free a) (Equiv.refl Unit))

/-- The layout. -/
@[reducible] def stdMFamLF : (stdMFam M).StdL E where
  Dt := fun a => {i // ¬ free a i}
  Fr := fun a => {i // free a i}
  Pd := fun _ => Unit
  ν := stdMNuF M free
  En := fun a => (M a).Cm.Nn
  upM := fun _ m => m
  upR := fun _ r => r
  msgOf := fun a x η j => withPad (F := E) x η (stdMNuF M free a j)

end

def Spec.stdMFamF_ok : Prop :=
  ∀ (E P O : Type) [Field E] [Fintype E] [Fintype P] [Fintype O] [DecidableEq O] (M : O → StdM E P)
      (free : ∀ a, (M a).Dt → Prop) [∀ a, DecidablePred (free a)] (L t : O → ℕ),
    (∀ a, (M a).OK (L a) (t a)) →
    (stdMFamLF M free).OK t ∧
    (∀ a i, (stdMFamLF M free).atD a i = (M a).place (Sum.inl i.1)) ∧
    ∀ a i, (stdMFamLF M free).atF a i = (M a).place (Sum.inl i.1)

theorem stdMFamF_ok : Spec.stdMFamF_ok := by
  intro E P O _ _ _ _ _ M free _ L t h
  refine ⟨⟨fun _ _ _ => rfl, fun a x η n => ?_, fun a => ?_, fun a => (h a).zk⟩,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · show withPad (F := E) x η (stdMNuF M free a ((stdMNuF M free a).symm n)) = _
    rw [Equiv.apply_symm_apply]
  · have e : (M a).Z.comap (stdMNuF M free a).symm =
        Sample.pad E (M a).μ ({i // ¬ free a i} ⊕ {i // free a i}) Unit (M a).B
          (fun x => (M a).plc ((stdMSp M free a).symm x)) (fun _ => 1) (M a).b := by
      show ({ D := (M a).Z₀.D, S := (M a).Z₀.S,
              mat := fun ρ s n => (M a).Z₀.mat ρ s ((M a).place.symm ((stdMNuF M free a).symm n)),
              err := (M a).Z₀.err } : Sample E (({i // ¬ free a i} ⊕ {i // free a i}) ⊕ Unit)) = _
      congr 1
      funext ρ s n
      rcases n with x | u
      · show (M a).Z₀.mat ρ s
            ((M a).place.symm ((M a).place (Sum.inl ((stdMSp M free a).symm x)))) = _
        rw [Equiv.symm_apply_apply]
        rfl
      · show (M a).Z₀.mat ρ s ((M a).place.symm ((M a).place (Sum.inr u))) = _
        rw [Equiv.symm_apply_apply]
        rfl
    show ((M a).Z.comap (stdMNuF M free a).symm).Private E fun _ => True
    rw [e]
    exact fun ρ _ x =>
      ood_private_pad E E (M a).μ ({i // ¬ free a i} ⊕ {i // free a i}) Unit (M a).B
        _ _ _ std_padBasis ρ ((h a).ne0 ρ.2) x

end Cb
