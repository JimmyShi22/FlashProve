-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectSendersStdM.lean: for toys: a family of standard oracle messages (data and one pad
entry, plain format) has a layout in the sense of the standard sender, and the layout meets its
conditions (`Sig.StdL.OK`) if every member meets its own (`StdM.OK`).

In standard terms: a lemma for example instances: the oracle messages of Cb/Obj/LdObjectToyKit.lean
fit the general layout (`Sig.StdL`) from which the library's standard honest sender is made.

Definitions, statement (`Cb.Spec.stdMFam_ok`) and proof.
The toys' oracle messages are the records `StdM` of Cb/Obj/LdObjectToyKit.lean (a code, data entries
and one pad entry under a bijection `place`, the sample row with a pad). The object of
Cb/Obj/LdObjectData.lean (`LdObjZ`) asks (`LdObjZ.Hyp`, field sndIs) that the seven senders of its
two tests for linear constraints and of its link are the standard senders of Cb/Ld/LdSendStdL.lean,
which are made from a layout `Y : N.StdL F`. This file joins the two.

Main names:
  `stdMFam M`: the family with the members `(M a).om`. (`Sig.one M.om` is the case of one name, by
    definition.)
  `stdMFamL M`: its layout: data := `(M a).Dt`; no free entry; pad := the one pad entry, an element
    of E; plain format.
  `Spec.stdMFam_ok`: if every `(M a).OK (L a) (t a)`, then `(stdMFamL M).OK t`; and the place of the
    datum i is `(M a).place (inl i)`.

Notation: `L`: a map `O → ℕ` (`(M a).OK (L a) (t a)`, Cb/Obj/LdObjectToyKit.lean, says that `L a`
bounds the lists of the code of `M a` at its radius); `atD a i`: of type `(N.om a).C.J`
(`Sig.StdL.atD`, Cb/Ld/LdSendStdL.lean: the place of the datum i in the message of a).

Limits: this file does not say that the toys' own senders (`M.snd`, Cb/Obj/LdObjectToyKit.lean;
their coins are one element of E) are the standard senders at this layout: they are not, by type
(the coins differ); they send the same messages.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdL
import Cb.Obj.LdObjectToyKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E P O : Type} [Field E] [Fintype E] [Fintype P] [Fintype O]
  [DecidableEq O] (M : O → StdM E P)

/-- The family. -/
@[reducible] def stdMFam : Sig E := { O := O, om := fun a => (M a).om }

/-- the entries of a message: (data, no free entry), the pad -/
def stdMNu (a : O) : (M a).Cm.J ≃ ((M a).Dt ⊕ Empty) ⊕ Unit :=
  (M a).place.symm.trans (Equiv.sumCongr (Equiv.sumEmpty _ _).symm (Equiv.refl Unit))

/-- The layout. -/
@[reducible] def stdMFamL : (stdMFam M).StdL E where
  Dt := fun a => (M a).Dt
  Fr := fun _ => Empty
  Pd := fun _ => Unit
  ν := stdMNu M
  En := fun a => (M a).Cm.Nn
  upM := fun _ m => m
  upR := fun _ r => r
  msgOf := fun a x η j => withPad (F := E) x η (stdMNu M a j)

end

def Spec.stdMFam_ok : Prop :=
  ∀ (E P O : Type) [Field E] [Fintype E] [Fintype P] [Fintype O] [DecidableEq O]
      (M : O → StdM E P) (L t : O → ℕ),
    (∀ a, (M a).OK (L a) (t a)) →
    (stdMFamL M).OK t ∧ ∀ a i, (stdMFamL M).atD a i = (M a).place (Sum.inl i)

theorem stdMFam_ok : Spec.stdMFam_ok := by
  intro E P O _ _ _ _ _ M L t h
  refine ⟨⟨fun _ _ _ => rfl, fun a x η n => ?_, fun a => ?_, fun a => (h a).zk⟩, fun _ _ => rfl⟩
  · show withPad (F := E) x η (stdMNu M a ((stdMNu M a).symm n)) = _
    rw [Equiv.apply_symm_apply]
  · have e : (M a).Z.comap (stdMNu M a).symm =
        Sample.pad E (M a).μ ((M a).Dt ⊕ Empty) Unit (M a).B (Sum.elim (M a).plc fun e => e.elim)
          (fun _ => 1) (M a).b := by
      show ({ D := (M a).Z₀.D, S := (M a).Z₀.S,
              mat := fun ρ s n => (M a).Z₀.mat ρ s ((M a).place.symm ((stdMNu M a).symm n)),
              err := (M a).Z₀.err } : Sample E (((M a).Dt ⊕ Empty) ⊕ Unit)) = _
      congr 1
      funext ρ s n
      rcases n with (i | e) | u
      · show (M a).Z₀.mat ρ s ((M a).place.symm ((M a).place (Sum.inl i))) = _
        rw [Equiv.symm_apply_apply]
        rfl
      · exact e.elim
      · show (M a).Z₀.mat ρ s ((M a).place.symm ((M a).place (Sum.inr u))) = _
        rw [Equiv.symm_apply_apply]
        rfl
    show ((M a).Z.comap (stdMNu M a).symm).Private E fun _ => True
    rw [e]
    exact fun ρ _ x =>
      ood_private_pad E E (M a).μ ((M a).Dt ⊕ Empty) Unit (M a).B
        _ _ _ std_padBasis ρ ((h a).ne0 ρ.2) x

end Cb
