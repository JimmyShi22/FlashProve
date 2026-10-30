-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartIdxFmt.lean: a segment's conditions and its well-formedness depend on a format of the
encoded index (`IdxFmt`, Cb/Gen/Tensor.lean) only through the number of rows and the sum of the two
numbers of column variables.

Book-keeping for the arithmetisation: the conditions do not depend on how the column variables of
the index matrix are split between the rows of the encoded index and the places inside a row. A
definition, the statement (`Cb.Spec.ldPartIdxFmt`) and proofs. Generic auxiliary lemmas: for whoever
has a model's segments at one format and needs them at another (another code; another split of the
column variables).

Main names:
  `Φ.Same Φ'`: the same number of rows; hi + lo = hi' + lo'.
  `Spec.ldPartIdxFmt`: `Φ.Same Φ'` ⇒ for families: the same values at all vertices, well formed at
    the one iff at the other; for segments: S.WF Φ ⇔ S.WF Φ', S.Holds Φ x W A ⇔ S.Holds Φ' x W A.

Limits: nothing on the code, on layouts, on messages of the encoded index: these do read the split.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSpec

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

/-- the same number of rows and of column variables -/
def IdxFmt.Same {F : Type} (Φ Φ' : IdxFmt F) : Prop := Φ.h = Φ'.h ∧ Φ.hi + Φ.lo = Φ'.hi + Φ'.lo

def Spec.ldPartIdxFmt : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (Φ Φ' : IdxFmt F), Φ.Same Φ' →
    (∀ (f : Fam X E), (f.WF Φ ↔ f.WF Φ') ∧ ∀ x W A b, f.val Φ x W A b = f.val Φ' x W A b) ∧
    ∀ (S : SegSpec X F E), (S.WF Φ ↔ S.WF Φ') ∧ ∀ x W A, S.Holds Φ x W A ↔ S.Holds Φ' x W A

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E] {Φ Φ' : IdxFmt F} (h : Φ.Same Φ')
include h

theorem IdxFmt.form_same (g ψ : ℕ → E) (W : ℕ → ℕ → F) : Φ.form g ψ W = Φ'.form g ψ W := by
  unfold IdxFmt.form
  rw [h.1, h.2]

theorem IdxAtom.at_same (a : IdxAtom E) (W : ℕ → ℕ → F) (pt : ℕ → E) : a.at Φ W pt = a.at Φ' W pt :=
  IdxFmt.form_same h _ _ _

theorem IdxAtom.ok_same (a : IdxAtom E) (v : ℕ) : a.OK Φ v ↔ a.OK Φ' v := by
  unfold IdxAtom.OK
  simp only [IdxAtom.at_same h]

theorem Atom0.val_same (a : Atom0 E) (v : ℕ) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    a.val Φ v W A b = a.val Φ' v W A b := by
  cases a with
  | cell _ => rfl
  | idx a => exact IdxAtom.at_same h a W _

theorem Atom0.wf_same (a : Atom0 E) (v : ℕ) : a.WF Φ v ↔ a.WF Φ' v := by
  cases a with
  | cell _ => exact Iff.rfl
  | idx a => exact IdxAtom.ok_same h a v

theorem Poly0.val_same (P : Poly0 X E) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    P.val Φ x W A b = P.val Φ' x W A b := by
  unfold Poly0.val
  simp only [Atom0.val_same h]

theorem Poly0.wf_same (P : Poly0 X E) : P.WF Φ ↔ P.WF Φ' :=
  and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun _ => Atom0.wf_same h (P.atom j) P.v)

theorem Atom.val_same (a : Atom X E) (v : ℕ) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    a.val Φ v x W A b = a.val Φ' v x W A b := by
  cases a with
  | base a => exact Atom0.val_same h a v W A b
  | sum w P => exact Finset.sum_congr rfl fun j _ => Poly0.val_same h P x W A _

theorem Atom.wf_same (a : Atom X E) (v : ℕ) : a.WF Φ v ↔ a.WF Φ' v := by
  cases a with
  | base a => exact Atom0.wf_same h a v
  | sum w P => exact and_congr Iff.rfl (Poly0.wf_same h P)

theorem Fam.val_same (f : Fam X E) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    f.val Φ x W A b = f.val Φ' x W A b := by
  unfold Fam.val
  simp only [Atom.val_same h]

theorem Fam.wf_same (f : Fam X E) : f.WF Φ ↔ f.WF Φ' :=
  and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun _ => Atom.wf_same h (f.atom j) f.v)

theorem SegSpec.wf_same (S : SegSpec X F E) : S.WF Φ ↔ S.WF Φ' :=
  and_congr (forall_congr' fun f => forall_congr' fun _ => Fam.wf_same h f)
    (forall_congr' fun k => forall_congr' fun _ => Fam.wf_same h k.1)

theorem SegSpec.holds_same (S : SegSpec X F E) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) :
    S.Holds Φ x W A ↔ S.Holds Φ' x W A := by
  unfold SegSpec.Holds
  simp only [Fam.val_same h]

end

theorem ldPartIdxFmt : Spec.ldPartIdxFmt := fun _ _ _ _ _ _ _ _ h =>
  ⟨fun f => ⟨Fam.wf_same h f, Fam.val_same h f⟩,
    fun S => ⟨SegSpec.wf_same h S, SegSpec.holds_same h S⟩⟩

end Cb
