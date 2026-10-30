-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SampleOK.lean: the sample of the code switch tells vectors apart.

The library's statement on the code switch asks of its sample map the property `Sample.OK`
(Cb/Gen/OodDec.lean): the seeds at which all answers of a given vector vanish are at most the map's
number err, unless the vector is 0. This file shows the property for the sample row with a pad of
one entry over the extension field, where the entries proper are at different corners of a cube. A
corner is given by the bits of a number.

Main definition: `reix`, a sample map under other names of the coordinates.
Main theorems.
 `ok_reix`      the property does not depend on the names of the coordinates
 `ok_pad_one`   the sample row with a pad of one entry has the property

Not claimed. Nothing on how small the map's number err is. Nothing is said of hiding.
-/
import Cb.Gen.OodDecPadProofs
import OnBytes.Slice.Draws
import OnBytes.Slice.Corners

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Cb.Ood Prob

/-- A sample map under other names of the coordinates. -/
@[reducible] def reix {E J J' : Type} (Z : Sample E J) (e : J' ≃ J) : Sample E J' :=
  { D := Z.D, S := Z.S, mat := fun ρ s j => Z.mat ρ s (e j), err := Z.err }

/-- The answers under other names are the answers of the vector that is renamed back. -/
theorem val_reix {E J J' : Type} [Field E] [Fintype J] [Fintype J'] (Z : Sample E J) (e : J' ≃ J)
    (ρ : Z.D) (v : J' → E) : (reix Z e).val ρ v = Z.val ρ (v ∘ e.symm) := by
  funext s
  show ∑ j, Z.mat ρ s (e j) * v j = ∑ j, Z.mat ρ s j * v (e.symm j)
  rw [← Equiv.sum_comp e fun j => Z.mat ρ s j * v (e.symm j)]
  simp

/-- The property of a sample map does not depend on the names of the coordinates. -/
theorem ok_reix {E J J' : Type} [Field E] [Fintype J] [Fintype J'] (Z : Sample E J) (e : J' ≃ J)
    (h : Z.OK) : (reix Z e).OK := by
  intro v hv
  have hne : v ∘ e.symm ≠ 0 := by
    intro h0
    apply hv
    funext j
    have := congrFun h0 (e j)
    simpa using this
  have e1 : (fun ρ : Z.D => (reix Z e).val ρ v = 0) = fun ρ => Z.val ρ (v ∘ e.symm) = 0 := by
    funext ρ
    rw [val_reix]
  show cnt (fun ρ : Z.D => (reix Z e).val ρ v = 0) ≤ Z.err
  rw [e1]
  exact h _ hne

/-- The sample row with a pad of one entry over the extension field has the property of a sample
map. The entry j proper is at the corner that the low a bits of idx j name. These numbers are
below 2^a and different. The factor of the pad is drawn among the elements other than 0. -/
theorem ok_pad_one (a : ℕ) {J : Type} [Fintype J] (idx : J → ℕ) (hlt : ∀ j, idx j < 2 ^ a)
    (hinj : Function.Injective idx) :
    (Sample.pad GE (Fin a) J Unit GEˣ (fun j t => (idx j).testBit t.val) (fun _ => 1)
      Units.val).OK := by
  have hpl : Function.Injective fun (j : J) (t : Fin a) => (idx j).testBit t.val :=
    fun j j' h => hinj (testBit_inj a (hlt j) (hlt j') fun t => congrFun h t)
  have hw : Function.Injective (padVal (F := GE) fun _ : Unit => (1 : GE)) := by
    intro c c' h
    funext u
    cases u
    simpa [padVal] using h
  have hon := Cb.ood_okOn_pad GE GE (Fin a) J Unit GEˣ (fun j t => (idx j).testBit t.val)
    (fun _ => 1) Units.val hpl (fun _ _ h => Units.ext h) hw
  intro v hv
  exact hon v (fun i => ⟨v (Sum.inr i), rfl⟩) hv

end OnBytes.Slice

#print axioms OnBytes.Slice.ok_reix
#print axioms OnBytes.Slice.ok_pad_one
