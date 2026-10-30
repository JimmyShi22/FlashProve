-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldShape.lean: this file carries out a reshaping row by row on an interleaving. A reshaping
(`Reshape`, Cb/Ld/LdBatShape.lean) is maps that carry the native words (wd), the pairs (message,
randomness) forth and back (up, dn) and the linear forms (fm) of one code over to another code at
the same long positions.

Two definitions (`Reshape.ilRowP`, `Reshape.ilR`), one statement (`Spec.ldShape_ilR`) and its proof.
Generic: any field, any two codes read at the same, finitely many, long positions, any finite set of
rows. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
For `ρ : Reshape C C'`, `ρ.Laws`: wd acts long position by long position and is injective; it takes
the encoding of w to the encoding of up w; where wd f agrees at a long position with the encoding of
a pair w' of C', f agrees there with the encoding of dn w'; dn undoes up; and fm a on the message of
a pair w' of C' has the value of a on the message of dn w'. `ρ.Fix e`: a pair whose encoding is
within e long positions of some wd f is fixed by up after dn.

Why: Cb/Ld/LdBatShape.lean has the operations refl, comp, fam, pairL, pairR on reshapings, and none
for rows. A member of a group has mask rows under a mask code; to see that code in another shape
(a short native word as a long word of copies) the reshaping of one row
has to be applied to each row.

Main names: `Reshape.ilR`, `Spec.ldShape_ilR` (see their doc comments).

Limits: this file says nothing on native positions, so nothing on what an encoding hides. It says
nothing on any protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatShape

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-- the row i of a pair (message, randomness) of an interleaved code -/
def Reshape.ilRowP {E P : Type} {C : LdCode E P} {R : Type} [Fintype R] [DecidableEq R]
    (w : ((C.il R).J → E) × ((C.il R).Q → E)) (i : R) : (C.J → E) × (C.Q → E) :=
  (fun j => w.1 (i, j), fun q => w.2 (i, q))

/-- The reshaping ρ carried out row by row. -/
def Reshape.ilR {E P : Type} {C C' : LdCode E P} (ρ : Reshape C C') (R : Type)
    [Fintype R] [DecidableEq R] : Reshape (C.il R) (C'.il R) where
  wd := fun f p s => ρ.wd (C.rowW f s.1) p s.2
  up := fun w =>
    (fun j => (ρ.up (Reshape.ilRowP w j.1)).1 j.2, fun q => (ρ.up (Reshape.ilRowP w q.1)).2 q.2)
  dn := fun w =>
    (fun j => (ρ.dn (Reshape.ilRowP w j.1)).1 j.2, fun q => (ρ.dn (Reshape.ilRowP w q.1)).2 q.2)
  fm := fun a j => ρ.fm (fun j' => a (j.1, j')) j.2

/-- States: under `ρ.Laws`, `ρ.ilR R` has the laws too and, at every radius e, has `Fix e` if ρ has
(a row of a word is no farther from the row of a codeword than the word from the codeword). -/
def Spec.ldShape_ilR : Prop :=
  ∀ (E P : Type) [Field E] [Finite P] (C C' : LdCode E P) (ρ : Reshape C C') (R : Type)
      [Fintype R] [DecidableEq R],
    ρ.Laws → (ρ.ilR R).Laws ∧ ∀ e, ρ.Fix e → (ρ.ilR R).Fix e

theorem ldShape_ilR : Spec.ldShape_ilR := by
  intro E P _ _ C C' ρ R _ _ hL
  refine ⟨⟨fun f g x h => ?_, fun w => ?_, fun f w x h => ?_, fun w => ?_,
      fun f g h => ?_, fun a w => ?_⟩,
    fun e hF f w h => ?_⟩
  · funext α
    obtain ⟨i, α⟩ := α
    exact congrFun (hL.loc (C.rowW f i) (C.rowW g i) x (funext fun β => congrFun h (i, β))) α
  · funext p s
    obtain ⟨i, s⟩ := s
    exact congrFun (congrFun (hL.enc (Reshape.ilRowP w i)) p) s
  · funext α
    obtain ⟨i, α⟩ := α
    exact congrFun
      (hL.off (C.rowW f i) (Reshape.ilRowP w i) x (funext fun β => congrFun h (i, β))) α
  · refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
    · obtain ⟨i, j⟩ := j
      exact congrFun (congrArg Prod.fst (hL.inj (Reshape.ilRowP w i))) j
    · obtain ⟨i, q⟩ := q
      exact congrFun (congrArg Prod.snd (hL.inj (Reshape.ilRowP w i))) q
  · funext p s
    obtain ⟨i, s⟩ := s
    have e := hL.winj (C.rowW f i) (C.rowW g i)
      (funext fun p => funext fun s => congrFun (congrFun h p) (i, s))
    exact congrFun (congrFun e p) s
  · show ∑ j : R × C'.J, ρ.fm (fun j' => a (j.1, j')) j.2 * w.1 j =
      ∑ j : R × C.J, a j * (ρ.dn (Reshape.ilRowP w j.1)).1 j.2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hL.val (fun j => a (i, j)) (Reshape.ilRowP w i)
  · have hr : ∀ i, ρ.up (ρ.dn (Reshape.ilRowP w i)) = Reshape.ilRowP w i := fun i =>
      hF (C.rowW f i) (Reshape.ilRowP w i)
        (le_trans (cnt_mono fun x hx hx' => hx (funext fun β => congrFun hx' (i, β))) h)
    refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
    · obtain ⟨i, j⟩ := j
      exact congrFun (congrArg Prod.fst (hr i)) j
    · obtain ⟨i, q⟩ := q
      exact congrFun (congrArg Prod.snd (hr i)) q

end Cb
