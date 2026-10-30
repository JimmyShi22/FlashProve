-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeListProofs.lean: the proofs of the statements of Cb/Gen/CodeList.lean.

Nothing is assumed beyond the hypotheses of the statements, which stand in their own text.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeList
import Cb.Gen.JohnsonListProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks

/-- Below the Johnson radius the distance is positive. -/
theorem InJohnson.pos {n d e : ℕ} (h : InJohnson n d e) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    unfold InJohnson at h
    rw [Nat.sub_zero, ← sq] at h
    exact absurd (lt_of_lt_of_le h (Nat.pow_le_pow_left (Nat.sub_le n e) 2)) (lt_irrefl _)
  · exact hd

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Finite E] [Algebra F E]

omit [Fintype F] in
theorem mca_iff_at : Spec.mca_iff_at F E := fun _ _ _ => Iff.rfl

/-- Unique decoding as a list: under `hd` and `h2`, `ListAt` with L = 1. -/
theorem listAt_one {F E : Type} [Field F] [Field E] [Finite E] [Algebra F E] (C : Code.Enc F)
    {d e : ℕ} (hd : HasDist C.G d) (h2 : 2 * e < d) (R : Type) [Finite R] : C.ListAt E R e 1 :=
  fun _ => cnt_le_of_forall_finset fun _ hY => Finset.card_le_one.mpr fun _ ha _ hb =>
    DecodesTo.unique (HasDist.map (E := E) hd) h2 (hY _ ha) (hY _ hb)

theorem listProps_of_props : Spec.listProps_of_props F E := fun C h =>
  { place := h.place
    dist := h.dist
    pos := h.d_pos
    hides := h.hides
    list := fun R _ => listAt_one C h.dist h.unique R
    mca := h.mca }

theorem props_of_listProps : Spec.props_of_listProps F E := fun _ _ h h2 =>
  { place := h.place
    dist := h.dist
    unique := h2
    mca := h.mca
    hides := h.hides }

theorem listProps_of_johnson : Spec.listProps_of_johnson F E := fun C h hJ hm =>
  { h with
    list := fun R _ f => johnson_enc F E C C.e h.dist hJ R f
    mca := hm }

theorem listProps_mono : Spec.listProps_mono F E := fun _ _ _ hL h =>
  { h with list := fun R _ f => (h.list R f).trans hL }

theorem listProps_one_le : Spec.listProps_one_le F E := by
  intro C L h
  have h1 := h.list Unit (fun a => (C.GE E).mulVec ((0 : Unit → Fin C.k → E) a))
  have h2 := card_le_cnt ({0} : Finset (Unit → Fin C.k → E))
    (P := fun M => DecodesTo (C.GE E) C.e (fun a => (C.GE E).mulVec ((0 : Unit → Fin C.k → E) a)) M)
    (fun x hx => by
      rw [Finset.mem_singleton.mp hx]
      exact decodesTo_mulVec _ _ _)
  rw [Finset.card_singleton] at h2
  exact h2.trans h1

theorem core_props : Spec.core_props F E := fun C h =>
  { place := h.place
    dist := h.dist
    unique := by
      show 2 * 0 < C.d
      exact h.pos
    mca := (C.atRadius 0 1).mca_third (E := E) (d := C.d) (e := 0) h.dist h.pos
    hides := h.hides }

omit [Fintype F] in
theorem prox_third : Spec.prox_third F E := fun C hd =>
  { list := fun _ he R _ => listAt_one C hd (by omega) R
    mca := fun e he R _ => C.mca_third (E := E) hd he R }

omit [Fintype F] in
theorem prox_johnson : Spec.prox_johnson F E := fun C _ hd hm =>
  { list := fun e he R _ f => johnson_enc F E C e hd he R f
    mca := hm }

theorem listProps_of_prox : Spec.listProps_of_prox F E := fun _ _ _ _ e _ _ hc hp he hL hb =>
  { place := hc.place
    dist := hc.dist
    pos := hc.pos
    hides := hc.hides
    list := fun R _ f => (hp.list e he R f).trans (hL _)
    mca := fun R _ f₀ f₁ => (hp.mca e he R f₀ f₁).trans (hb _) }

end
end Cb
