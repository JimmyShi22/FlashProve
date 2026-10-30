-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSpecProofs.lean: the proofs of the two small laws stated in Cb/Req/ReqSpec.lean.

Main names (statements and hypotheses: Cb/Req/ReqSpec.lean):
  `ext_vtx`: a multilinear extension at a vertex of the cube.
  `fam_val_congr`: dependence of a family's value on the places read.

Limits: what the head of Cb/Req/ReqSpec.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSpec

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

theorem ext_vtx : Spec.ext_vtx := by
  intro E _ v f b hb
  have hz : (fun t : Fin v => vtx (E := E) v b (0 + t)) = Alg.corner (Alg.bits v b) := by
    funext t
    simp [vtx, Alg.corner, Alg.bits, t.2]
  unfold Blocks.ext
  simp only [eqN_eq, hz]
  show Alg.mleN f (Alg.corner (Alg.bits v b)) = f b
  rw [Alg.mleN_eq_mle, Alg.mle_corner, Alg.num_bits hb]

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

theorem CForm.val_congr (f : CForm E) {A A' : ℕ → ℕ → ℕ → E}
    (h : ∀ t ∈ f.terms, A t.2.1 t.2.2.1 t.2.2.2 = A' t.2.1 t.2.2.1 t.2.2.2) :
    f.val A = f.val A' := by
  unfold CForm.val
  rw [List.map_congr_left fun t ht => by rw [h t ht]]

theorem Term.val_congr (t : Term X E) (x : X) (b : ℕ)
    {Y Y' : ℕ → E} (h : ∀ j ∈ t.atoms, Y j = Y' j) : t.val x b Y = t.val x b Y' := by
  unfold Term.val
  rw [List.map_congr_left h]

theorem Atom0.val_congr (a : Atom0 E) (Φ : IdxFmt F) (v : ℕ) (W : ℕ → ℕ → F) {A A' : ℕ → ℕ → ℕ → E}
    (h : ∀ p ∈ a.places v, A p.1 p.2.1 p.2.2 = A' p.1 p.2.1 p.2.2) {b : ℕ} (hb : b < 2 ^ v) :
    a.val Φ v W A b = a.val Φ v W A' b := by
  cases a with
  | cell f => exact CForm.val_congr (f b) fun t ht => h t.2 ⟨b, hb, t, ht, rfl⟩
  | idx a => rfl

theorem Poly0.val_congr (P : Poly0 X E) (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F)
    {A A' : ℕ → ℕ → ℕ → E} (hw : P.WF Φ)
    (h : ∀ p ∈ P.places, A p.1 p.2.1 p.2.2 = A' p.1 p.2.1 p.2.2) {b : ℕ} (hb : b < 2 ^ P.v) :
    P.val Φ x W A b = P.val Φ x W A' b := by
  unfold Poly0.val
  rw [List.map_congr_left fun t ht =>
      Term.val_congr t x b fun j hj =>
        Atom0.val_congr (P.atom j) Φ P.v W (fun p hp => h p ⟨j, hw.1 t ht j hj, hp⟩) hb]

theorem Atom.val_congr (a : Atom X E) (Φ : IdxFmt F) (v : ℕ) (x : X) (W : ℕ → ℕ → F)
    {A A' : ℕ → ℕ → ℕ → E} (hw : a.WF Φ v)
    (h : ∀ p ∈ a.places v, A p.1 p.2.1 p.2.2 = A' p.1 p.2.1 p.2.2) {b : ℕ} (hb : b < 2 ^ v) :
    a.val Φ v x W A b = a.val Φ v x W A' b := by
  cases a with
  | base a => exact Atom0.val_congr a Φ v W h hb
  | sum w P =>
    refine Finset.sum_congr rfl fun j hj => Poly0.val_congr P Φ x W hw.2 h ?_
    rw [hw.1, pow_add]
    calc b * 2 ^ w + j < b * 2 ^ w + 2 ^ w := Nat.add_lt_add_left (Finset.mem_range.1 hj) _
      _ = (b + 1) * 2 ^ w := by ring
      _ ≤ 2 ^ v * 2 ^ w := Nat.mul_le_mul_right _ hb

end

theorem fam_val_congr : Spec.fam_val_congr := by
  intro X F E _ _ _ f Φ x W A A' hw h b hb
  unfold Fam.val
  rw [List.map_congr_left fun t ht =>
      Term.val_congr t x b fun j hj =>
        Atom.val_congr (f.atom j) Φ f.v x W (hw.2 j (hw.1 t ht j hj))
          (fun p hp => h p ⟨j, hw.1 t ht j hj, hp⟩) hb]

end Cb
