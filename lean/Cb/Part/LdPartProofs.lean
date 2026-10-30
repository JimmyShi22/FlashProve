-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartProofs.lean: the proofs of the four statements of Cb/Part/LdPart.lean.

Main names (statements and hypotheses: Cb/Part/LdPart.lean):
  `ldPart_form`: the tensor form at the image of a matrix over F.
  `ldPart_idx`: an index atom's extension at matrices over E.
  `ldPart_sum`: the value of a sum atom at a point.
  `ldPart_vtx`: the polynomials' values at the vertices.

The proofs:
  `ldPart_form`, `ldPart_sum`: by unfolding.
  `ldPart_idx`: the law at the unit matrices (which lie over F), then linearity of the tensor form
    and of the extension.
  `ldPart_vtx`: `ext_vtx` (Cb/Req/ReqSpecProofs.lean), kind by kind.

Limits: what the head of Cb/Part/LdPart.lean lists as not said is not said here either.
-/
import Cb.Part.LdPart
import Cb.Req.ReqSpecProofs

set_option autoImplicit false

namespace Cb

open Blocks Finset

theorem ldPart_form : Spec.ldPart_form := fun _ _ _ _ _ _ _ _ _ => rfl

theorem ldPart_sum : Spec.ldPart_sum := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- the extension of a double sum with fixed right factors -/
theorem ldPart_ext_sum2 {E : Type} [Field E] (V h K : ℕ) (G : ℕ → ℕ → ℕ → E)
    (M : ℕ → ℕ → E) (q : ℕ → E) :
    Blocks.ext V (fun b => ∑ y ∈ range h, ∑ c ∈ range K, G b y c * M y c) q =
      ∑ y ∈ range h, ∑ c ∈ range K, Blocks.ext V (fun b => G b y c) q * M y c := by
  unfold Blocks.ext
  calc
    ∑ X ∈ range (2 ^ V), eqN V 0 q X * ∑ y ∈ range h, ∑ c ∈ range K, G X y c * M y c =
        ∑ X ∈ range (2 ^ V), ∑ y ∈ range h, ∑ c ∈ range K, eqN V 0 q X * (G X y c * M y c) := by
      simp only [mul_sum]
    _ = ∑ y ∈ range h, ∑ X ∈ range (2 ^ V), ∑ c ∈ range K, eqN V 0 q X * (G X y c * M y c) :=
      sum_comm
    _ = ∑ y ∈ range h, ∑ c ∈ range K, ∑ X ∈ range (2 ^ V), eqN V 0 q X * (G X y c * M y c) :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ y ∈ range h, ∑ c ∈ range K, (∑ X ∈ range (2 ^ V), eqN V 0 q X * G X y c) * M y c := by
        refine sum_congr rfl fun y _ => sum_congr rfl fun c _ => ?_
        rw [sum_mul]
        exact sum_congr rfl fun X _ => (mul_assoc _ _ _).symm

/-- a double sum against a unit matrix -/
theorem ldPart_sum_unit {F E : Type} [Field F] [Field E] [Algebra F E] (h K : ℕ) (G : ℕ → ℕ → E)
    {y c : ℕ} (hy : y < h) (hc : c < K) :
    ∑ y' ∈ range h, ∑ c' ∈ range K, G y' c' * algebraMap F E (if y' = y ∧ c' = c then 1 else 0) =
      G y c := by
  rw [sum_eq_single y, sum_eq_single c]
  · rw [if_pos ⟨rfl, rfl⟩, map_one, mul_one]
  · intro c' _ hc'
    rw [if_neg (fun e => hc' e.2), map_zero, mul_zero]
  · intro hn
    exact absurd (mem_range.2 hc) hn
  · intro y' _ hy'
    exact sum_eq_zero fun c' _ => by rw [if_neg (fun e => hy' e.1), map_zero, mul_zero]
  · intro hn
    exact absurd (mem_range.2 hy) hn

theorem ldPart_idx : Spec.ldPart_idx := by
  intro F E _ _ _ Φ V a hOK WE q
  have key : ∀ y ∈ range Φ.h, ∀ c ∈ range (2 ^ (Φ.hi + Φ.lo)),
      Blocks.ext V (fun b => a.g (vtx V b) y * eqN (Φ.hi + Φ.lo) 0 (a.ψ (vtx V b)) c) q =
        a.g q y * eqN (Φ.hi + Φ.lo) 0 (a.ψ q) c := by
    intro y hy c hc
    have h0 := hOK (fun y' c' => if y' = y ∧ c' = c then 1 else 0) q
    have e1 : ∀ pt : ℕ → E, a.at Φ (fun y' c' => if y' = y ∧ c' = c then (1 : F) else 0) pt =
        a.g pt y * eqN (Φ.hi + Φ.lo) 0 (a.ψ pt) c := fun pt =>
      ldPart_sum_unit (F := F) Φ.h (2 ^ (Φ.hi + Φ.lo))
        (fun y' c' => a.g pt y' * eqN (Φ.hi + Φ.lo) 0 (a.ψ pt) c') (mem_range.1 hy) (mem_range.1 hc)
    rw [e1 q] at h0
    rw [← h0]
    exact congrArg (fun f => Blocks.ext V f q) (funext fun b => (e1 (vtx V b)).symm)
  unfold formE
  rw [ldPart_ext_sum2 V Φ.h (2 ^ (Φ.hi + Φ.lo))
      (fun b y c => a.g (vtx V b) y * eqN (Φ.hi + Φ.lo) 0 (a.ψ (vtx V b)) c) WE q]
  exact sum_congr rfl fun y hy => sum_congr rfl fun c hc => by rw [key y hy c hc]

section Vtx
variable {X F E : Type} [Field F] [Field E] [Algebra F E] (Φ : IdxFmt F) (x : X)
  (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem ldPart_vtx0 (a : Atom0 E) (V b : ℕ) (hb : b < 2 ^ V) :
    a.ext Φ.h (Φ.hi + Φ.lo) V (fun y c => algebraMap F E (W y c)) A (vtx V b) =
      a.val Φ V W A b := by
  cases a with
  | cell f => exact ext_vtx E V _ b hb
  | idx a => rfl

theorem ldPart_vtxP (P : Poly0 X E) (b : ℕ) (hb : b < 2 ^ P.v) :
    P.ext Φ.h (Φ.hi + Φ.lo) x (fun y c => algebraMap F E (W y c)) A (vtx P.v b) =
      P.val Φ x W A b := by
  unfold Poly0.ext Poly0.val
  congr 1
  refine List.map_congr_left fun t _ => ?_
  unfold Term.ext Term.val
  rw [ext_vtx E P.v _ b hb]
  congr 2
  exact List.map_congr_left fun j _ => ldPart_vtx0 Φ W A (P.atom j) P.v b hb

theorem ldPart_vtxA (a : Atom X E) (v b : ℕ) (hw : a.WF Φ v) (hb : b < 2 ^ v) :
    a.ext Φ.h (Φ.hi + Φ.lo) v x (fun y c => algebraMap F E (W y c)) A (vtx v b) =
      a.val Φ v x W A b := by
  cases a with
  | base a => exact ldPart_vtx0 Φ W A a v b hb
  | sum w P =>
    have hv : P.v = v + w := hw.1
    show Blocks.ext v
        (fun b =>
          ∑ j ∈ range (2 ^ w), P.ext
            Φ.h (Φ.hi + Φ.lo) x (fun y c => algebraMap F E (W y c)) A (vtx (v + w) (b * 2 ^ w + j)))
        (vtx v b) =
      ∑ j ∈ range (2 ^ w), P.val Φ x W A (b * 2 ^ w + j)
    rw [ext_vtx E v _ b hb]
    refine sum_congr rfl fun j hj => ?_
    rw [← hv]
    refine ldPart_vtxP Φ x W A P _ ?_
    rw [hv, pow_add]
    have hj' := mem_range.1 hj
    calc b * 2 ^ w + j < b * 2 ^ w + 2 ^ w := Nat.add_lt_add_left hj' _
      _ = (b + 1) * 2 ^ w := by ring
      _ ≤ 2 ^ v * 2 ^ w := Nat.mul_le_mul_right _ hb

theorem ldPart_vtxF (f : Fam X E) (b : ℕ) (hw : f.WF Φ) (hb : b < 2 ^ f.v) :
    f.ext Φ.h (Φ.hi + Φ.lo) x (fun y c => algebraMap F E (W y c)) A (vtx f.v b) =
      f.val Φ x W A b := by
  unfold Fam.ext Fam.val
  congr 1
  refine List.map_congr_left fun t ht => ?_
  unfold Term.ext Term.val
  rw [ext_vtx E f.v _ b hb]
  congr 2
  exact List.map_congr_left fun j hj =>
    ldPart_vtxA Φ x W A (f.atom j) f.v b (hw.2 j (hw.1 t ht j hj)) hb

end Vtx

theorem ldPart_vtx : Spec.ldPart_vtx := fun _ _ _ _ _ _ Φ x W A =>
  ⟨ldPart_vtx0 Φ W A, ldPart_vtxP Φ x W A, ldPart_vtxA Φ x W A, ldPart_vtxF Φ x W A⟩

end Cb
