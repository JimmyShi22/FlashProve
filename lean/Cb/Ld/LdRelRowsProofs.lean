-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelRowsProofs.lean: the proofs of the statements of Cb/Ld/LdRelRows.lean (agreement whatever
the number of rows).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Lemmas: five renamings. Each states `LdCode.SameAs` (Cb/Ld/LdRelRows.lean) of two codes: one row
(`LdCode.same_unit`), rows of rows (`LdCode.same_curry`), rows of a pair (`LdCode.same_pair`), rows
of a complex (`LdCode.same_fam`), rows of a family with rows (`LdCode.same_ld`). Each holds by
unfolding the definitions. `ld_rows_self`, `ld_rows_il`, `ld_rows_pair`, `ld_rows_fam` and
`ld_rows_ld` each apply one of them through `ld_rows_same`.
Main names (statements and hypotheses: Cb/Ld/LdRelRows.lean): `ld_rows_same`: from `C.SameAs C' φ`
and `C.MCAat e bad` to `C'.MCAat e bad`; `ld_rows_mono`: a larger count.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelRows
import Cb.Ld.LdRelRepProofs
import Cb.Ld.LdRelProofsCode

set_option autoImplicit false

namespace Cb
open Prob

namespace LdCode
variable {E P : Type}

theorem same_unit (C : LdCode E P) : (C.il Unit).SameAs C fun α => ((), α) where
  onto := fun β => ⟨β.2, rfl⟩
  word := fun f' => ⟨fun p s => f' p s.2, fun _ _ => rfl⟩
  code := fun m' r' => ⟨fun j => m' j.2, fun q => r' q.2, fun _ _ => rfl⟩
  back := fun m r => ⟨fun j => m ((), j), fun q => r ((), q), fun _ _ => rfl⟩

theorem same_curry (C : LdCode E P) (R R₁ : Type) [Fintype R] [DecidableEq R]
    [Fintype R₁] [DecidableEq R₁] :
    (C.il (R × R₁)).SameAs ((C.il R₁).il R) fun α => ((α.1, α.2.1), α.2.2) where
  onto := fun β => ⟨(β.1.1, (β.1.2, β.2)), rfl⟩
  word := fun f' => ⟨fun p s => f' p (s.1.1, (s.1.2, s.2)), fun _ _ => rfl⟩
  code := fun m' r' =>
    ⟨fun j => m' (j.1.1, (j.1.2, j.2)), fun q => r' (q.1.1, (q.1.2, q.2)), fun _ _ => rfl⟩
  back := fun m r =>
    ⟨fun j => m ((j.1, j.2.1), j.2.2), fun q => r ((q.1, q.2.1), q.2.2), fun _ _ => rfl⟩

theorem same_pair (C₁ C₂ : LdCode E P) (R : Type) [Fintype R] [DecidableEq R] :
    ((C₁.il R).pair (C₂.il R)).SameAs ((C₁.pair C₂).il R) fun α => match α with
      | (i, .inl a) => .inl (i, a)
      | (i, .inr a) => .inr (i, a) where
  onto := fun β => match β with
    | .inl (i, a) => ⟨(i, .inl a), rfl⟩
    | .inr (i, a) => ⟨(i, .inr a), rfl⟩
  word := fun f' => ⟨fun p => match p with
      | .inl p => fun s => f' (.inl p) s
      | .inr p => fun s => f' (.inr p) s, fun _ α => match α with
      | (_, .inl _) => rfl
      | (_, .inr _) => rfl⟩
  code := fun m' r' => ⟨fun j => match j with
      | .inl (i, j) => m' (i, .inl j)
      | .inr (i, j) => m' (i, .inr j), fun q => match q with
      | .inl (i, q) => r' (i, .inl q)
      | .inr (i, q) => r' (i, .inr q), fun _ α => match α with
      | (_, .inl _) => rfl
      | (_, .inr _) => rfl⟩
  back := fun m r => ⟨fun j => match j with
      | (i, .inl j) => m (.inl (i, j))
      | (i, .inr j) => m (.inr (i, j)), fun q => match q with
      | (i, .inl q) => r (.inl (i, q))
      | (i, .inr q) => r (.inr (i, q)), fun _ α => match α with
      | (_, .inl _) => rfl
      | (_, .inr _) => rfl⟩

theorem same_fam {A : Type} [Fintype A] [DecidableEq A] (C : A → LdCode E P) (R : Type)
    [Fintype R] [DecidableEq R] :
    (LdCode.fam fun a => (C a).il R).SameAs ((LdCode.fam C).il R) fun α =>
      ⟨α.2.1, (α.1, α.2.2)⟩ where
  onto := fun β => ⟨(β.2.1, ⟨β.1, β.2.2⟩), rfl⟩
  word := fun f' => ⟨fun p s => f' p s, fun _ _ => rfl⟩
  code := fun m' r' =>
    ⟨fun j => m' (j.2.1, ⟨j.1, j.2.2⟩), fun q => r' (q.2.1, ⟨q.1, q.2.2⟩), fun _ _ => rfl⟩
  back := fun m r =>
    ⟨fun j => m ⟨j.2.1, (j.1, j.2.2)⟩, fun q => r ⟨q.2.1, (q.1, q.2.2)⟩, fun _ _ => rfl⟩

end LdCode

section
variable (E P : Type) [Field E] [Finite E] [Fintype P]

theorem ld_rows_same : Spec.ld_rows_same E P := by
  intro C C' φ e bad h hm f₀' f₁'
  obtain ⟨f₀, h₀⟩ := h.word f₀'
  obtain ⟨f₁, h₁⟩ := h.word f₁'
  refine (cnt_mono fun θ => ?_).trans (hm f₀ f₁)
  rintro ⟨S, hS, ⟨m', r', hc⟩, hn⟩
  refine ⟨S, hS, ?_, fun hb => hn ⟨?_, ?_⟩⟩
  · obtain ⟨m, r, hmr⟩ := h.code m' r'
    refine ⟨m, r, fun x hx => funext fun β => ?_⟩
    obtain ⟨α, rfl⟩ := h.onto β
    have e1 : C'.T f₀' x α + θ • C'.T f₁' x α = C'.T (C'.enc m' r') x α := congrFun (hc x hx) α
    show C.T f₀ x (φ α) + θ • C.T f₁ x (φ α) = C.T (C.enc m r) x (φ α)
    rw [← h₀, ← h₁, ← hmr]
    exact e1
  · obtain ⟨m, r, hb0⟩ := hb.1
    obtain ⟨m', r', hmr⟩ := h.back m r
    exact ⟨m', r', fun x hx => funext fun α => by rw [h₀, hmr]; exact congrFun (hb0 x hx) (φ α)⟩
  · obtain ⟨m, r, hb1⟩ := hb.2
    obtain ⟨m', r', hmr⟩ := h.back m r
    exact ⟨m', r', fun x hx => funext fun α => by rw [h₁, hmr]; exact congrFun (hb1 x hx) (φ α)⟩

theorem ld_rows_self : Spec.ld_rows_self E P := fun C e bad h =>
  ld_rows_same E P _ _ _ e bad (LdCode.same_unit C) (h Unit)

theorem ld_rows_il : Spec.ld_rows_il E P := fun C R₁ _ _ e bad h R _ _ =>
  ld_rows_same E P _ _ _ e bad (LdCode.same_curry C R R₁) (h (R × R₁))

theorem ld_rows_pair : Spec.ld_rows_pair E P := fun C₁ C₂ e b₁ b₂ h₁ h₂ R _ _ =>
  ld_rows_same E P _ _ _ e (b₁ + b₂) (LdCode.same_pair C₁ C₂ R)
    (ld_mca_pair E P (C₁.il R) (C₂.il R) e b₁ b₂ (h₁ R) (h₂ R))

theorem ld_rows_fam : Spec.ld_rows_fam E P := fun A _ _ C e b h R _ _ =>
  ld_rows_same E P _ _ _ e _ (LdCode.same_fam C R)
    (ld_mca_fam E P A (fun a => (C a).il R) e b fun a => h a R)

theorem ld_rows_mono : Spec.ld_rows_mono E P := fun C e bad bad' hb h R _ _ =>
  ld_mca_mono E P (C.il R) e bad bad' hb (h R)

end

/-- Rows of a family with rows. -/
theorem LdCode.same_ld {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {A : Type}
    [Fintype A] [DecidableEq A] {C : A → Code.Enc F} (T : Reading C) (R₀ : A → Type)
    [∀ a, Fintype (R₀ a)] [∀ a, DecidableEq (R₀ a)] (R : Type) [Fintype R] [DecidableEq R] :
    (T.ld E fun a => R × R₀ a).SameAs ((T.ld E R₀).il R) fun α =>
      ⟨α.2.1, ((α.1, α.2.2.1), α.2.2.2)⟩ where
  onto := fun β => ⟨(β.2.1.1, ⟨β.1, (β.2.1.2, β.2.2)⟩), rfl⟩
  word := fun f' => ⟨fun p s => f' p (s.1.1, (s.1.2, s.2)), fun _ _ => rfl⟩
  code := fun m' r' =>
    ⟨fun j => m' (j.2.1.1, ⟨j.1, (j.2.1.2, j.2.2)⟩),
      fun q => r' (q.2.1.1, ⟨q.1, (q.2.1.2, q.2.2)⟩),
      fun _ _ => rfl⟩
  back := fun m r =>
    ⟨fun j => m ⟨j.2.1, ((j.1, j.2.2.1), j.2.2.2)⟩,
      fun q => r ⟨q.2.1, ((q.1, q.2.2.1), q.2.2.2)⟩,
      fun _ _ => rfl⟩

theorem ld_rows_ld (F : Type) [Field F] (E : Type) [Field E] [Finite E] [Algebra F E] :
    Spec.ld_rows_ld F E := fun A _ _ C T e bad hp h R₀ _ _ R _ _ =>
  ld_rows_same E T.P _ _ _ e bad (LdCode.same_ld T R₀ R)
    (ldr_mca F E A C T (fun a => R × R₀ a) e bad hp (h fun a => R × R₀ a))

end Cb
