-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPkRes.lean: packed cells under restriction to a part of a matrix of packed entries
(some packed rows, some columns).

Plain mathematics on `pack`, `PackBy`, `Packed`, `cells` of Cb/Ld/LdRngAlg.lean. Definitions,
statements (in `Cb.Spec`) and proofs. No protocol. In standard terms: book-keeping for the range
check. Several integers (cells) are packed into one element of a commutative ring E with powers of a
radix ϱ; these lemmas say when unpacking a part of a matrix of such elements agrees with unpacking
the whole. `PackBy b ϱ Y mpk`: all cells of Y have absolute value below b, and mpk is the packing of
Y; `cells P b ϱ mpk`: the Y with `PackBy b ϱ Y mpk` (a choice), the matrix 0 if there is none. Many
statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: a request that is built from a partition holds a segment's packed rows in several messages,
hands some of them on after a closing, and reads them again later, then among other rows. Each
block's range check and each later reading speak of the matrix of packed entries that it sees. That
all of them mean the same integers is what these lemmas give, under their hypotheses.

Main names ("below b" is in absolute value):
  `resY ι κ Y`, `resM ι κ mpk`: the part of a matrix of cells, and of a matrix of packed entries,
    along maps ι of packed rows and κ of columns (any maps: injectivity is not needed); a packed
    row goes with all its lanes.
  `Spec.ldPartRes_cells`: under unique packing (`Uniq b ϱ P p`, characteristic p): if the whole is
    a packing of cells below b, the cells of the part are the cells of the whole, restricted.
  `Spec.ldPartRes_cover`: for parts that cover all pairs (packed row, column): `PackBy` of the
    whole ⇔ `PackBy` of every part. No condition on ϱ, P, p.
  `Spec.ldPartRes_entry`: "is a packing of cells below b" is a property of the single entries:
    `Packed P b ϱ mpk` ⇔ every entry is Σ_l ϱ^l y_l for some integers y_l below b. No condition on
    ϱ, P, p.
  `Spec.ldPartRes_same`: under unique packing (`Uniq b ϱ P p`, characteristic p): two matrices of
    packed entries, both packings of cells below b, that have the same entry at (i, c) and (i', c')
    have the same cells there, lane by lane.

Limits: this file says nothing on reads (`ReadBy`), on messages or places. A part takes whole packed
rows: single lanes cannot be cut out.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRngAlgProofs

set_option autoImplicit false

namespace Cb
open Prob Finset Cb.Rng Cb.RngPk

/-- the part of a matrix of cells, and of a matrix of packed entries -/
def resY {Rp Rp' C C' : Type} {P : ℕ} (ι : Rp' → Rp) (κ : C' → C) (Y : Rp × Fin P → C → ℤ) :
    Rp' × Fin P → C' → ℤ :=
  fun r c => Y (ι r.1, r.2) (κ c)
def resM {E Rp Rp' C C' : Type} (ι : Rp' → Rp) (κ : C' → C) (mpk : Rp → C → E) : Rp' → C' → E :=
  fun i c => mpk (ι i) (κ c)

namespace Spec

def ldPartRes_by : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rp' C C' : Type) [Fintype Rp] [Fintype Rp'] (P : ℕ) (b ϱ : ℤ)
      (ι : Rp' → Rp) (κ : C' → C) (Y : Rp × Fin P → C → ℤ) (mpk : Rp → C → E),
    PackBy b ϱ Y mpk → PackBy b ϱ (resY ι κ Y) (resM ι κ mpk)

def ldPartRes_cells : Prop :=
  ∀ (E : Type) [CommRing E] (p : ℕ) [CharP E p] (Rp Rp' C C' : Type) [Fintype Rp] [Fintype Rp']
      (P : ℕ) (b ϱ : ℤ) (ι : Rp' → Rp) (κ : C' → C) (mpk : Rp → C → E),
    Uniq b ϱ P p → Packed P b ϱ mpk → cells P b ϱ (resM ι κ mpk) = resY ι κ (cells P b ϱ mpk)

def ldPartRes_cover : Prop :=
  ∀ (E : Type) [CommRing E] (Rp C T : Type) [Fintype Rp] (Rq Cq : T → Type)
      [∀ t, Fintype (Rq t)] (P : ℕ) (b ϱ : ℤ) (ι : ∀ t, Rq t → Rp) (κ : ∀ t, Cq t → C)
      (Y : Rp × Fin P → C → ℤ) (mpk : Rp → C → E),
    (∀ i c, ∃ t i' c', ι t i' = i ∧ κ t c' = c) →
    (PackBy b ϱ Y mpk ↔ ∀ t, PackBy b ϱ (resY (ι t) (κ t) Y) (resM (ι t) (κ t) mpk))

def ldPartRes_entry : Prop :=
  ∀ (E : Type) [CommRing E] (Rp C : Type) [Fintype Rp] (P : ℕ) (b ϱ : ℤ) (mpk : Rp → C → E),
    Packed P b ϱ mpk ↔
    ∀ i c,
      ∃ y : Fin P → ℤ, (∀ l, |y l| < b) ∧ mpk i c = ∑ l : Fin P, (ϱ : E) ^ (l : ℕ) * ((y l : ℤ) : E)

def ldPartRes_packed : Prop :=
  ∀ (E : Type) [CommRing E] (Rp C T : Type) [Fintype Rp] (Rq Cq : T → Type) [∀ t, Fintype (Rq t)]
      (P : ℕ) (b ϱ : ℤ) (ι : ∀ t, Rq t → Rp) (κ : ∀ t, Cq t → C) (mpk : Rp → C → E),
    (∀ i c, ∃ t i' c', ι t i' = i ∧ κ t c' = c) →
    (Packed P b ϱ mpk ↔ ∀ t, Packed P b ϱ (resM (ι t) (κ t) mpk))

def ldPartRes_same : Prop :=
  ∀ (E : Type) [CommRing E] (p : ℕ) [CharP E p] (Rp Rp' C C' : Type) [Fintype Rp] [Fintype Rp']
      (P : ℕ) (b ϱ : ℤ) (mpk : Rp → C → E) (mpk' : Rp' → C' → E),
    Uniq b ϱ P p → Packed P b ϱ mpk → Packed P b ϱ mpk' →
    ∀ i c i' c', mpk i c = mpk' i' c' → ∀ l, cells P b ϱ mpk (i, l) c = cells P b ϱ mpk' (i', l) c'

end Spec

theorem ldPartRes_by : Spec.ldPartRes_by := fun _ _ _ _ _ _ _ _ _ _ _ ι κ _ _ h =>
  ⟨fun r c => h.1 (ι r.1, r.2) (κ c), fun i c => h.2 (ι i) (κ c)⟩

/-- The virtual matrix of cells (`cells`) of a packing (`Packed`) is packed by it (`PackBy`). -/
theorem ldPartRes_spec {E Rp C : Type} [CommRing E] [Fintype Rp] (P : ℕ) (b ϱ : ℤ)
    (mpk : Rp → C → E) (h : Packed P b ϱ mpk) :
    PackBy b ϱ (cells P b ϱ mpk) mpk := by
  unfold cells
  rw [dif_pos h]
  exact h.choose_spec

theorem ldPartRes_cells : Spec.ldPartRes_cells := fun E _ p _ Rp Rp' C C' _ _ P b ϱ ι κ mpk hU h =>
  rngPk_cells E p Rp' C' P b b ϱ _ _ hU (le_refl b)
    (ldPartRes_by E Rp Rp' C C' P b ϱ ι κ _ mpk (ldPartRes_spec P b ϱ mpk h))

theorem ldPartRes_cover : Spec.ldPartRes_cover := by
  intro E _ Rp C T _ Rq Cq _ P b ϱ ι κ Y mpk hc
  refine ⟨fun h t => ldPartRes_by E Rp (Rq t) C (Cq t) P b ϱ (ι t) (κ t) Y mpk h,
    fun h => ⟨fun r c => ?_, fun i c => ?_⟩⟩
  · obtain ⟨i, l⟩ := r
    obtain ⟨t, i', c', rfl, rfl⟩ := hc i c
    exact (h t).1 (i', l) c'
  · obtain ⟨t, i', c', rfl, rfl⟩ := hc i c
    exact (h t).2 i' c'

theorem ldPartRes_entry : Spec.ldPartRes_entry := by
  intro E _ Rp C _ P b ϱ mpk
  constructor
  · rintro ⟨Y, h1, h2⟩ i c
    exact ⟨fun l => Y (i, l) c, fun l => h1 (i, l) c, h2 i c⟩
  · intro h
    choose y h1 h2 using h
    exact ⟨fun r c => y r.1 c r.2, fun r c => h1 r.1 c r.2, fun i c => h2 i c⟩

theorem ldPartRes_packed : Spec.ldPartRes_packed := by
  intro E _ Rp C T _ Rq Cq _ P b ϱ ι κ mpk hc
  refine ⟨fun ⟨Y, h⟩ t => ⟨_, ldPartRes_by E Rp (Rq t) C (Cq t) P b ϱ (ι t) (κ t) Y mpk h⟩,
    fun h => ?_⟩
  rw [ldPartRes_entry]
  intro i c
  obtain ⟨t, i', c', rfl, rfl⟩ := hc i c
  exact (ldPartRes_entry E (Rq t) (Cq t) P b ϱ _).1 (h t) i' c'

theorem ldPartRes_same : Spec.ldPartRes_same := by
  intro E _ p _ Rp Rp' C C' _ _ P b ϱ mpk mpk' hU h h' i c i' c' he l
  have s := ldPartRes_spec P b ϱ mpk h
  have s' := ldPartRes_spec P b ϱ mpk' h'
  have e := rngPk_unique E p Unit P b ϱ (fun r => cells P b ϱ mpk (i, r.2) c)
    (fun r => cells P b ϱ mpk' (i', r.2) c') hU (fun r => s.1 _ _) (fun r => s'.1 _ _)
    (fun _ => (s.2 i c).symm.trans (he.trans (s'.2 i' c')))
  exact congrFun e ((), l)

end Cb
