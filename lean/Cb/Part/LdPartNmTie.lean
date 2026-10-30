-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartNmTie.lean: the clauses on namings of the ties between stages, for the namings of a
partition's bodies and kept messages (`P.nmS`, Cb/Part/LdPartNmOf.lean).

Definitions (with two lemmas on `rpS` that they need) and statements (the statements in `Cb.Spec`);
the proofs are in Cb/Part/LdPartNmTieProofs.lean. Plain mathematics on namings; no message, no
protocol. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
In standard terms: book-keeping for how a request's cells are laid out from one part of the
protocol to the next. The ties at a closing (`LdPartTie`, Cb/Part/LdPartNext.lean) are eight clauses
between the reading of the kept messages before, the reading of the open messages after, and the
overwriting of the further witness. The clauses on namings of the title are `PartOf`, `OwnAt`
(Cb/Part/LdPartTieNm.lean) and the fields part, own, cover, named of `LdPartTieL.OK`
(Cb/Part/LdPartTieOf.lean), part, named of `LdPartKeepL.OK` (Cb/Part/LdPartKeepOf.lean), own, cover
of `LdPartTie0L.OK` (Cb/Part/LdPartTie0Of.lean). The statements say, each under its hypotheses, that
the namings meet them.

Why: the ties at a closing are proved for arbitrary parameters (two namings, maps of packed rows and
columns) under conditions. Their clauses on namings had a toy value only (Cb/Part/LdPartTieOf.lean,
Limits).

Main names:
  `Spec.ldPartNmTie_part`: on₀ ⊆ on₁ ⊆ the segments, 0 < K.P, K.Cw ≠ 0 ⇒ (nmS on₀).PartOf (nmS on₁)
    (incS ..) id.
  `Spec.ldPartNmTie_own`: on j, j < P.n, cols j ≤ K.Cw, 0 < K.P, K.Cw ≠ 0, on ⊆ the segments ⇒ (nmS
    on).OwnAt K.P j (2^rowsLog j) (cols j) (ownS ..) id.
  `Spec.ldPartNmTie_cover`: on₀ ⊆ on₁, on₁ j, j < P.n, every segment of on₁ is j or in on₀ ⇒ the two
    rectangles cover all pairs (packed row, column) of the larger matrix.
  `Spec.ldPartNmTie_alone`: on j, j < P.n, every segment of on is j ⇒ the own rectangle alone covers
    (the first body).
  `Spec.ldPartNmTie_sets`: `P.Props p`: what is kept after k is in body k (onKept k ⊆ onBody k);
    body k + 1 holds nothing but segment k + 1's matrix and what is kept after k (that it does hold
    what is kept after k is `onBody`'s definition: Cb/Part/LdPartNmOf.lean: no conjunct here); body
    0 holds segment 0's matrix alone; body k holds segment k's matrix.
  `Spec.ldPartNmTie_named`: `P.Props p`: every row of `P.kept k` is named by the naming of the kept
    messages after k, its matrix with the segment's number of columns.

Limits: this file says nothing on the clauses on entries of the ties: the closing's places.
These clauses say that a kept message's entry is the entry behind the
closing, and what is overwritten. It says nothing on numbers (unique packing). This file gives no
instance of `LdPartD`, so as far as this file shows its theorems may hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartNmOf
import Cb.Part.LdPartTieNm

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

namespace LdPartD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

omit [Fintype F] in
theorem rpS_mono {on₀ on₁ : ℕ → Bool} (h : ∀ s, on₀ s = true → on₁ s = true) (s : ℕ) :
    P.rpS K on₀ s ≤ P.rpS K on₁ s := by
  unfold rpS
  by_cases h0 : on₀ s = true
  · rw [if_pos h0, if_pos (h s h0)]
  · rw [if_neg h0]
    exact Nat.zero_le _

/-- a packed row of the smaller matrix, in the larger -/
def incS {on₀ on₁ : ℕ → Bool} (h : ∀ s, on₀ s = true → on₁ s = true) :
    (Σ s : Fin P.n, Fin (P.rpS K on₀ s)) → Σ s : Fin P.n, Fin (P.rpS K on₁ s) :=
  fun x => ⟨x.1, Fin.castLE (P.rpS_mono K h x.1) x.2⟩

omit [Fintype F] in
theorem rpS_on {on : ℕ → Bool} {j : ℕ} (hon : on j = true) : P.rp K j = P.rpS K on j := by
  unfold rpS
  rw [if_pos hon]

/-- the packed rows of segment j's matrix -/
def ownS (on : ℕ → Bool) (j : ℕ) (hj : j < P.n) (hon : on j = true) :
    Fin (P.rp K j) → Σ s : Fin P.n, Fin (P.rpS K on s) :=
  fun i => ⟨⟨j, hj⟩, Fin.cast (P.rpS_on K hon) i⟩

end LdPartD

namespace Spec

def ldPartNmTie_part : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) [NeZero K.Cw] (on₀ on₁ : ℕ → Bool) (Rd₀ U₀ Rd₁ U₁ : Type) [Fintype Rd₀]
      [Fintype U₀] [DecidableEq U₀] [Fintype Rd₁] [Fintype U₁] [DecidableEq U₁]
      (wd₀ nd₀ wd₁ nd₁ : ℕ) (d₀ : (P.parS K on₀ Rd₀ U₀ wd₀ nd₀).one.Row)
      (d₁ : (P.parS K on₁ Rd₁ U₁ wd₁ nd₁).one.Row) (h : ∀ s, on₀ s = true → on₁ s = true),
    0 < K.P → (∀ s, on₁ s = true → s < P.n) →
    (P.nmS K on₀ Rd₀ U₀ wd₀ nd₀ d₀).PartOf (P.nmS K on₁ Rd₁ U₁ wd₁ nd₁ d₁) (P.incS K h) id

def ldPartNmTie_own : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) [NeZero K.Cw] (on : ℕ → Bool) (Rd U : Type) [Fintype Rd] [Fintype U]
      [DecidableEq U] (wd nd : ℕ) (d0 : (P.parS K on Rd U wd nd).one.Row) (j : ℕ)
      (hj : j < P.n) (hon : on j = true),
    0 < K.P → (∀ s, on s = true → s < P.n) → (P.seg j).cols ≤ K.Cw →
    (P.nmS K on Rd U wd nd d0).OwnAt
      K.P j (2 ^ (P.seg j).rowsLog) (P.seg j).cols (P.ownS K on j hj hon) id

def ldPartNmTie_cover : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (on₀ on₁ : ℕ → Bool) (h : ∀ s, on₀ s = true → on₁ s = true) (j : ℕ)
      (hj : j < P.n) (hon : on₁ j = true),
    (∀ s, on₁ s = true → s = j ∨ on₀ s = true) →
    ∀ (i : Σ s : Fin P.n, Fin (P.rpS K on₁ s)) (c : Fin K.Cw),
      (∃ i' c', P.incS K h i' = i ∧ (id c' : Fin K.Cw) = c) ∨
      ∃ i' c', P.ownS K on₁ j hj hon i' = i ∧ (id c' : Fin K.Cw) = c

def ldPartNmTie_alone : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (on : ℕ → Bool) (j : ℕ) (hj : j < P.n) (hon : on j = true),
    (∀ s, on s = true → s = j) →
    ∀ (i : Σ s : Fin P.n, Fin (P.rpS K on s)) (c : Fin K.Cw),
      ∃ i' c', P.ownS K on j hj hon i' = i ∧ (id c' : Fin K.Cw) = c

def ldPartNmTie_sets : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (p : ℕ),
    P.Props p →
    (∀ k s, P.onKept k s = true → P.onBody k s = true) ∧
    (∀ k s, P.onBody (k + 1) s = true → s = k + 1 ∨ P.onKept k s = true) ∧
    (∀ s, P.onBody 0 s = true → s = 0) ∧
    ∀ k, P.onBody k k = true

def ldPartNmTie_named : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (p k : ℕ),
    P.Props p →
    ∀ q ∈ P.kept k, q.2 < P.rowsS (P.onKept k) q.1 ∧ P.colsS (P.onKept k) q.1 = (P.seg q.1).cols

end Spec
end Cb
