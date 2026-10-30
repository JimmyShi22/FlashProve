-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeEraseLd.lean: erasure correction for a code read under a transformation (`Cb.LdCode` of
Cb/Ld/LdRel.lean).

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Gen/CodeEraseLdProofs.lean.

An `LdCode` has an encoder into native words and a transformation `T` of native words into long
words. Cb/Gen/CodeErase.lean has erasure correction for generator matrices and for readings of codes
of Code/Iface.lean. Here is the same at the level at which the proximity blocks beyond unique
decoding are written: C is any `LdCode`, a long word g is given, and a set S of long positions.

Main names:
  `C.AgreesOn S g w`: on S the long word g is the transform of the encoding of w = (message,
    randomness). `C.OnCode g S` says that there is such a w (`Spec.lde_onCode_iff`).
  `C.erase? d S g`: a w with `C.AgreesOn S g w` (the only one under `C.Laws` and `C.Dist d`:
    `Spec.lde_unique`), if S is large, that is, has more than (number of long positions) - d
    elements, and there is one; "none" else.
  `C.Exc e f₀ f₁ θ`, `C.ExcFold e f₀ f₁ θ`: θ is exceptional at the radius e for the line
    T f₀ + θ T f₁, or (1 - θ) T f₀ + θ T f₁ (`C.MCAat` bounds the number of the first kind:
    `Spec.lde_mcaAt_iff_exc`).
Stated, for a code with `C.Laws` and `C.Dist d` (nothing else is asked of the code; but
`Spec.lde_mcaAt_fold` asks `C.Laws` and `C.MCAat e bad`, no distance):
  `Spec.lde_erase_line` (linearity on a common set); `Spec.lde_mcaAt_fold` (the count of `C.MCAat`
    holds for the second form of the line).
  `Spec.lde_erase_ends`, `Spec.lde_erase_ends_fold` (e < d, S omits at most e positions, θ not
    exceptional, the point of the line on the code on S: erase? succeeds at both ends and at the
    point, and commutes with the line).
  `Spec.lde_erase_il`; `Spec.lde_erase_pair` (two codes side by side, both with the laws and the
    distance d: side by side); both on a large S.

Limits: this file says nothing on running time. `C.Dist d` with `C.Laws` makes the transform of an
encoding determine (message, randomness), if d > 0; a transformation that forgets a part of the
codeword, in such a way that some non-zero (message, randomness) has the transform 0, has no d > 0
here. This file says nothing on protocols. This file says nothing on the value of any number.

Terms: lean/GLOSSARY.md: block (the sense of `Cb/Ld/`), laws (of a code), list, long position,
native position.
-/
import Cb.Ld.LdRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob

namespace LdCode
variable {E P : Type} [Field E] (C : LdCode E P)

/-- message and randomness -/
abbrev MR : Type := (C.J → E) × (C.Q → E)

/-- On S the long word g is the transform of the encoding of w. -/
def AgreesOn (S : Finset P) (g : P → C.Aa → E) (w : C.MR) : Prop :=
  ∀ x ∈ S, g x = C.T (C.enc w.1 w.2) x

variable [Fintype P]

open Classical in
/-- Erasure correction under the transformation. Where a statement needs the distance, it assumes
`C.Dist d`: C has distance at least d under the transformation. -/
def erase? (d : ℕ) (S : Finset P) (g : P → C.Aa → E) : Option C.MR :=
  if h : Fintype.card P < S.card + d ∧ ∃ w, C.AgreesOn S g w then some h.2.choose else none

/-- The same, with 0 where there is no result. -/
def eraseD (d : ℕ) (S : Finset P) (g : P → C.Aa → E) : C.MR := (C.erase? d S g).getD 0

open Classical in
/-- All long positions at which g is the transform of the encoding of w. -/
def agr (g : P → C.Aa → E) (w : C.MR) : Finset P :=
  Finset.univ.filter fun x => g x = C.T (C.enc w.1 w.2) x

/-- θ is exceptional for the line T f₀ + θ T f₁ at the radius e. -/
def Exc (e : ℕ) (f₀ f₁ : C.Word) (θ : E) : Prop :=
  ∃ S : Finset P,
    Fintype.card P ≤ S.card + e ∧
    C.OnCode (C.T f₀ + θ • C.T f₁) S ∧
    ¬ (C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S)

/-- θ is exceptional for the line (1 - θ) T f₀ + θ T f₁ at the radius e. -/
def ExcFold (e : ℕ) (f₀ f₁ : C.Word) (θ : E) : Prop :=
  ∃ S : Finset P,
    Fintype.card P ≤ S.card + e ∧
    C.OnCode ((1 - θ) • C.T f₀ + θ • C.T f₁) S ∧
    ¬ (C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S)

end LdCode

namespace Spec
variable (E : Type) [Field E] (P : Type) [Fintype P]

def lde_onCode_iff : Prop :=
  ∀ (C : LdCode E P) (g : P → C.Aa → E) (S : Finset P), C.OnCode g S ↔ ∃ w, C.AgreesOn S g w

def lde_unique : Prop :=
  ∀ (C : LdCode E P) (d : ℕ), C.Laws → C.Dist d → ∀ S : Finset P, Fintype.card P < S.card + d →
    ∀ (g : P → C.Aa → E) (w w' : C.MR), C.AgreesOn S g w → C.AgreesOn S g w' → w = w'

/-- What erasure correction returns. -/
def lde_erase_iff : Prop :=
  ∀ (C : LdCode E P) (d : ℕ), C.Laws → C.Dist d → ∀ (S : Finset P) (g : P → C.Aa → E) (w : C.MR),
    C.erase? d S g = some w ↔ Fintype.card P < S.card + d ∧ C.AgreesOn S g w

def lde_erase_none_iff : Prop :=
  ∀ (C : LdCode E P) (d : ℕ) (S : Finset P) (g : P → C.Aa → E),
    C.erase? d S g = none ↔ ¬ (Fintype.card P < S.card + d ∧ C.OnCode g S)

def lde_eraseD : Prop :=
  ∀ (C : LdCode E P) (d : ℕ) (S : Finset P) (g : P → C.Aa → E) (w : C.MR),
    C.erase? d S g = some w → C.eraseD d S g = w

def lde_near_iff_agr : Prop :=
  ∀ (C : LdCode E P) (e : ℕ) (f : C.Word) (w : C.MR),
    C.Near e f (C.enc w.1 w.2) ↔ Fintype.card P ≤ (C.agr (C.T f) w).card + e

/-- Under `C.Laws` and `C.Dist d`, every member of a list at a radius e < d is erasure correction on
its own agreement set. -/
def lde_erase_agr : Prop :=
  ∀ (C : LdCode E P) (d e : ℕ), C.Laws → C.Dist d → e < d → ∀ (f : C.Word) (w : C.MR),
    C.Near e f (C.enc w.1 w.2) → C.erase? d (C.agr (C.T f) w) (C.T f) = some w

/-- Under `C.Laws` and `C.Dist d`, what erasure correction returns on a set that omits at most e
long positions is a member of the list at e. -/
def lde_erase_near : Prop :=
  ∀ (C : LdCode E P) (d e : ℕ), C.Laws → C.Dist d → ∀ (S : Finset P) (f : C.Word) (w : C.MR),
    C.erase? d S (C.T f) = some w → Fintype.card P ≤ S.card + e → C.Near e f (C.enc w.1 w.2)

def lde_erase_anti : Prop :=
  ∀ (C : LdCode E P) (d : ℕ), C.Laws → C.Dist d → ∀ (S S' : Finset P) (g : P → C.Aa → E) (w : C.MR),
    S ⊆ S' → Fintype.card P < S.card + d → C.erase? d S' g = some w → C.erase? d S g = some w

def lde_erase_line : Prop :=
  ∀ (C : LdCode E P) (d : ℕ), C.Laws → C.Dist d →
    ∀ (S : Finset P) (g₀ g₁ : P → C.Aa → E) (w₀ w₁ : C.MR) (c₀ c₁ : E), C.erase? d S g₀ = some w₀ →
      C.erase? d S g₁ = some w₁ → C.erase? d S (c₀ • g₀ + c₁ • g₁) = some (c₀ • w₀ + c₁ • w₁)

def lde_mcaAt_iff_exc [Finite E] : Prop :=
  ∀ (C : LdCode E P) (e bad : ℕ), C.MCAat e bad ↔ ∀ f₀ f₁ : C.Word, cnt (C.Exc e f₀ f₁) ≤ bad

def lde_mcaAt_fold [Finite E] : Prop :=
  ∀ (C : LdCode E P) (e bad : ℕ),
    C.Laws → C.MCAat e bad → ∀ f₀ f₁ : C.Word, cnt (C.ExcFold e f₀ f₁) ≤ bad

/-- The two ends of a line. -/
def lde_erase_ends : Prop :=
  ∀ (C : LdCode E P) (d e : ℕ), C.Laws → C.Dist d → e < d →
    ∀ S : Finset P, Fintype.card P ≤ S.card + e →
      ∀ (f₀ f₁ : C.Word) (θ : E), ¬ C.Exc e f₀ f₁ θ → C.OnCode (C.T f₀ + θ • C.T f₁) S →
        ∃ w₀ w₁,
          C.erase? d S (C.T f₀) = some w₀ ∧
          C.erase? d S (C.T f₁) = some w₁ ∧
          C.erase? d S (C.T f₀ + θ • C.T f₁) = some (w₀ + θ • w₁)

def lde_erase_ends_fold : Prop :=
  ∀ (C : LdCode E P) (d e : ℕ), C.Laws → C.Dist d → e < d →
    ∀ S : Finset P, Fintype.card P ≤ S.card + e →
      ∀ (f₀ f₁ : C.Word) (θ : E), ¬ C.ExcFold e f₀ f₁ θ →
        C.OnCode ((1 - θ) • C.T f₀ + θ • C.T f₁) S →
        ∃ w₀ w₁,
          C.erase? d S (C.T f₀) = some w₀ ∧
          C.erase? d S (C.T f₁) = some w₁ ∧
          C.erase? d S ((1 - θ) • C.T f₀ + θ • C.T f₁) = some ((1 - θ) • w₀ + θ • w₁)

/-- Interleaving: row by row. -/
def lde_erase_il : Prop :=
  ∀ (C : LdCode E P) (d : ℕ), C.Laws → C.Dist d →
    ∀ (R : Type) [Fintype R] [DecidableEq R] (S : Finset P), Fintype.card P < S.card + d →
      ∀ (g : P → (C.il R).Aa → E) (w : (C.il R).MR),
        (C.il R).erase? d S g = some w ↔
        ∀ i, C.erase? d S (fun x α => g x (i, α)) = some (fun j => w.1 (i, j), fun q => w.2 (i, q))

/-- Two codes side by side. -/
def lde_erase_pair : Prop :=
  ∀ (C₁ C₂ : LdCode E P) (d : ℕ), C₁.Laws → C₁.Dist d → C₂.Laws → C₂.Dist d →
    ∀ S : Finset P, Fintype.card P < S.card + d →
      ∀ (g : P → (C₁.pair C₂).Aa → E) (w : (C₁.pair C₂).MR),
        (C₁.pair C₂).erase? d S g = some w ↔
        C₁.erase? d S (fun x α => g x (.inl α)) =
          some (fun j => w.1 (.inl j), fun q => w.2 (.inl q)) ∧
        C₂.erase? d S (fun x α => g x (.inr α)) =
          some (fun j => w.1 (.inr j), fun q => w.2 (.inr q))

end Spec
end Cb
