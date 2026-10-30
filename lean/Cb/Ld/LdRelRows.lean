-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelRows.lean: agreement "whatever the number of rows", for codes read under a
transformation: a notion that is kept by interleaving, pairs and complexes.

This file is about mutual correlated agreement of interleaved codes: it defines agreement that holds
for every number of interleaved rows, and states that this notion passes to interleavings, pairs and
families of codes.
Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdRelRowsProofs.lean. Generic: any finite field, any codes.

Why: the blocks ask mutual correlated agreement (Cb/Ld/LdRel.lean: `MCAat e bad`) of interleavings
of the codes that are in their records: a fold asks it of `C.il R` for cubes R of all sizes, where C
may itself be an interleaving, a pair or a complex. Below a third of the distance (3 e < d)
agreement follows from laws and distance, for every code (`ld_mca_third`, Cb/Ld/LdBaseCode.lean).
Beyond, for families of Reed-Solomon codes whose message and randomness fill the dimension, with
rows, under an even reading (Cb/Ld/LdRelRep.lean: `T.ld E R`), it is proved within half the distance
(`rsHalf_group`, Cb/Gl/GlAgreeHalf.lean), and from there to the Johnson radius it stands, at the
radii e with `T.mult a ≤ e` for all a (`rs_group_prox`, Cb/Gen/CodeRepRS.lean), under the named
hypothesis `BCHKS46` (Cb/Gen/CodeListRS.lean), which this file does not prove; in both for
distinct points and 0 < k a < n a (dimension k a + 1, length n a), with a count that does not depend
on the rows. But (T.ld E R).il R' is not of the form T.ld E R'' as a record (its symbols are named
R' × (Σ a, R a × ..), not Σ a, (R' × R a) × ..). Here: the notion does not see such names.

Main names:
  `C.MCArows e bad`: (C.il R).MCAat e bad for every finite set R of rows.
  `Spec.ld_rows_same`: C.SameAs C' φ, C.MCAat e bad ⇒ C'.MCAat e bad.
  `Spec.ld_rows_self`: C.MCArows e bad ⇒ C.MCAat e bad (one row).
  `Spec.ld_rows_il`: C.MCArows e bad ⇒ (C.il R).MCArows e bad (rows of rows are rows).
  `Spec.ld_rows_pair`: C₁.MCArows e b₁, C₂.MCArows e b₂ ⇒ (C₁.pair C₂).MCArows e (b₁ + b₂) (rows of
    a pair are a pair of rows; the counts add: `ld_mca_pair`).
  `Spec.ld_rows_fam`: (C a).MCArows e (b a) for all a ⇒ (LdCode.fam C).MCArows e (∑ a, b a).
  `Spec.ld_rows_ld`: a family of codes of Code/Iface.lean under a reading T, message and randomness
    filling the dimension: if T.MCAat E R e bad for every family R of rows, then
    (T.ld E R).MCArows e bad.

Limits: this file does not say that any code has `MCArows` beyond a third. That is an instance's
matter. This file says nothing on lists: they follow from laws and distance below the Johnson
radius, for every code (Cb/Ld/LdRelJohnson.lean). It says nothing on re-reading at other positions.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelRep
import Cb.Ld.LdRelAny

set_option autoImplicit false

namespace Cb
open Prob

namespace LdCode
variable {E P : Type} [Field E]

/-- Every long word of C' is one of C, and the two have the same codewords, up to a renaming φ
(onto) of the coordinates of a long symbol. -/
structure SameAs (C C' : LdCode E P) (φ : C'.Aa → C.Aa) : Prop where
  onto : Function.Surjective φ
  word : ∀ f' : C'.Word, ∃ f : C.Word, ∀ x α, C'.T f' x α = C.T f x (φ α)
  code : ∀ m' r', ∃ m r, ∀ x α, C'.T (C'.enc m' r') x α = C.T (C.enc m r) x (φ α)
  back : ∀ m r, ∃ m' r', ∀ x α, C'.T (C'.enc m' r') x α = C.T (C.enc m r) x (φ α)

/-- Agreement whatever the number of rows. -/
def MCArows [Finite E] [Fintype P] (C : LdCode E P) (e bad : ℕ) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R], (C.il R).MCAat e bad

end LdCode

namespace Spec
section
variable (E P : Type) [Field E] [Finite E] [Fintype P]

def ld_rows_same : Prop :=
  ∀ (C C' : LdCode E P) (φ : C'.Aa → C.Aa) (e bad : ℕ),
    C.SameAs C' φ → C.MCAat e bad → C'.MCAat e bad

def ld_rows_self : Prop := ∀ (C : LdCode E P) (e bad : ℕ), C.MCArows e bad → C.MCAat e bad

def ld_rows_il : Prop :=
  ∀ (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R] (e bad : ℕ),
    C.MCArows e bad → (C.il R).MCArows e bad

def ld_rows_pair : Prop :=
  ∀ (C₁ C₂ : LdCode E P) (e b₁ b₂ : ℕ),
    C₁.MCArows e b₁ → C₂.MCArows e b₂ → (C₁.pair C₂).MCArows e (b₁ + b₂)

def ld_rows_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → LdCode E P) (e : ℕ) (b : A → ℕ),
    (∀ a, (C a).MCArows e (b a)) → (LdCode.fam C).MCArows e (∑ a, b a)

def ld_rows_mono : Prop :=
  ∀ (C : LdCode E P) (e bad bad' : ℕ), bad ≤ bad' → C.MCArows e bad → C.MCArows e bad'

end

/-- Families of codes with rows, under a reading. -/
def ld_rows_ld (F : Type) [Field F] (E : Type) [Field E] [Finite E] [Algebra F E] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (e bad : ℕ),
    (∀ a, (C a).msg + (C a).r = (C a).k) →
    (∀ (R : A → Type) [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)], T.MCAat E R e bad) →
    ∀ (R : A → Type) [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)], (T.ld E R).MCArows e bad

end Spec
end Cb
