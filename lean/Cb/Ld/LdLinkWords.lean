-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinkWords.lean: counting lemmas for the soundness analysis of the interactive oracle
reduction of Cb/Ld/LdLink.lean (the link between two encoded indices, beyond unique decoding) for
the claim that two tables of words decode to messages that agree on fixed coordinates. They say, for
each of the reduction's three verifier messages that are not seeds, which of its values are bad and
at most how many there are; for γ and φ, what follows if the value drawn is not bad.

Definitions and statements; the proofs are in Cb/Ld/LdLinkWordsProofs.lean. On vectors and tables
only. It builds on Cb/Ld/LdFoldEq.lean.
The format `LdIx` (Cb/Ld/LdFoldEq.lean) has a generator matrix G, a sample map Z and a radius of
decoding. An encoded index is a table f of words, one for each row r in {0,1}^v; an honest one has
the codewords `G.mulVec` of full messages. A record (`LdIx.Rec`) is a seed of Z with the answers of
every row. The fold at γ (`foldAll`, Cb/Gen/FoldWords.lean) is the sum over the rows r of eq(γ, r)
times the row. A point γ is bad for the fold of a table (`LdIx.Bad`, Cb/Ld/LdFoldEq.lean) if some
codeword is near the folded word (within e' positions, e' the radius at which the fold is tested)
and has the record's folded answers, while the table does not decode or the codeword's message part
is not the fold of what the table decodes to.

The setting (`LdLkW`: the data). Both encoded indices have the format X, so one decoder serves both.
f₀ with the record rec₀ is the first one, f₁ with rec₁ the further one. `lay` names the places of
the layout in a message part: where the index proper is. In the use in view (no law of `LdLkW`) pads
lie off the layout; those of the two encoded indices are independent, and the link leaves them out.
Claimed: both decode, each with its own record, and the two decoded message parts agree on the
layout, in every row (`SameOn`).
The course, without the seeds and answers of samples. The verifier draws γ; the prover names u₀, u₁
= the folds at γ of the full messages of the rows of the two encoded indices; the verifier draws, in
one message, t₀ locations of the first and t₁ of the further one; then it draws φ.
The rows that are left: the record's row of each on its own fold (`X.RecRow`); the codeword of u₀
(u₁) has at the drawn locations the folds of the columns read; and one equality row (`EqRow`),
restricted to the layout. No row couples the two inputs before.

Main names:
  `Spec.ldLk_complete`: completeness, for tables of full messages that agree on the layout.
  `Spec.ldLk_cnt_eq`, `Spec.ldLk_cnt_gam`: at most v·|E|^(v-1) points γ have `BadEq`; at most ε₀ +
    ε₁ + v·|E|^(v-1) have `BadGam`, where ε₀, ε₁ bound the bad points of the two folds
    (`Spec.ldFe_cnt`, `Spec.ldFe_none`, Cb/Ld/LdFoldEq.lean, state such bounds, one in each regime,
    under their hypotheses). The two regimes, for a fold that is tested at the radius e' (e₀ for the
    first, e₁ for the further one; eM: the radius of decoding): first: no collision (`X.Coll`) at
    the record's seed, and e' ≤ eM below the distance; second: the index decodes, and e' + eM is
    below the distance.
  `Spec.ldLk_cnt_loc`: at most the larger of (n - e₀ - 1)^t₀ · n^t₁ and n^t₀ · (n - e₁ - 1)^t₁, of
    the n^(t₀+t₁) pairs of lists, have `BadLoc2` (n: the number of positions, |ι|): which of the two
    folds is far is fixed before the locations are drawn. Not the sum.
  `Spec.ldLk_cnt_phi`: if `D.pl` is injective, at most l·|E|^(l-1) points φ have `BadPhi`.
  `Spec.ldLk_back_gam`: γ not bad; u₀ near the first fold, u₁ near the other, each meets its
    record's row, and they agree on the layout: then both indices decode and agree on the layout.
  `Spec.ldLk_back_phi`: φ not bad and the equality row: u₀ and u₁ agree on the layout.

Of note in this link: records and their rows; equality on the layout
only; of a fold "near", not "decodes"; the case "the further index does not decode" is inside
`X.Bad`.

Limits: this file says nothing on samples and lists of the two oracle messages that hold u₀, u₁;
nothing on the test that closes the rows, on zero knowledge. It does not say that agreement on the
layout means "the same index": that is a law of the configuration.
Terms: lean/GLOSSARY.md.
The link follows this protocol's technical report, which follows the work that this protocol builds
on (lean/CREDITS.md, "Further work").
-/
import Cb.Ld.LdFoldEq

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

/-- The link, on vectors: the data. -/
structure LdLkW (E ι κ J Λ : Type) where
  /-- the format of both encoded indices -/
  X   : LdIx E ι κ J
  /-- the places of the layout in a message part -/
  lay : Λ → J
  /-- the number of coordinates of φ; the places of the layout as vertices of a cube -/
  l   : ℕ
  pl  : Λ → Fin l → Bool

namespace LdLkW
variable {E ι κ J Λ : Type} (D : LdLkW E ι κ J Λ)

/-- Two message parts agree on the layout. -/
def SameOn (U U' : D.X.Row × J → E) : Prop := ∀ r a, U (r, D.lay a) = U' (r, D.lay a)

/-- The layout part of one full message. -/
def layV (u : κ → E) : Λ → E := fun a => D.X.msg u (D.lay a)

variable [Field E]

/-- The equality row. -/
def EqRow [Fintype Λ] (φ : Fin D.l → E) (u₀ u₁ : κ → E) : Prop :=
  ∑ a, Alg.eqk φ (D.pl a) * (D.layV u₀ a - D.layV u₁ a) = 0

def BadEq (U₀ U₁ : D.X.Row × J → E) (γ : Fin D.X.v → E) : Prop :=
  ¬ D.SameOn U₀ U₁ ∧ ∀ a, foldV γ U₀ (D.lay a) = foldV γ U₁ (D.lay a)

def BadPhi [Fintype Λ] (u₀ u₁ : κ → E) (φ : Fin D.l → E) : Prop :=
  D.layV u₀ ≠ D.layV u₁ ∧ D.EqRow φ u₀ u₁

variable [Fintype ι] [Fintype κ]

/-- The codeword of u has at the drawn locations the values of the word w. -/
def ColW {t : ℕ} (w : ι → E) (u : κ → E) (Q : Fin t → ι) : Prop :=
  ∀ i, D.X.G.mulVec u (Q i) = w (Q i)

/-- The bad pairs of lists of locations; w₀, w₁ are the two folded words. -/
def BadLoc2 {t₀ t₁ : ℕ} (e₀ e₁ : ℕ) (w₀ w₁ : ι → E)
    (u₀ u₁ : κ → E) (Q : (Fin t₀ → ι) × (Fin t₁ → ι)) : Prop :=
  (¬ D.X.NearW e₀ w₀ u₀ ∨ ¬ D.X.NearW e₁ w₁ u₁) ∧ D.ColW w₀ u₀ Q.1 ∧ D.ColW w₁ u₁ Q.2

variable [Fintype J]

/-- The bad points γ. -/
def BadGam (f₀ f₁ : D.X.Row → ι → E) (rec₀ rec₁ : D.X.Rec) (e₀ e₁ : ℕ) (γ : Fin D.X.v → E) : Prop :=
  D.X.Bad f₀ rec₀ e₀ γ ∨
  D.X.Bad f₁ rec₁ e₁ γ ∨
  ∃ U₀ U₁, D.X.dec f₀ rec₀ = some U₀ ∧ D.X.dec f₁ rec₁ = some U₁ ∧ D.BadEq U₀ U₁ γ

end LdLkW

namespace Spec
section
variable (E ι κ J Λ : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Λ]

/-- Completeness, for two tables of full messages that agree on the layout: no exception. -/
def ldLk_complete : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (M₀ M₁ : D.X.Row → κ → E) (γ : Fin D.X.v → E) (φ : Fin D.l → E),
    D.SameOn (D.X.view M₀) (D.X.view M₁) →
    D.layV (foldAll γ M₀) = D.layV (foldAll γ M₁) ∧ D.EqRow φ (foldAll γ M₀) (foldAll γ M₁)

/-- The backward step at γ. -/
def ldLk_back_gam : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (f₀ f₁ : D.X.Row → ι → E) (rec₀ rec₁ : D.X.Rec) (e₀ e₁ : ℕ)
      (γ : Fin D.X.v → E) (u₀ u₁ : κ → E),
    ¬ D.BadGam f₀ f₁ rec₀ rec₁ e₀ e₁ γ → D.X.NearW e₀ (foldAll γ f₀) u₀ → D.X.RecRow rec₀ γ u₀ →
    D.X.NearW e₁ (foldAll γ f₁) u₁ → D.X.RecRow rec₁ γ u₁ → D.layV u₀ = D.layV u₁ →
    ∃ U₀ U₁, D.X.dec f₀ rec₀ = some U₀ ∧ D.X.dec f₁ rec₁ = some U₁ ∧ D.SameOn U₀ U₁

/-- The backward step at φ. -/
def ldLk_back_phi : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (u₀ u₁ : κ → E) (φ : Fin D.l → E),
    ¬ D.BadPhi u₀ u₁ φ → D.EqRow φ u₀ u₁ → D.layV u₀ = D.layV u₁

/-- The two lists of locations: the larger of the two errors. -/
def ldLk_cnt_loc : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (t₀ t₁ e₀ e₁ : ℕ) (w₀ w₁ : ι → E) (u₀ u₁ : κ → E),
    cnt (D.BadLoc2 (t₀ := t₀) (t₁ := t₁) e₀ e₁ w₀ w₁ u₀ u₁) ≤
      max ((Fintype.card ι - e₀ - 1) ^ t₀ * Fintype.card ι ^ t₁)
        (Fintype.card ι ^ t₀ * (Fintype.card ι - e₁ - 1) ^ t₁)

variable [Fintype E]

def ldLk_cnt_eq : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (U₀ U₁ : D.X.Row × J → E),
    cnt (D.BadEq U₀ U₁) ≤ D.X.v * Fintype.card E ^ (D.X.v - 1)

/-- The round of γ. -/
def ldLk_cnt_gam : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (f₀ f₁ : D.X.Row → ι → E) (rec₀ rec₁ : D.X.Rec) (e₀ e₁ ε₀ ε₁ : ℕ),
    cnt (D.X.Bad f₀ rec₀ e₀) ≤ ε₀ → cnt (D.X.Bad f₁ rec₁ e₁) ≤ ε₁ →
    cnt (D.BadGam f₀ f₁ rec₀ rec₁ e₀ e₁) ≤ ε₀ + ε₁ + D.X.v * Fintype.card E ^ (D.X.v - 1)

def ldLk_cnt_phi : Prop :=
  ∀ (D : LdLkW E ι κ J Λ) (u₀ u₁ : κ → E),
    Function.Injective D.pl → cnt (D.BadPhi u₀ u₁) ≤ D.l * Fintype.card E ^ (D.l - 1)

end
end Spec
end Cb
