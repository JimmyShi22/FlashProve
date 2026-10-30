-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartTieNm.lean: a body's matrix of cells made of two rectangles: the packed rows that were
kept, with their own naming, and the packed rows of one new layer.

Definitions and statements (the statements in `Cb.Spec`); the proofs are in
Cb/Part/LdPartTieNmProofs.lean. Plain mathematics on namings (`LdPartNm`, Cb/Part/LdPartCells.lean)
and packings (Cb/Ld/LdRngAlg.lean, Cb/Part/LdPartPkRes.lean). No protocol, no message, no partition.
The statements say, each under its hypotheses, that what is laid, what is packed and what is read in
the whole is what is laid, packed and read in the parts. In standard terms: book-keeping for the
range check across two consecutive stages of a request: the integer matrix that the later stage
checks is read off packed rows carried over from the earlier stage and packed rows just sent.

Why: after a closing the next body reads cells of earlier segments off the messages that were kept
and its own cells off the messages just sent. Each stage has a naming of its matrix. That the
namings of two stages mean the same integers is needed for the exact and for the relaxed relation;
here it is stated once, for arbitrary parameters. The packing factor is in types (a row of cells is
(packed row, lane below P)). The three objects that meet here (the naming before, the naming after,
the layer) each bring their own P. They are assumed equal as numbers, and lanes are compared by
their values: no statement holds a cast.

Main names (a row gives the premises that are its own; `PartOf` or `OwnAt` of the parts, `OK` of the
namings and equal packing factors are in the statements that need them; and whatever the arguments
hold as proofs, among them a `RngPar`'s `neC`: its type C of columns is not empty):
  `nm₀.PartOf nm₁ ι κ`, `nm.OwnAt P' j rows cols oR oC`: see their docstrings.
  `layO P' j rows cols Z`: the layer as a matrix of cells.
  `Spec.ldPartTieNm_layPart`: `nm₁.lay Z` on the part is `nm₀.lay Z`.
  `Spec.ldPartTieNm_layOwn`: `nm.lay Z` on the own rectangle is the layer.
  `Spec.ldPartTieNm_packX`: if the two rectangles cover all pairs (packed row, column): the kept
    part is the packing of `nm₀.lay Z`, the own part is the packing of the layer ⇒ the whole is the
    packing of `nm₁.lay Z`. No condition on the radix.
  `Spec.ldPartTieNm_packOwn`: the same where nothing was kept: the layer's rectangle alone covers.
  `Spec.ldPartTieNm_readPart`: under unique packing (`Uniq`, at the characteristic of E): the whole
    a packing of cells below b ⇒ the matrices read off the whole by nm₁ and off the part by nm₀
    agree at every row that nm₀ names, in all columns.
  `Spec.ldPartTieNm_readOwn`: under the same two premises (unique packing; the whole a packing of
    cells below b): nm reads, at (j, r, c) inside the layer's shape, the cell ((r / P', r mod P'),
    c) of the own part.

Limits: this file does not say that a cover exists: a cover forces every packed row to have an entry
in every column of the body, so all layers have one width. It does not say which kept rows nm₀
names. The file is generic in nm₀: it need not name all that is kept. It says nothing on reads
(`ReadBy`), masks, messages.
How it stands to a write-up of ours (lean/CREDITS.md; by reading): the picture is the
write-up's:
behind a closing a segment reads its own cells off the messages just sent and an earlier matrix off
whichever message holds its packing there: the kept one, or the one into which a closing has encoded
it anew; its range predicate speaks of one integer matrix made of both; each matrix gets zero rows
at its end until P divides its number of rows, so no packed row straddles two matrices ("a kept unit
is whole packed rows" is finer than the write-up's unit, a whole matrix). Declared
differences.
(1) The layout: there the matrices stand along a diagonal, zeros elsewhere; here they are stacked on
the same columns. The range check's ternary matrix then has one row for each of the Cw columns,
where the write-up has the sum of the widths: another verifier message: a difference of
format.
(2) The cover: there padding has no place: zeros of the big matrix are not sent. Where the cover is
realised by entries of messages, narrow matrices are sent at the full width: more rows than the
write-up counts.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPartCellsProofs
import Cb.Part.LdPartPkRes

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

namespace LdPartNm

/-- Says: nm₀ is the part of nm₁ on the packed rows ι and the columns κ (both injective). -/
structure PartOf {p₀ p₁ : RngPar} (nm₀ : LdPartNm p₀) (nm₁ : LdPartNm p₁)
    (ι : p₀.Rp → p₁.Rp) (κ : p₀.C → p₁.C) : Prop where
  injR : Function.Injective ι
  injC : Function.Injective κ
  row  : ∀ s r, r < nm₀.R s →
    r < nm₁.R s ∧
    (nm₁.rowAt s r).1 = ι (nm₀.rowAt s r).1 ∧
    ((nm₁.rowAt s r).2 : ℕ) = ((nm₀.rowAt s r).2 : ℕ)
  col  : ∀ s, 0 < nm₀.R s → nm₀.C s = nm₁.C s ∧ ∀ c < nm₀.C s, nm₁.colAt s c = κ (nm₀.colAt s c)
  back : ∀ s r i, r < nm₁.R s → (nm₁.rowAt s r).1 = ι i → r < nm₀.R s

/-- Says: the segment j's matrix is on the rectangle oR × oC (both injective) in the standard order;
back: nm names no other segment's row there. -/
structure OwnAt {p : RngPar} (nm : LdPartNm p) (P' j rows cols : ℕ) {rp Cw : ℕ}
    (oR : Fin rp → p.Rp) (oC : Fin Cw → p.C) : Prop where
  injR : Function.Injective oR
  injC : Function.Injective oC
  R    : nm.R j = rows
  C    : nm.C j = cols
  row  : ∀ r < rows,
    ∃ i : Fin rp, (i : ℕ) = r / P' ∧ (nm.rowAt j r).1 = oR i ∧ ((nm.rowAt j r).2 : ℕ) = r % P'
  col  : ∀ c < cols, ∃ c' : Fin Cw, (c' : ℕ) = c ∧ nm.colAt j c = oC c'
  back : ∀ s r i, r < nm.R s → (nm.rowAt s r).1 = oR i → s = j

end LdPartNm

/-- the layer as a matrix of cells -/
def layO (P' j rows cols : ℕ) {rp Cw : ℕ} (Z : ℕ → ℕ → ℕ → ℤ) : Fin rp × Fin P' → Fin Cw → ℤ :=
  fun r c =>
    if r.1.val * P' + r.2.val < rows ∧ c.val < cols then Z j (r.1.val * P' + r.2.val) c.val else 0

namespace Spec

def ldPartTieNm_layPart : Prop :=
  ∀ (p₀ p₁ : RngPar) (nm₀ : LdPartNm p₀) (nm₁ : LdPartNm p₁) (ι : p₀.Rp → p₁.Rp)
      (κ : p₀.C → p₁.C) (Z : ℕ → ℕ → ℕ → ℤ),
    nm₀.OK → nm₁.OK → nm₀.PartOf nm₁ ι κ →
    ∀ (i : p₀.Rp) (c : p₀.C) (l₀ : Fin p₀.P) (l₁ : Fin p₁.P),
      (l₀ : ℕ) = l₁ → nm₁.lay Z (ι i, l₁) (κ c) = nm₀.lay Z (i, l₀) c

def ldPartTieNm_layOwn : Prop :=
  ∀ (p : RngPar) (nm : LdPartNm p) (P' j rows cols rp Cw : ℕ) (oR : Fin rp → p.Rp)
      (oC : Fin Cw → p.C) (Z : ℕ → ℕ → ℕ → ℤ),
    nm.OK → nm.OwnAt P' j rows cols oR oC →
    ∀ (i : Fin rp) (c : Fin Cw) (l' : Fin P') (l : Fin p.P),
      (l' : ℕ) = l → nm.lay Z (oR i, l) (oC c) = layO P' j rows cols Z (i, l') c

/-- Packed in the whole: packed in the part. (not all hypotheses are named here: see the statement
below) -/
def ldPartTieNm_packPart : Prop :=
  ∀ (E : Type) [CommRing E] (p₀ p₁ : RngPar) (nm₀ : LdPartNm p₀) (nm₁ : LdPartNm p₁)
      (ι : p₀.Rp → p₁.Rp) (κ : p₀.C → p₁.C) (Z : ℕ → ℕ → ℕ → ℤ) (b ϱ : ℤ) (mpk : p₁.Rp → p₁.C → E),
    p₀.P = p₁.P → nm₀.OK → nm₁.OK → nm₀.PartOf nm₁ ι κ →
    PackBy b ϱ (nm₁.lay Z) mpk → PackBy b ϱ (nm₀.lay Z) (resM ι κ mpk)

/-- Packed in the parts of a cover: packed in the whole. (not all hypotheses are named here: see the
statement below) -/
def ldPartTieNm_packX : Prop :=
  ∀ (E : Type) [CommRing E] (p₀ p₁ : RngPar) (nm₀ : LdPartNm p₀) (nm₁ : LdPartNm p₁)
      (ι : p₀.Rp → p₁.Rp) (κ : p₀.C → p₁.C) (P' j rows cols rp Cw : ℕ) (oR : Fin rp → p₁.Rp)
      (oC : Fin Cw → p₁.C) (Z : ℕ → ℕ → ℕ → ℤ) (b ϱ : ℤ) (mpk : p₁.Rp → p₁.C → E),
    p₀.P = p₁.P → P' = p₁.P → nm₀.OK → nm₁.OK → nm₀.PartOf nm₁ ι κ →
    nm₁.OwnAt P' j rows cols oR oC →
    (∀ i c, (∃ i' c', ι i' = i ∧ κ c' = c) ∨ ∃ i' c', oR i' = i ∧ oC c' = c) →
    PackBy b ϱ (nm₀.lay Z) (resM ι κ mpk) →
    PackBy b ϱ (layO P' j rows cols Z) (resM oR oC mpk) → PackBy b ϱ (nm₁.lay Z) mpk

/-- The same where the layer's rectangle alone covers. (not all hypotheses are named here: see the
statement below) -/
def ldPartTieNm_packOwn : Prop :=
  ∀ (E : Type) [CommRing E] (p : RngPar) (nm : LdPartNm p) (P' j rows cols rp Cw : ℕ)
      (oR : Fin rp → p.Rp) (oC : Fin Cw → p.C) (Z : ℕ → ℕ → ℕ → ℤ) (b ϱ : ℤ) (mpk : p.Rp → p.C → E),
    P' = p.P → nm.OK → nm.OwnAt P' j rows cols oR oC → (∀ i c, ∃ i' c', oR i' = i ∧ oC c' = c) →
    PackBy b ϱ (layO P' j rows cols Z) (resM oR oC mpk) → PackBy b ϱ (nm.lay Z) mpk

/-- Read in the whole, read in the kept part. (not all hypotheses are named here: see the statement
below) -/
def ldPartTieNm_readPart : Prop :=
  ∀ (E : Type) [CommRing E] (pp : ℕ) [CharP E pp] (p₀ p₁ : RngPar) (nm₀ : LdPartNm p₀)
      (nm₁ : LdPartNm p₁) (ι : p₀.Rp → p₁.Rp) (κ : p₀.C → p₁.C) (b ϱ : ℤ) (mpk : p₁.Rp → p₁.C → E),
    p₀.P = p₁.P → nm₀.PartOf nm₁ ι κ → Uniq b ϱ p₁.P pp → Packed p₁.P b ϱ mpk →
    ∀ s r c, r < nm₀.R s →
      nm₁.mats (cells p₁.P b ϱ mpk) s r c = nm₀.mats (cells p₀.P b ϱ (resM ι κ mpk)) s r c

/-- Read in the whole, read in the layer. (not all hypotheses are named here: see the statement
below) -/
def ldPartTieNm_readOwn : Prop :=
  ∀ (E : Type) [CommRing E] (pp : ℕ) [CharP E pp] (p : RngPar) (nm : LdPartNm p)
      (P' j rows cols rp Cw : ℕ) (oR : Fin rp → p.Rp) (oC : Fin Cw → p.C)
      (b ϱ : ℤ) (mpk : p.Rp → p.C → E),
    P' = p.P → nm.OwnAt P' j rows cols oR oC → Uniq b ϱ p.P pp → Packed p.P b ϱ mpk →
    ∀ (r c : ℕ) (i : Fin rp) (l : Fin P') (c' : Fin Cw), r < rows → c < cols → (i : ℕ) = r / P' →
      (l : ℕ) = r % P' → (c' : ℕ) = c →
      nm.mats (cells p.P b ϱ mpk) j r c = cells P' b ϱ (resM oR oC mpk) (i, l) c'

end Spec
end Cb
