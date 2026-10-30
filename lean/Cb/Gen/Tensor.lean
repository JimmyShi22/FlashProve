-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/Tensor.lean: the format of an encoded index (the layout by column blocks) and a tensor form
on the index matrix.

In standard terms: a layout of a matrix with h rows and 2^(hi+lo) columns in the messages of an
interleaved code, and a linear form of the matrix with tensor-product coefficients. Definitions and
statements; the proofs are in Cb/Gen/TensorProofs.lean.

Main names:
  `IdxFmt`: the data. The encoding itself is not defined here: it is that of the component
    `IdxFmt.comp`, a `Comp` of Cb/Gen/Code.lean (unique decoding).
  The layout, public and, under `Φ.Fits`, injective: the entry (y, c) of the matrix stands in row
    c / 2^lo at the place 2^lo · y + c mod 2^lo of that row's message. `IdxFmt.Fits`: the places of
    the layout lie in the message part of the code.
  `IdxFmt.put W`: the message that holds the matrix W. `IdxFmt.get m`: the matrix that is read off
    a message at the layout; 0 outside the h rows and 2^(hi+lo) columns.
  `IdxFmt.form g ψ W`: the tensor form; in standard terms, the multilinear extension of the vector
    gᵀ W, in the hi + lo bits of the column number, at the point ψ. `IdxFmt.rowCoef`: the same form
    as coefficients on the message of the encoded index. (The first hi coordinates of ψ belong to
    the most significant bits of a column number.)

  Stated (in `Cb.Spec`), under `Φ.Fits`: get ∘ put is the identity on matrices that are 0 outside
    the range (`get_put`); put is injective on them (`put_inj`); the tensor form of get m is the
    linear form with the coefficients rowCoef on m (`form_rows`). With no hypothesis on Φ: get reads
    the layout only (`get_congr`) and is 0 outside the range (`inRange_get`); put is 0 off the
    layout (`put_off`); put ∘ get gives m back at the places of the layout (`put_get`).

Conventions, as in Blocks/Basic.lean: matrices, vectors of coefficients and points are functions on
numbers; the form reads g at y < h only and ψ at its first hi + lo coordinates only.

Limits: this file says nothing on which matrices are indices. It
says nothing on any protocol. It says nothing on how the verifier evaluates g (Lean models no
running time).
The notions (layout, tensor form) follow definitions of this protocol's technical report
(lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.Code

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop Finset

/-- The format of an encoded index: the data. -/
structure IdxFmt (F : Type) where
  code : Code.Enc F
  /-- the number of rows of the index matrix -/
  h  : ℕ
  /-- the matrix has 2^(hi+lo) columns; the encoded index has 2^hi rows, each of which holds a block
  of 2^lo columns -/
  hi : ℕ
  lo : ℕ

namespace IdxFmt
variable {F : Type} (Φ : IdxFmt F)

/-- the places of the layout lie in the message part of the code -/
def Fits : Prop := 2 ^ Φ.lo * Φ.h ≤ Φ.code.msg

/-- the encoded index as a component of Cb/Gen/Code.lean: 2^hi interleaved rows over F -/
abbrev comp : Comp F := Comp.fin Φ.code (2 ^ Φ.hi) true

/-- a message of the encoded index: 2^hi rows over F. (It is (comp.enc E).Msg for every E, by
unfolding.) -/
abbrev Msg : Type := Fin (2 ^ Φ.hi) → Fin Φ.code.msg → F

/-- a matrix is 0 outside the h rows and 2^(hi+lo) columns -/
def InRange [Zero F] (W : ℕ → ℕ → F) : Prop :=
  ∀ y c, ¬ (y < Φ.h ∧ c < 2 ^ (Φ.hi + Φ.lo)) → W y c = 0

/-- The message that holds the matrix W: its entries at the layout, zeros elsewhere. -/
def put [Zero F] (W : ℕ → ℕ → F) : Φ.Msg :=
  fun ι j =>
    if j.val < 2 ^ Φ.lo * Φ.h then W (j.val / 2 ^ Φ.lo) (2 ^ Φ.lo * ι.val + j.val % 2 ^ Φ.lo) else 0

/-- The matrix that is read off a message at the layout. -/
def get [Zero F] (m : Φ.Msg) : ℕ → ℕ → F :=
  fun y c =>
    if y < Φ.h then nat (fun ι => nat (m ι) (2 ^ Φ.lo * y + c % 2 ^ Φ.lo)) (c / 2 ^ Φ.lo) else 0

section Form
variable [Field F] {E : Type} [Field E] [Algebra F E]

/-- The tensor form ⟨g ⊗ eq(ψ, ·), W⟩. -/
def form (g ψ : ℕ → E) (W : ℕ → ℕ → F) : E :=
  ∑ y ∈ range Φ.h,
    ∑ c ∈ range (2 ^ (Φ.hi + Φ.lo)), g y * eqN (Φ.hi + Φ.lo) 0 ψ c * algebraMap F E (W y c)

/-- the coefficient of the tensor form at the place j of row ι of the message -/
def rowCoef (g ψ : ℕ → E) (ι j : ℕ) : E :=
  eqN Φ.hi 0 ψ ι *
    (if j < 2 ^ Φ.lo * Φ.h then g (j / 2 ^ Φ.lo) * eqN Φ.lo Φ.hi ψ (j % 2 ^ Φ.lo) else 0)

end Form
end IdxFmt

namespace Spec

/-- Under `Φ.Fits`, reading undoes writing, for a matrix in range (`InRange`). -/
def get_put : Prop :=
  ∀ (F : Type) [Zero F] (Φ : IdxFmt F), Φ.Fits → ∀ W, Φ.InRange W → Φ.get (Φ.put W) = W

/-- The layout is injective: under `Φ.Fits`, two matrices in range with the same message are equal.
-/
def put_inj : Prop :=
  ∀ (F : Type) [Zero F] (Φ : IdxFmt F),
    Φ.Fits → ∀ W W', Φ.InRange W → Φ.InRange W' → Φ.put W = Φ.put W' → W = W'

/-- Zeros off the layout. -/
def put_off : Prop :=
  ∀ (F : Type) [Zero F] (Φ : IdxFmt F) (W : ℕ → ℕ → F) (ι : Fin (2 ^ Φ.hi)) (j : Fin Φ.code.msg),
    2 ^ Φ.lo * Φ.h ≤ j.val → Φ.put W ι j = 0

/-- What is read is 0 outside the range. -/
def inRange_get : Prop :=
  ∀ (F : Type) [Zero F] (Φ : IdxFmt F) (m : Φ.Msg), Φ.InRange (Φ.get m)

/-- Only the places of the layout are read. -/
def get_congr : Prop :=
  ∀ (F : Type) [Zero F] (Φ : IdxFmt F) (m m' : Φ.Msg),
    (∀ ι (j : Fin Φ.code.msg), j.val < 2 ^ Φ.lo * Φ.h → m ι j = m' ι j) → Φ.get m = Φ.get m'

/-- Writing undoes reading at the places of the layout. -/
def put_get : Prop :=
  ∀ (F : Type) [Zero F] (Φ : IdxFmt F) (m : Φ.Msg) (ι : Fin (2 ^ Φ.hi)) (j : Fin Φ.code.msg),
    j.val < 2 ^ Φ.lo * Φ.h → Φ.put (Φ.get m) ι j = m ι j

/-- Under `Φ.Fits`, the tensor form on the matrix is a linear form on the message of the encoded
index, and a tensor again: a factor on the rows times a factor on the places. -/
def form_rows : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F), Φ.Fits →
    ∀ (g ψ : ℕ → E) (m : Φ.Msg), Φ.form g ψ (Φ.get m) =
      ∑ ι : Fin (2 ^ Φ.hi), ∑ j : Fin Φ.code.msg, Φ.rowCoef g ψ ι.val j.val * algebraMap F E (m ι j)

end Spec
end Cb
