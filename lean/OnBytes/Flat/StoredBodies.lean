-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/StoredBodies.lean: how a symbol of a stored table is written into the body of a leaf,
and read back: a body is a string of bits, the stored leaf's own string as the format hashes it
between the start and the salt.

A symbol is a pair (position, column). It is written by the code of the stored tables' symbols
(`pStored`, OnBytes/TypedOracleCompiler/Run/Tag174.lean): the label under the number 174 with the column's and the
salt's numbers of words, the index 2^depth + position, the column, the fill. Where that code writes
nothing (a column of 2^24 words or more; a label's word of 2^64 or more) the body is an escape of 16
bits, with which no string of that code begins, and then the string of a total code of all
symbols (`PCode.orElse`, Run/CodingPart.lean). So every symbol has a body and is read back.

Main names.
  `escS`: the escape. `cS`: the total code, from the library's serialisers.
  `embStored a salt`, `prjStored a salt`: the two maps. a: the stored table's depth; salt: the
    length of a file's salt, in bytes.
  `prjStored_embStored`: what is written is read back, for all symbols.
  `embStored_fit`: where `storedOK` holds, the body is `storedStr`: the bits of the format's label
    under the number 174, with the index 2^depth + the symbol's own position, and of column and
    fill.

Limits: the law, and what a body is where the format's code writes. A symbol brings its own
position: that it is the position at which the symbol is read is said by nothing here. Nothing on
salts, on hashes, on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.Tag174
import Run.CodingPart
import Compile.Ser
import Run.PageQ

set_option autoImplicit false

namespace OnBytes.Flat
open Rom _root_.Run
open _root_.Iop (Ser)
open TypedOracleCompiler.Run (t174 pStored storedStr storedOK pStored_some pStored_put pStored_tag)

/-- The escape: 16 bits that are not the first 16 of a label under 174. -/
def escS : List Bool := List.replicate 16 false

/-- The escape is not the first 16 bits of a label under 174. -/
theorem escS_ne : escS ≠ t174 := by decide +kernel

/-- A total code of all stored symbols (position, column), from the library's serialisers. -/
def cS : StrCode (ℕ × List UInt64) := (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)).toStrCode

variable (a salt : ℕ)

/-- No string of the stored symbols' code begins with the escape. -/
theorem stored_no_escS (y : ℕ × List UInt64) (s : List Bool)
    (h : (pStored a salt).put y = some s) : ¬ escS <+: s := by
  rintro ⟨r, rfl⟩
  exact escS_ne ((List.take_left' (l₂ := r) (rfl : escS.length = 16)).symm.trans
    (pStored_tag a salt y _ h).2)

/-- A stored symbol (position, column) as a body. -/
def embStored : ℕ × List UInt64 → List Bool :=
  ((pStored a salt).orElse cS escS (stored_no_escS a salt)).put

/-- A body read as a stored symbol. -/
def prjStored : List Bool → Option (ℕ × List UInt64) :=
  ((pStored a salt).orElse cS escS (stored_no_escS a salt)).parse

/-- What is written is read back, for all symbols. -/
theorem prjStored_embStored (y : ℕ × List UInt64) :
    prjStored a salt (embStored a salt y) = some y :=
  ((pStored a salt).orElse cS escS (stored_no_escS a salt)).parse_put y

/-- Where `storedOK` holds, a symbol's body is `storedStr`. -/
theorem embStored_fit (y : ℕ × List UInt64) (h : storedOK a salt y) :
    embStored a salt y = storedStr a salt y :=
  PCode.orElse_put_some _ _ _ _ (pStored_some a salt y h)

end OnBytes.Flat
