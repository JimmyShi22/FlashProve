-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingTag.lean.
Run/CodingTag.lean: what keeps the strings of different uses of the hash apart: the number in the
label, read off a bit string at a fixed place. A definition that computes, theorems. After the
format page's rules R2.1, R2.4 (the label stands behind the half and the 64 bytes of the parameter
block), not held against the page as it ships.
   tag16 s  the 16 bits of s from bit 520 on: the two low bytes of the label's first word
   tag16_at  a string that has 520 bits and then w in front has the first 16 bits of w as its tag,
       if w has at least 16
   tag16_hdr  of a string with the header of a call (a start of 32 bytes): the first 16 bits of the
       word number + 2^16 tree
   tag16_pre33  of a string that is pre33, 256 bits, and then w
   tag16_162  of a string in the shape of a round's call; p162_tag asks that the word with the
       chain's label has the rounds' number in its low 16 bits: at a given label an evaluation t160,
       t162, t164, t166, and that they differ
   apart  two partial codes whose strings have different tags write no common string (what PCode.sum
       asks)
What is not said. Nothing on a hash.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingImpl
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Run.CodingPage162
import Fmt.Rules23Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

/-- the tag of a round's call -/
theorem p162_tag {I X : Type} {L : BatchProtocolWithLeafBody I X} {tg : Tag} (D : ChainD L tg)
    (hl : (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.label))).take 16 = t162) (K : ℕ)
    (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool) (h : (p162 D K).put x = some s) :
    tag16 s = t162 := by
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162_shape D K x s h
  exact (tag16_162 _ ρ r hρ _).trans hl

end TypedOracleCompiler.Run
