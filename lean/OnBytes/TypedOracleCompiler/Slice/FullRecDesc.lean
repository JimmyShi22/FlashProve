-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/FullRecDesc.lean: the Lean port's description of an entry's chain at the full-size
files of the setting "record with work", read as the sibling's, meets the four conditions that the
carrier for the entry asks of a description.

OnBytes/Slice/FullRecSz.lean has the description `frD` in the library's form, and
OnBytes/Slice/FullRecLink.lean has its 41 rounds as the link's five, the batching's and a chain's
(`fr_ds_C`). A carrier from the library's written link to the sibling's asks of the sibling's
description: its plan's field is the second; its rounds' data are the library's, read as the
sibling's (`PQ.ofLib`); its stored tables have the positions of the tables' code; its openings of
stored tables are the given ones. This file shows the four of `asTypedCompilerDescription frD`
(OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean): the same three fields, as the sibling's description.

Main theorems: `fr_two_field`, `fr_two_ds`, `fr_two_a`, `fr_two_xs`.

Not claimed. Nothing on soundness. Nothing on a decision, a compiler, a wiring, a page, bytes or a
file. The description is at an empty statement; its rounds and openings are the same at every
statement (`fr_ds_at`, `fr_xs_at`). The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryAccept
import OnBytes.Slice.FullRecLink

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open OnBytes.Slice TypedOracleCompiler.Run
open EntryAccept (asTypedCompilerDescription)

/-- The plan's field is the second. -/
theorem fr_two_field : (asTypedCompilerDescription frD).base.plan.field = .two := rfl

/-- The rounds' data are the library's, read as the sibling's: the link's five, the batching's, the
chain's. -/
theorem fr_two_ds : (asTypedCompilerDescription frD).ds =
    (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map PQ.ofLib := by
  rw [← fr_ds_C]
  exact PQ.rds_ofLib frD.base fr_roots

/-- The stored tables have the positions of the tables' code. -/
theorem fr_two_a : (asTypedCompilerDescription frD).a = frS.P.T.a := fr_a

/-- The openings of stored tables are the library's: both tables' at round number 3. -/
theorem fr_two_xs : (asTypedCompilerDescription frD).xs = frD.xs ∧
    (asTypedCompilerDescription frD).xs = [⟨3, false, 0, 62⟩, ⟨3, true, 62, 62⟩] := ⟨rfl, fr_xs⟩

end TypedOracleCompiler.Slice
