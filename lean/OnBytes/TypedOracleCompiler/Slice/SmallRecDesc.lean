-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SmallRecDesc.lean: the Lean port's description of an entry's chain at the small
files of the setting "record with work", read as the sibling's, meets the four conditions that the
carrier for the entry asks of a description.

OnBytes/Slice/SmallRecSz.lean has the description `srD` in the library's form, and
OnBytes/Slice/SmallRecLink.lean has its 24 rounds as the link's five, the batching's and a chain's
(`sr_ds_C`). A carrier from the library's written link to the sibling's asks of the sibling's
description: its plan's field is the second; its rounds' data are the library's, read as the
sibling's (`PQ.ofLib`); its stored tables have the positions of the tables' code; its openings of
stored tables are the given ones. This file shows the four of `asTypedCompilerDescription srD`
(OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean): the same three fields, as the sibling's description.

Main theorems: `sr_two_field`, `sr_two_ds`, `sr_two_a`, `sr_two_xs`.

Not claimed. Nothing on soundness. Nothing on a decision, a compiler, a wiring, a page, bytes or a
file. The description is at an empty statement; its rounds and openings are the same at every
statement (`sr_ds_at`, `sr_xs_at`). The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryAccept
import OnBytes.Slice.SmallRecLink

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open OnBytes.Slice TypedOracleCompiler.Run
open EntryAccept (asTypedCompilerDescription)

/-- The plan's field is the second. -/
theorem sr_two_field : (asTypedCompilerDescription srD).base.plan.field = .two := rfl

/-- The rounds' data are the library's, read as the sibling's: the link's five, the batching's, the
chain's. -/
theorem sr_two_ds : (asTypedCompilerDescription srD).ds =
    (srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds).map PQ.ofLib := by
  rw [← sr_ds_C]
  exact PQ.rds_ofLib srD.base sr_roots

/-- The stored tables have the positions of the tables' code. -/
theorem sr_two_a : (asTypedCompilerDescription srD).a = srS.P.T.a := sr_a

/-- The openings of stored tables are the library's: both tables' at round number 3. -/
theorem sr_two_xs : (asTypedCompilerDescription srD).xs = srD.xs ∧
    (asTypedCompilerDescription srD).xs = [⟨3, false, 0, 51⟩, ⟨3, true, 51, 51⟩] := ⟨rfl, sr_xs⟩

end TypedOracleCompiler.Slice
