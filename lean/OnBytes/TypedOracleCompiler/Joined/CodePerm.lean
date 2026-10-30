-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/CodePerm.lean: a code of strings (`Rom.StrCode`, Rom/Hotel.lean) carried along a
permutation of what is coded.

A tool for tests of theorems that speak of several codings of the typed oracles over one hash
function: from one code, another that differs from it at chosen points. Nothing on soundness.


Main names: `permCode`; `put_inj`: a code of strings is one to one.

That a countable type has a code, and that a coding exists at every carrier of countable types, are
the library's: `Rom.StrCode.ofCountable` (CompileK/ImplExists.lean),
`TypedOracleCompiler.Compile.Batch.countable_pts`, `exists_impl` (Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean).

Limits: one definition and one lemma on codes of strings. No coding of the typed oracles is built
here, and no hash function, protocol or program is named.

Terms: lean/GLOSSARY.md.
-/
import Rom.Hotel
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open Rom

/-- A code of strings, carried along a permutation of what is coded. -/
def permCode {A : Type} (c : StrCode A) (σ : A ≃ A) : StrCode A where
  put := fun a => c.put (σ a)
  parse := fun s => (c.parse s).map σ.symm
  parse_put := fun a => by
    rw [c.parse_put, Option.map_some, Equiv.symm_apply_apply]
  put_parse := fun s a h => by
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [Equiv.apply_symm_apply]
    exact c.put_parse s b hb

/-- A code of strings is one to one. -/
theorem put_inj {A : Type} (c : StrCode A) : Function.Injective c.put := fun a b h =>
  Option.some.inj (by rw [← c.parse_put a, ← c.parse_put b, h])

end TypedOracleCompiler.Joined
