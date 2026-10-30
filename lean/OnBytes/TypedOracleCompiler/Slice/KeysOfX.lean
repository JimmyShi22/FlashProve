-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/KeysOfX.lean: the two keys of stored tables that are written of an instance of the
entry's protocol.

An instance of the entry's protocol is "both tables' answers; both tables' seeds" (XE,
OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean). The decision of `verify-on-bytes`
on an entry's chain takes two keys of tables (TableKey, OnBytes/Iop/Foldeq.lean). This
file writes the two keys of an instance: keyOf (OnBytes/Slice/KeyOfRec.lean) of the
first table's seeds and answers, with the item 0, and of the copy's, with the item 1. It
is a file of its own, with few imports, so that a program that runs the decision can
take the definition without what is proved of it. It stands in no noncomputable section.

Main definition: keysOfX.
Main theorems: keysOfX_items.

Not claimed. That these keys are those that a program makes of a file. Nothing on soundness. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyOfRec
import OnBytes.TypedOracleCompiler.Slice.EntryDelivers

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open OnBytes.Slice

/-- The two keys that are written of an instance: of the first table's seeds and answers, with
the item 0; of the copy's, with the item 1. an: how a table's answers are read. -/
def keysOfX {An : Type} (v lg s : ℕ) (an : An → (Fin v → Bool) × Fin s → GE) (x : XE An lg s) :
    OnBytes.TableKey × OnBytes.TableKey :=
  (keyOf (fun β : NZ => β.val) (x.2.1, an x.1.1),
    { keyOf (fun β : NZ => β.val) (x.2.2, an x.1.2) with item := 1 })

/-- The first key names the item 0, the second the item 1. -/
theorem keysOfX_items {An : Type} (v lg s : ℕ) (an : An → (Fin v → Bool) × Fin s → GE)
    (x : XE An lg s) : (keysOfX v lg s an x).1.item = 0 ∧ (keysOfX v lg s an x).2.item = 1 :=
  ⟨rfl, rfl⟩

end TypedOracleCompiler.Slice
