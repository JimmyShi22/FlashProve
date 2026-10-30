-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Spell/Closed.lean: the five equations between the written committer's typed queries and
the format's own functions (`Bind.Cpp.Spells`, Johnson/Bind/Cpp/Spells.lean), gathered: at all
public files whose plan's salt has 40 bytes, at every hash function. Calls alone: nothing is proved
in this file. No definition: no goal is stated.
  `spellsLeaf`: `SpellsLeaf Z hash` from `SaltAt Z`: `spellsLeaf_of` (Leaf.lean) at
    `Bind.Cpp.spellsC` (Johnson/Bind/Cpp/SpellsC.lean).
  `spellsSeed`: `SpellsSeed Z hash`, no premise: `spellsSeed_of` (Seed.lean) at `spellsC`.
  **`spells`**: `Spells Z hash` from `SaltAt Z`: these two with `spellsC`, `spellsNode`
    (Johnson/Bind/Cpp/SpellsNode.lean) and `spellsId` (Johnson/Bind/Cpp/SpellsId.lean).
Limits. Those of the five files that are called. `SaltAt Z` IS A PREMISE AND IS SHOWN AT NO Z HERE.
Equations between values of this library's own terms: NOTHING ON ANY PROGRAM, and nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding. That the five suffice for a tie between two committers is
not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.Spell.Leaf
import Johnson.Bind.Spell.Seed
import Johnson.Bind.Cpp.SpellsC
import Johnson.Bind.Cpp.SpellsNode
import Johnson.Bind.Cpp.SpellsId

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Spell
open VerifierAndGoals VerifiableInference Bind.Cpp

/-- A leaf's answer is the format's leaf hash, where the plan's salt at Z has 40 bytes. -/
theorem spellsLeaf (Z : PublicFiles) (hs : SaltAt Z) (hash : Hash) : SpellsLeaf Z hash :=
  spellsLeaf_of Z hs hash (spellsC Z hash)

/-- The OOD seed, spelled, is the format's draw from the table's name. -/
theorem spellsSeed (Z : PublicFiles) (hash : Hash) : SpellsSeed Z hash :=
  spellsSeed_of Z hash (spellsC Z hash)

/-- **All five**, where the plan's salt at Z has 40 bytes. -/
theorem spells (Z : PublicFiles) (hs : SaltAt Z) (hash : Hash) : Spells Z hash :=
  ⟨spellsC Z hash, spellsLeaf Z hs hash, spellsNode Z hash, spellsSeed Z hash, spellsId Z hash⟩

end Bind.Spell

#print axioms Bind.Spell.spellsLeaf
#print axioms Bind.Spell.spellsSeed
#print axioms Bind.Spell.spells
