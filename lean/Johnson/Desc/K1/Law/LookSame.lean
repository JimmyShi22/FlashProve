-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project that is not in this repository: as copied, the same
-- bytes behind this line.
/-
Johnson/Desc/K1/Law/LookSame.lean: a relation on two states of the first chain (`First.S`): the open
ledger, the open link's context, the count of rows owed and what was heard of the lookup on the
calls are the same. A definition, with its two plain laws.

Main names: `LookSame`, `LookSame.refl`, `LookSame.trans`.

What is not claimed. NOTHING ON THE SMALLNESS TEST's PART `tl` OF THE STATE: the quiet steps behind
a sending of the reads write it. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (S)

/-- Four readers of the state answer at s' as at s. -/
structure LookSame (s s' : S) : Prop where
  fork : s'.fork? = s.fork?
  link : s'.link? = s.link?
  owed : s'.rowsOwed = s.rowsOwed
  look : s'.lookHeard? = s.lookHeard?

theorem LookSame.refl (s : S) : LookSame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem LookSame.trans {a b c : S} (h : LookSame a b) (k : LookSame b c) : LookSame a c :=
  ⟨k.fork.trans h.fork, k.link.trans h.link, k.owed.trans h.owed, k.look.trans h.look⟩

end VerifiableInference.Desc.K1
