-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/PossThere.lean: A NAMED TEST IN THE PLACE OF A SILENT DEFAULT: every code switch
whose number of positions the table's numbers read is there. One definition, one theorem. No
Mathlib.

Why. `possAt bs n m` (Johnson/Desc/First/NumbersAtBlocks.lean) reads the number of positions of the
code switch into group m off the sub-protocol of the kind K2 that stands there; where it finds none
it answers 0, in silence. The test on the form of the rows' table (`rowsAtFit`) does not see that.

What is said. `possThereB bs n`: for every group m from 1 to n a sub-protocol of the kind K2 stands
in bs whose place's segment (n where the place names none) is m. `possAt_of_there`: where the test
accepts, `possAt bs n m` is `possOf` of such a sub-protocol: no default is read.

Limits. It says nothing on the number itself. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {St Cl : Type}

/-- Every code switch from group 1 to group n is there. -/
def possThereB (bs : List (Block St Cl)) (n : Nat) : Bool :=
  (List.range n).all fun i =>
    (bs.find? fun b => b.place.kind == .K2 && b.place.link.getD n == i + 1).isSome

/-- Where the test accepts, no default is read. -/
theorem possAt_of_there (bs : List (Block St Cl)) (n m : Nat) (h : possThereB bs n = true)
    (h1 : 1 ≤ m) (hn : m ≤ n) :
    ∃ b, (bs.find? fun b => b.place.kind == .K2 && b.place.link.getD n == m) = some b ∧
      possAt bs n m = possOf b := by
  have h' := List.all_eq_true.1 h (m - 1) (List.mem_range.2 (by omega))
  rw [show m - 1 + 1 = m by omega] at h'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h'
  exact ⟨b, hb, by unfold possAt; rw [hb]; rfl⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.possAt_of_there
