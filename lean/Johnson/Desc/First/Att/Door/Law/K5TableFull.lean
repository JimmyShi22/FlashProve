-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TableFull.lean: kind K5: K5Table
(Johnson/Desc/First/Att/Door/Law/K5AtMgPaid.lean: the four fields of K5Owes that are tests on the
table's lists alone) AT THE FULL WRITTEN LIST OF SEGMENTS, AT EACH OF ITS TWELVE ATTENTION SEGMENTS:
a theorem: decisions by the kernel
(Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean) laid into the structure.

THE LETTERS: `LFull` := twelve times (layers, attention), then the output head · `PFull` :=
flatPlacesOf LFull true · k := 14 (2 g + 1) + 4 · pl := ⟨1, some (2 g + 1), 3, .K5⟩ · O := what is
open at border k · Q := the public items open there AT THE WIDER LIST OVER THE EMPTY BASE (morePlus
{}). LIMITS (that file's own): decided at the table's text as this library has it, at no other ·
that the composed meaning's list of segments and its base's list are these texts is owed by rfl in
a build that holds them. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.K5AtMgPaid
import Johnson.Desc.First.Att.Door.Law.K5ListsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc VerifiableInference.Desc.First

/-- The full written list of segments. -/
abbrev LFull : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]

/-- Its places. -/
abbrev PFull : List Place := flatPlacesOf LFull true

/-- **The four tests on the table's lists, at the full list.** -/
theorem k5Table_full {g : ℕ} (hg : g < 12) :
    K5Table g LFull ⟨1, some (2 * g + 1), 3, .K5⟩ ((openSets LFull PFull (start LFull))[14 * (2 * g + 1) + 4]?.getD [])
      ((pubSets (morePlus {}) LFull PFull)[14 * (2 * g + 1) + 4]?.getD []) :=
  { openQ := twenty_full hg
    tiesO := ties_full hg
    openIn := openQ_full hg
    tiedObj := tiedObj_full hg }

end H2K5.Door

#print axioms H2K5.Door.k5Table_full
