-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Claims/TablesTree.lean: kind K5: every table that an attention segment's
quiet step lays into the state names array number 2.

  `tabs_tree`: tablesP g mats nW lk p = some t → every member of (tabsBack t).funs has tree = 2.

By `tablesP_lays` (Johnson/Desc/First/Att/Claims/ReadsOfIs.lean): the list that tablesP returns is
tablesA over the declared reads, and tablesA writes 2 in that field. The one line of the kind's text
that makes a table (Johnson/Desc/First/Att/TablesP.lean) writes the same.

Is it empty? Where tablesP returns no table the statement says nothing; where it refuses, nothing.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsOfIs
import Johnson.Desc.First.Att.TabsBack

set_option autoImplicit false

namespace K5Law
open VerifiableInference.Desc.First.Att VerifiableInference.Desc.First.Att.P

/-- Every table of the segment's list names array number 2. -/
theorem tabs_tree {g : Geo} {lk : LookIn} {p : Pts} {nW : Nat} {t : TablesP}
    {mats : Array (Nat × Nat)} (h : P.tablesP g mats nW lk p = some t) :
    ∀ f ∈ (tabsBack t).funs.toList, f.tree = 2 := by
  intro f hf
  rw [show (tabsBack t).funs = t.funs.map funBack from rfl, Array.toList_map,
    (tablesP_lays h).1] at hf
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
  obtain ⟨r, _, hq⟩ := List.mem_flatMap.1 hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hq
  rfl

#print axioms tabs_tree

end K5Law
