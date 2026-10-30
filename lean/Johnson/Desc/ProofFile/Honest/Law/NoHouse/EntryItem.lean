-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/EntryItem.lean: FROM AN ENTRY OF A LINK's ORDER OF CLAIMS
TO AN ITEM OF THE TABLE. The library's SortItems.lean (Johnson/Desc/First/Link/Law/) goes from an
item `forms m kk r` that a segment's batching closes to the entries of the order that it stands for
(`hruns_of_sort`), and says as a decided Bool that every entry of the order is such a run
(`items_tight`). Here that Bool read as a sentence: at every entry o of the sort's order there is an
item `forms m kk r` among those that the batching closes, with o among the runs that it stands for.

WHAT THIS IS. Two lemmas on the library's closed tables of names. None of the library's goals.

  `form_of_name`, `item_of_entry`

Limits. Closed facts on names. Nothing on any state. Nothing on any property.

-/
import Johnson.Desc.First.Link.Law.SortItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (ModelPart Item formsOf runsOf)
open VerifiableInference.Desc.Sound (runsAt)
open VerifiableInference.Desc.LinkJoin (sortItems formNames formNames_at items_tight)

/-- A name of forms of the table at a sort is an item of every segment of that sort. -/
theorem form_of_name (sub : ModelPart) (m : Nat) (x : Nat × String) (h : x ∈ formNames sub) :
    Item.forms m x.1 x.2 ∈ formsOf sub m := by
  rw [← formNames_at sub m] at h
  obtain ⟨i, hi, e⟩ := List.mem_filterMap.1 h
  have hseg : ∀ j ∈ formsOf sub m, ∀ m' k r, j = Item.forms m' k r → m' = m := by
    intro j hj m' k r ej
    subst ej
    cases sub <;> simp [formsOf] at hj <;> omega
  cases i with
  | forms m' k r =>
    obtain rfl := hseg _ hi m' k r rfl
    have e' : some (k, r) = some x := e
    obtain rfl := Option.some.inj e'
    exact hi
  | _ => cases e

/-- **FROM ENTRY TO ITEM.** -/
theorem item_of_entry (links : List ModelPart) (m : Nat) (sub : ModelPart) (hs : links[m]? = some sub) :
    ∀ o ∈ sortItems sub, ∃ kk r, Item.forms m kk r ∈ formsOf sub m ∧ o ∈ runsAt links m kk r := by
  intro o ho
  have h1 := List.contains_iff_mem.1 (List.all_eq_true.1 (items_tight sub) o ho)
  obtain ⟨x, hx, hox⟩ := List.mem_flatMap.1 h1
  refine ⟨x.1, x.2, form_of_name sub m x hx, ?_⟩
  unfold runsAt
  rw [hs]
  exact hox

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.form_of_name
#print axioms ProofFile.Honest.FirstThread.item_of_entry
