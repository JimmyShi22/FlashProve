-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortItems.lean: THE LETTER items OF WHAT IS LEFT OF A LINK's LAW
(`CoreRest2`, LinkRestAtSort2.lean; `CoreLeft`), CHOSEN: THE SORT's OWN ORDER OF
CLAIMS; WITH THE FIELD hruns PAID AT IT, AND THE PREMISE hit OF THE THREE PAYERS OF THE FIELD
hitems. A definition; statements and proofs; closed tests, decided, with negative lines.

Why this term. Two fields name items. hruns asks that it hold every run that the table's names of
forms stand for at the segment's sort. hitems asks its clause at every entry of items: so the list
should hold nothing more. The payers of hitems (hitems_layers, hitems_attention; a
third's hitems_head) are general in items under hit: every entry of items is among the sort's
listed entries. The driver's own order of a segment's claims (First.orderOf sub) is that list: it
holds just the runs that the table names (`items_tight`), and it is the link's own L.order (by the
segment's fact).

What is said.
  `sortItems sub` := First.orderOf sub.
  `runs_in_items`: at each of the three sorts every run of every name of forms of the table lies in
    sortItems. `items_tight`: and every entry of sortItems is such a run: nothing is asked idly.
    `runs_in_other`: THE NEGATIVE LINE: against another sort's list the first test fails at all
    three sorts.
  `hruns_of_sort`: **the field hruns, in its own text but for 𝔇.runs unfolded (runsAt links)**:
    (hs : links[m]? = some sub) : for all kk, r: Item.forms m kk r ∈ formsOf sub m → every p ∈
    runsAt links m kk r lies in sortItems sub.
  `hit_layers`, `hit_attention`, `hit_head`: **hit**, against the three payers' own lists (copied
    out of their files).
  `items_is_order`: (hL : SegAt m sub L) : sortItems sub = L.order.

Limits. CLOSED FACTS ON THE TABLE's NAMES. The premise hin of the same payers (formsIn at every
entry of items, ON STATES) is not touched: at this term it is asked at all entries of the order.
Nothing on soundness.

-/
import Johnson.Desc.Sound.BordersForms
import Johnson.Desc.First.Link.Law.LinkJoinPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (ModelPart Item formsOf runsOf orderOf)
open VerifiableInference.Desc.Sound (runsAt)

/-- **THE TERM FOR items**: the sort's own order of claims. -/
def sortItems (sub : ModelPart) : List (ℕ × String) := orderOf sub

/-- The names of forms of the table at a sort, as (piece, run). -/
def formNames (sub : ModelPart) : List (ℕ × String) :=
  (formsOf sub 0).filterMap fun i => match i with
    | .forms _ k r => some (k, r)
    | _ => none

/-- Every run of every name of forms at the sort a lies in the list of the sort b. -/
def runsInB (a b : ModelPart) : Bool :=
  (formNames a).all fun x => (runsOf a x.1 x.2).all (sortItems b).contains

theorem runs_in_items : ∀ sub : ModelPart, runsInB sub sub = true := fun sub => by
  cases sub <;> decide

/-- Nothing more: every entry of the list is a run of a name of forms. -/
theorem items_tight : ∀ sub : ModelPart,
    ((sortItems sub).all ((formNames sub).flatMap fun x => runsOf sub x.1 x.2).contains) =
      true := fun sub => by
  cases sub <;> decide

/-- The negative line: against another sort's list the test fails. -/
theorem runs_in_other : runsInB .layers .attention = false ∧ runsInB .attention .head = false ∧
    runsInB .head .layers = false := by decide

/-- The names do not depend on the segment's number. -/
theorem formNames_at (sub : ModelPart) (m : ℕ) :
    ((formsOf sub m).filterMap fun i => match i with
      | .forms _ k r => some (k, r)
      | _ => none) = formNames sub := by
  cases sub <;> rfl

/-- A name of forms at segment m is one at segment 0. -/
theorem formName_of_mem (sub : ModelPart) (m kk : ℕ) (r : String)
    (h : Item.forms m kk r ∈ formsOf sub m) : (kk, r) ∈ formNames sub := by
  rw [← formNames_at sub m]
  exact List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- **hruns.** -/
theorem hruns_of_sort (links : List ModelPart) (m : ℕ) (sub : ModelPart) (hs : links[m]? = some sub) :
    ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ runsAt links m kk r, p ∈ sortItems sub := by
  intro kk r h p hp
  unfold runsAt at hp
  rw [hs] at hp
  have h1 := List.all_eq_true.1 (runs_in_items sub) _ (formName_of_mem sub m kk r h)
  have h2 := List.all_eq_true.1 h1 p hp
  exact List.contains_iff_mem.1 h2

/-- **hit, at a layers' link.** -/
theorem hit_layers : ∀ e ∈ sortItems .layers, e ∈ [(1, "objects"), (1, "guests"), (2, "front"),
    (2, "back"), (4, "K8.equations"), (6, "objects"), (6, "guests")] := by decide

/-- **hit, at an attention link.** -/
theorem hit_attention : ∀ e ∈ sortItems .attention, e ∈ [(1, "objects"), (1, "guests"),
    (1, "planes"), (2, "join"), (2, "first"), (2, "keys"), (2, "second"), (4, "K8.equations"),
    (6, "objects"), (6, "guests")] := by decide

/-- **hit, at the head's link.** -/
theorem hit_head : ∀ e ∈ sortItems .head, e ∈ [(2, "objects"), (2, "guests"), (3, "norm"), (3,
    "join"), (3, "policy"), (2, "planes"), (7, "objects"), (7, "guests"), (5, "K8.equations"), (3,
    "logits"), (8, "the merge")] := by decide

/-- It is the link's own order. -/
theorem items_is_order {T Cl : Type} {m : ℕ} {sub : ModelPart} {L : Link T Cl} (hL : SegAt m sub L) :
    sortItems sub = L.order := (order_at hL).1.symm

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.runs_in_items
#print axioms VerifiableInference.Desc.LinkJoin.items_tight
#print axioms VerifiableInference.Desc.LinkJoin.runs_in_other
#print axioms VerifiableInference.Desc.LinkJoin.formNames_at
#print axioms VerifiableInference.Desc.LinkJoin.formName_of_mem
#print axioms VerifiableInference.Desc.LinkJoin.hruns_of_sort
#print axioms VerifiableInference.Desc.LinkJoin.hit_layers
#print axioms VerifiableInference.Desc.LinkJoin.hit_attention
#print axioms VerifiableInference.Desc.LinkJoin.hit_head
#print axioms VerifiableInference.Desc.LinkJoin.items_is_order
