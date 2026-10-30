-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BordersKeep.lean: WHAT OF THE TABLE OF JOINTS' PROMISE A ROW LEAVES BY ITS FORM
ALONE. Small lemmas on lists; no Mathlib. A file BESIDE the table: it turns nothing of it.

Why. Behind every block the table's promise is owed anew (Johnson/Desc/First/Borders.lean, `onAt`).
Three of its clauses read the open set: `rowsHeld` and `membersHeld` (which classes of rows, which
pins are open) and `sampledIn` (whose samples must be held, shown, free of a collision). Most rows
close and open no class of rows and no pin. There the three clauses ask behind the block, OF ANY
RECORD, just what they ask in front: so what is left of them is that the block's text leaves what
they read of the record.

What is said. `Item.isRow`, `Item.isPin`: an item is a class of rows; a pin with a sample.
`stepOpen_filter`: a row whose ins and outs hold no item of a sort leaves the open items of that
sort, in their order. `rowsHeld_step`, `membersHeld_step`, `sampledIn_step`, `samplesHeld_step`: at
such a row the clause at the open set behind is the clause at the open set in front, at every
record.
`quietRow`: the test on a row, as a Bool.

Limits. On the OPEN SET's side alone: that the record's parts which these clauses read stay across
the block is each kind's own lemma on its text. Nothing on `shapeAt`, `inOrder`, the public items.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- The item is a class of rows. -/
def Item.isRow : Item → Bool
  | .row _ _ => true
  | _ => false

/-- The item is a pin of tenants that have a sample. -/
def Item.isPin : Item → Bool
  | .pin _ _ => true
  | .pinKept _ => true
  | .pinI => true
  | .pinV => true
  | _ => false

/-- A row closes and opens no class of rows and no such pin. -/
def quietRow (r : BlockRow) : Bool :=
  (r.ins ++ r.outs).all fun i => !i.isRow && !i.isPin

section lists
variable {β : Type}

theorem filter_ins (p : Item → Bool) (ins O : List Item) (h : ∀ i ∈ ins, p i = false) :
    (O.filter fun i => !ins.contains i).filter p = O.filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro a _
  cases hp : p a with
  | false => rfl
  | true =>
    have hn : ¬ a ∈ ins := fun hm => by rw [h a hm] at hp; cases hp
    simp [hn]

theorem filter_outs (p q : Item → Bool) (outs : List Item) (h : ∀ i ∈ outs, p i = false) :
    (outs.filter q).filter p = [] := by
  rw [List.filter_filter]
  apply List.filter_eq_nil_iff.2
  intro a ha
  simp [h a ha]

/-- A row whose ins and outs hold no item of a sort leaves the open items of that sort. -/
theorem stepOpen_filter (p : Item → Bool) (O : List Item) (r : BlockRow)
    (hi : ∀ i ∈ r.ins, p i = false) (ho : ∀ i ∈ r.outs, p i = false) :
    (stepOpen O r).filter p = O.filter p := by
  unfold stepOpen
  rw [List.filter_append, filter_ins p r.ins O hi, filter_outs p _ r.outs ho, List.append_nil]

theorem filterMap_key (f : Item → Option β) (p : Item → Bool) (h : ∀ i, p i = false → f i = none)
    (O : List Item) : (O.filter p).filterMap f = O.filterMap f := by
  induction O with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a with
    | true => simp [List.filter_cons, hp, List.filterMap_cons, ih]
    | false => simp [List.filter_cons, hp, List.filterMap_cons, h a hp, ih]

theorem foldl_key (g : β → Item → β) (p : Item → Bool) (h : ∀ k i, p i = false → g k i = k)
    (O : List Item) : ∀ k, (O.filter p).foldl g k = O.foldl g k := by
  induction O with
  | nil => intro _; rfl
  | cons a l ih =>
    intro k
    cases hp : p a with
    | true => simp [List.filter_cons, hp, ih]
    | false => simp [List.filter_cons, hp, h k a hp, ih]

theorem all_key (g p : Item → Bool) (h : ∀ i, p i = false → g i = true) (O : List Item) :
    (O.filter p).all g = O.all g := by
  induction O with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a with
    | true => simp [List.filter_cons, hp, ih]
    | false => simp [List.filter_cons, hp, h a hp, ih]

theorem flatMap_key (f : Item → List β) (p : Item → Bool) (h : ∀ i, p i = false → f i = [])
    (O : List Item) : (O.filter p).flatMap f = O.flatMap f := by
  induction O with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a with
    | true => simp [List.filter_cons, hp, List.flatMap_cons, ih]
    | false => simp [List.filter_cons, hp, List.flatMap_cons, h a hp, ih]

theorem contains_key (x : Item) (p : Item → Bool) (hx : p x = true) (O : List Item) :
    (O.filter p).contains x = O.contains x := by
  simp [hx]

end lists

section
variable (N : Numbers)

theorem rowSegs_of_filter (O O' : List Item) (h : O'.filter Item.isRow = O.filter Item.isRow) :
    rowSegs O' = rowSegs O := by
  unfold rowSegs
  rw [← filterMap_key _ Item.isRow (fun i hi => by cases i <;> first | rfl | cases hi) O',
    ← filterMap_key _ Item.isRow (fun i hi => by cases i <;> first | rfl | cases hi) O, h]

theorem rowsDue_of_filter (O O' : List Item) (h : O'.filter Item.isRow = O.filter Item.isRow)
    (m : Nat) : rowsDue N O' m = rowsDue N O m := by
  unfold rowsDue
  rw [← foldl_key _ Item.isRow (fun k i hi => by cases i <;> first | rfl | cases hi) O' 0,
    ← foldl_key _ Item.isRow (fun k i hi => by cases i <;> first | rfl | cases hi) O 0, h]

theorem all_of_filter (g : Item → Bool) (hg : ∀ i, i.isRow = false → g i = true)
    (O O' : List Item) (h : O'.filter Item.isRow = O.filter Item.isRow) : O'.all g = O.all g := by
  rw [← all_key g Item.isRow hg O', ← all_key g Item.isRow hg O, h]

/-- `rowsHeld` reads of the open set its classes of rows alone. -/
theorem rowsHeld_of_filter (O O' : List Item) (h : O'.filter Item.isRow = O.filter Item.isRow)
    (s : S) : rowsHeld N O' s = rowsHeld N O s := by
  unfold rowsHeld
  rw [rowSegs_of_filter O O' h]
  congr 1
  funext m
  rw [rowsDue_of_filter N O O' h m]
  cases s.st.groups[N.groupAt m]? with
  | none => rfl
  | some G =>
    dsimp only
    rw [all_of_filter _ (fun i hi => by cases i <;> first | rfl | cases hi) O O' h]

/-- `membersHeld` reads of the open set its classes of rows and its pins alone. -/
theorem membersHeld_of_filter (O O' : List Item)
    (h : O'.filter Item.isRow = O.filter Item.isRow)
    (hp : O'.filter Item.isPin = O.filter Item.isPin) (s : S) :
    membersHeld N O' s = membersHeld N O s := by
  have hc : ∀ m t, O'.contains (.pin m t) = O.contains (.pin m t) := by
    intro m t
    rw [← contains_key (.pin m t) Item.isPin rfl O', ← contains_key (.pin m t) Item.isPin rfl O, hp]
  unfold membersHeld
  rw [rowSegs_of_filter O O' h]
  simp only [hc]

/-- `sampledIn` reads of the open set its pins alone. -/
theorem sampledIn_of_filter (O O' : List Item) (hp : O'.filter Item.isPin = O.filter Item.isPin) :
    sampledIn N O' = sampledIn N O := by
  unfold sampledIn
  rw [← flatMap_key _ Item.isPin (fun i hi => by cases i <;> first | rfl | cases hi) O',
    ← flatMap_key _ Item.isPin (fun i hi => by cases i <;> first | rfl | cases hi) O, hp]

theorem quietRow_isRow {r : BlockRow} (h : quietRow r = true) :
    (∀ i ∈ r.ins, i.isRow = false) ∧ (∀ i ∈ r.outs, i.isRow = false) := by
  unfold quietRow at h
  have h' := List.all_eq_true.1 h
  constructor <;> intro i hi
  · have := h' i (List.mem_append_left _ hi)
    cases e : i.isRow <;> simp_all
  · have := h' i (List.mem_append_right _ hi)
    cases e : i.isRow <;> simp_all

theorem quietRow_isPin {r : BlockRow} (h : quietRow r = true) :
    (∀ i ∈ r.ins, i.isPin = false) ∧ (∀ i ∈ r.outs, i.isPin = false) := by
  unfold quietRow at h
  have h' := List.all_eq_true.1 h
  constructor <;> intro i hi
  · have := h' i (List.mem_append_left _ hi)
    cases e : i.isPin <;> simp_all
  · have := h' i (List.mem_append_right _ hi)
    cases e : i.isPin <;> simp_all

/-- **At a row that closes and opens no class of rows and no pin `rowsHeld` asks behind the block
what it asks in front, of every record.** -/
theorem rowsHeld_step (O : List Item) (r : BlockRow) (h : quietRow r = true) (s : S) :
    rowsHeld N (stepOpen O r) s = rowsHeld N O s :=
  rowsHeld_of_filter N O _
    (stepOpen_filter _ O r (quietRow_isRow h).1 (quietRow_isRow h).2) s

/-- The like for `membersHeld`. -/
theorem membersHeld_step (O : List Item) (r : BlockRow) (h : quietRow r = true) (s : S) :
    membersHeld N (stepOpen O r) s = membersHeld N O s :=
  membersHeld_of_filter N O _
    (stepOpen_filter _ O r (quietRow_isRow h).1 (quietRow_isRow h).2)
    (stepOpen_filter _ O r (quietRow_isPin h).1 (quietRow_isPin h).2) s

/-- The like for the tenants whose samples the promise speaks of. -/
theorem sampledIn_step (O : List Item) (r : BlockRow) (h : quietRow r = true) :
    sampledIn N (stepOpen O r) = sampledIn N O :=
  sampledIn_of_filter N O _ (stepOpen_filter _ O r (quietRow_isPin h).1 (quietRow_isPin h).2)

/-- And so for "the samples are held". -/
theorem samplesHeld_step {P W : Type} (Mg : Meaning P W) (O : List Item) (r : BlockRow)
    (h : quietRow r = true) (a : P × S) :
    samplesHeld N Mg (stepOpen O r) a = samplesHeld N Mg O a := by
  unfold samplesHeld
  rw [sampledIn_step N O r h]

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.stepOpen_filter
#print axioms VerifiableInference.Desc.First.rowsHeld_step
#print axioms VerifiableInference.Desc.First.membersHeld_step
#print axioms VerifiableInference.Desc.First.sampledIn_step
#print axioms VerifiableInference.Desc.First.samplesHeld_step
