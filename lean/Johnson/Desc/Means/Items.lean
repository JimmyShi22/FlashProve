-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Items.lean: what a statement still claims, row by row, so that each claim can be
named at a border of a chain and stays one proposition while it rides past other blocks.

An open row is named by its group and its place among the group's open rows (RowAt). The adding of a
row puts it at the end, and no effect shown here but the beginning of the group's test takes an open
row away or moves it: so a row's place does not turn while it lies open (rowsOf_withRow and the
lemmas beside it). OpenSays says that the row at a place, if there is one, holds of the words;
SampleSays that a message's sample rows hold. Claims (Johnson/Desc/Means/Claims.lean) is all of
these together (claims_iff_items). An item rides: in a later statement with the same open rows on
the group, or the same sample rows on the message, it says what it said (openSays_rides,
sampleSays_rides).

Main definitions: rowsOf, RowAt, OpenSays, SampleSays.
Main theorems: claims_iff_items, rowsOf_withRow, rowsOf_withGroup, rowsOf_joined, rowsOf_sameGroups,
rowAt_withRow, openSays_rides, sampleSays_rides, openSays_new.

What is not claimed. Which places a block's rows get: that is a number of the block's own text.
Nothing on the beginning of a test, which empties the group's open rows. Nothing on soundness.

-/
import Johnson.Desc.Means.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {S S' : Statement}

/-- The open rows of the group number g, if the group is there. -/
def rowsOf (S : Statement) (g : Nat) : Option (Array Row) := (S.groups[g]?).map (·.rows)

/-- The row r lies open on the group number g, at the place i. -/
def RowAt (S : Statement) (g i : Nat) (r : Row) : Prop :=
  ∃ R : Array Row, rowsOf S g = some R ∧ R[i]? = some r

theorem rowAt_iff {g i : Nat} {r : Row} :
    RowAt S g i r ↔ ∃ G : Group, S.groups[g]? = some G ∧ G.rows[i]? = some r := by
  unfold RowAt rowsOf
  constructor
  · rintro ⟨R, h, hi⟩
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨G, hG, hi⟩
  · rintro ⟨G, hG, hi⟩
    exact ⟨G.rows, by rw [hG]; rfl, hi⟩

/-! ## A row's place does not turn -/

theorem rowsOf_sameGroups (hg : S'.groups = S.groups) (g : Nat) : rowsOf S' g = rowsOf S g := by
  unfold rowsOf
  rw [hg]

/-- A change of one group that leaves its open rows. -/
theorem rowsOf_oneGroup (g₀ : Nat) (f : Group → Group) (hg : S'.groups = S.groups.modify g₀ f)
    (hf : ∀ G, (f G).rows = G.rows) (g : Nat) : rowsOf S' g = rowsOf S g := by
  unfold rowsOf
  rw [hg, Array.getElem?_modify]
  split
  · cases S.groups[g]? with
    | none => rfl
    | some G => exact congrArg some (hf G)
  · rfl

theorem rowsOf_joined (g₀ o : Nat) (k : Bool) (G : Group) (g : Nat) :
    rowsOf (Slice.withMessageInGroup S g₀ o k G) g = rowsOf S g :=
  rowsOf_oneGroup g₀ (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k }) rfl
    (fun _ => rfl) g

/-- A new group turns no group that was there. -/
theorem rowsOf_withGroup (a b : Nat) {g : Nat} (hg : g < S.groups.size) :
    rowsOf (Slice.withGroup S a b) g = rowsOf S g := by
  unfold rowsOf
  show ((S.groups.push { code := a, maskCode := b })[g]?).map _ = _
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hg)]

/-- **The adding puts the row at the end** of its group's open rows, and leaves the other groups. -/
theorem rowsOf_withRow (g₀ : Nat) (row : Row) (g : Nat) :
    rowsOf (Slice.withRow S g₀ row) g =
      if g₀ = g then (rowsOf S g).map (·.push row) else rowsOf S g := by
  unfold rowsOf
  show ((S.groups.modify g₀ fun G => { G with rows := G.rows.push row })[g]?).map _ = _
  rw [Array.getElem?_modify]
  split
  · cases S.groups[g]? with
    | none => rfl
    | some G => rfl
  · rfl

/-- Behind the adding a row lies where it lay; the new row lies at the end. -/
theorem rowAt_withRow (g₀ : Nat) (row : Row) (g i : Nat) (r : Row) :
    RowAt (Slice.withRow S g₀ row) g i r ↔
      RowAt S g i r ∨ (g₀ = g ∧ r = row ∧ ∃ R, rowsOf S g = some R ∧ i = R.size) := by
  unfold RowAt
  rw [rowsOf_withRow]
  by_cases c : g₀ = g
  · rw [if_pos c]
    constructor
    · rintro ⟨R', h, hi⟩
      obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [Array.getElem?_push] at hi
      by_cases e : i = R.size
      · rw [if_pos e] at hi
        exact Or.inr ⟨c, (Option.some.inj hi).symm, R, hR, e⟩
      · rw [if_neg e] at hi
        exact Or.inl ⟨R, hR, hi⟩
    · rintro (⟨R, hR, hi⟩ | ⟨_, rfl, R, hR, rfl⟩)
      · refine ⟨R.push row, by rw [hR]; rfl, ?_⟩
        have hlt : i < R.size := by
          by_contra e
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt e)] at hi
          cases hi
        rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
        exact hi
      · exact ⟨R.push r, by rw [hR]; rfl, by rw [Array.getElem?_push, if_pos rfl]⟩
  · rw [if_neg c]
    constructor
    · exact Or.inl
    · rintro (h | ⟨e, _⟩)
      · exact h
      · exact absurd e c

/-! ## The items -/

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The open row at the place i of the group g, if there is one, holds of the words. -/
def OpenSays (S : Statement) (g i : Nat) (m : Words K) : Prop :=
  ∀ r, RowAt S g i r → Says ρ S r m

/-- The sample rows of the oracle message o hold of the words. -/
def SampleSays (S : Statement) (o : Nat) (m : Words K) : Prop :=
  ∀ x : Oracle, S.oracles[o]? = some x → AllSay ρ S x.sampleRows.toList m

/-- **What a statement still claims is its items together.** -/
theorem claims_iff_items (m : Words K) :
    Claims ρ S m ↔ (∀ g i, OpenSays ρ S g i m) ∧ ∀ o, Pending S o → SampleSays ρ S o m := by
  constructor
  · intro h
    refine ⟨fun g i r hr => ?_, fun o hp x hx => h.samples o x hx hp⟩
    obtain ⟨G, hG, hi⟩ := rowAt_iff.1 hr
    exact h.rows g G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))
  · rintro ⟨h1, h2⟩
    refine ⟨fun g G hG r hr => ?_, fun o x hx hp => h2 o hp x hx⟩
    obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hr)
    exact h1 g i r (rowAt_iff.2 ⟨G, hG, by rw [Array.getElem?_eq_getElem hi, e]⟩)

/-- **An open row's item rides**: in a later statement in which the group has the same open rows it
says what it said. -/
theorem openSays_rides (hI : InOrder S) (hE : Extends S S') {g : Nat}
    (hr : rowsOf S' g = rowsOf S g) (i : Nat) (m : Words K) :
    OpenSays ρ S' g i m ↔ OpenSays ρ S g i m := by
  have key : ∀ r, RowAt S g i r → (Says ρ S' r m ↔ Says ρ S r m) := by
    intro r h
    obtain ⟨G, hG, hi⟩ := rowAt_iff.1 h
    exact says_extends ρ hE
      (hI.rows g G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))) m
  have same : ∀ r, RowAt S' g i r ↔ RowAt S g i r := by
    intro r
    unfold RowAt
    rw [hr]
  constructor
  · intro h r hr'
    exact (key r hr').1 (h r ((same r).2 hr'))
  · intro h r hr'
    exact (key r ((same r).1 hr')).2 (h r ((same r).1 hr'))

/-- **A message's sample rows' item rides**: in a later statement in which the message has the same
sample rows it says what it said. -/
theorem sampleSays_rides (hI : InOrder S) (hE : Extends S S') {o : Nat}
    (hs : (S'.oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map (fun x : Oracle => x.sampleRows)) (m : Words K) :
    SampleSays ρ S' o m ↔ SampleSays ρ S o m := by
  constructor
  · intro h x hx r hr
    rw [hx] at hs
    obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 hs
    have e' : x'.sampleRows = x.sampleRows := e
    exact (says_extends ρ hE (hI.samples o x hx r hr) m).1 (h x' hx' r (by rw [e']; exact hr))
  · intro h x' hx' r hr
    rw [hx'] at hs
    obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 hs.symm
    have e' : x.sampleRows = x'.sampleRows := e
    have hr' : r ∈ x.sampleRows.toList := by
      rw [e']
      exact hr
    exact (says_extends ρ hE (hI.samples o x hx r hr') m).2 (h x hx r hr')

/-- **The item that the adding opens**: behind the adding of a row to a group with n open rows, the
item at the place n says that the row holds. -/
theorem openSays_new (g : Nat) (G : Group) (row : Row) (hG : S.groups[g]? = some G)
    (m : Words K) :
    OpenSays ρ (Slice.withRow S g row) g G.rows.size m ↔ Says ρ S row m := by
  have hv : ∀ r, Says ρ (Slice.withRow S g row) r m ↔ Says ρ S r m := by
    intro r
    unfold Says
    rw [value_congr ρ (S := S) (S' := Slice.withRow S g row) rfl rfl]
  have hR : rowsOf S g = some G.rows := by
    unfold rowsOf
    rw [hG]
    rfl
  constructor
  · intro h
    exact (hv row).1 (h row ((rowAt_withRow g row g G.rows.size row).2
      (Or.inr ⟨rfl, rfl, G.rows, hR, rfl⟩)))
  · intro h r hr
    rcases (rowAt_withRow g row g G.rows.size r).1 hr with ⟨R, hR', hi⟩ | ⟨_, e, _⟩
    · rw [hR] at hR'
      obtain rfl := Option.some.inj hR'
      rw [Array.getElem?_eq_none (Nat.le_refl _)] at hi
      cases hi
    · rw [e]
      exact (hv row).2 h

end OnBytes.Means
