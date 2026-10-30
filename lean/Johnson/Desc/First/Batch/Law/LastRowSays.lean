-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/LastRowSays.lean
(kind K9's soundness lemma; for the table of joints): THEOREM: THE ONE EQUATION's PIECE's RELATION
BEHIND (LastRowAt, Law/Cores.lean) FROM THE LIBRARY's OWN TWO SENTENCES: "the group's last row says
its claim of the words" (LastSays, Law/CoresTable.lean) and "the statement is in order"
(Johnson/Desc/Means/Order.lean: InOrder).
  fit_of_inOrder   hfit of lastRow_of_says: in a statement in order an open row has passed the tests
                of the adding (InOrder.rows): so it has no coefficient on a table that is not there
                (RowIn.absent) nor on a later oracle message (RowIn.off).
  lastRow_of_inOrder   **LastSays, InOrder of the part's statement and "at most N oracle messages"
                give LastRowAt.**
  PlaceSays, lastSays_of_place   the same sentence BY THE PLAN's NUMBERS (group number g, place i in
                its list), as a table's filling reads it: it gives LastSays where the link's check
                names group g and that list has i + 1 rows.
  st_part, placeSays_of_run   and PlaceSays at the real record from "all rows of a run of places in
                group g's list say their claims": the form to which the closing's files' layer
                for the letter "row" unfolds at a class in the list.
(Law/RowSays.lean has the tie of rowSum to the library's value and Says for one row and
for all rows of a group: rowSum_value, holds_says, groupHolds_says, under the same two conditions
as hypotheses. This file is about the group's LAST row and pays the two conditions from InOrder.)
Not claimed: InOrder or any of these numbers at any state.

-/
import Johnson.Desc.First.Batch.Law.CoresTable
import Johnson.Desc.Means.Order
import Johnson.Desc.Means.Absent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens)

variable {T K : Type} [CommRing K]

/-- In a statement in order the group's last row fits. -/
theorem fit_of_inOrder (X : Lens T) (ρ : Reading K) (N : Nat) (s : T)
    (h : ∀ a, X.get? s = some a → OnBytes.Means.InOrder a.d.st ∧ a.d.st.oracles.size ≤ N) :
    ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
      ∀ row, G.rows.back? = some row → a.d.st.oracles.size ≤ N ∧
        (∀ o part, a.d.st.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0) ∧
        ∀ o, a.d.st.oracles.size ≤ o → ∀ part J, ρ.val (row.coefficient o part J) = 0 := by
  intro a ha G hG row hr
  obtain ⟨hO, hN⟩ := h a ha
  have hin : OnBytes.Means.RowIn a.d.st G row := hO.rows _ G hG row (by
    rw [Array.back?_eq_getElem?] at hr
    exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hr))
  exact ⟨hN, fun o part hh J => hin.absent ρ hh J, fun o ho part J => hin.off ρ o ho part J⟩

/-- **From the library's two sentences to the law's relation behind the one equation.** -/
theorem lastRow_of_inOrder (X : Lens T) (ρ : Reading K) (N : Nat) (s : T)
    (m : Nat → OnBytes.Part → Nat → K) (hs : LastSays X ρ s m)
    (h : ∀ a, X.get? s = some a → OnBytes.Means.InOrder a.d.st ∧ a.d.st.oracles.size ≤ N) :
    LastRowAt X ρ N s m :=
  lastRow_of_says X ρ N s m hs (fit_of_inOrder X ρ N s h)

/-- The row at place i of group number g's list says its claim of the words: g and i: numbers of a
plan. -/
def PlaceSays (X : Lens T) (ρ : Reading K) (g i : Nat) (s : T)
    (m : Nat → OnBytes.Part → Nat → K) : Prop :=
  ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[g]? = some G →
    ∀ row, G.rows[i]? = some row → OnBytes.Means.Says ρ a.d.st row m

/-- **From the plan's numbers to the link's own check and the list's end**: where the link's check
names group g and that group's list has i + 1 rows. -/
theorem lastSays_of_place (X : Lens T) (ρ : Reading K) (g i : Nat) (s : T)
    (m : Nat → OnBytes.Part → Nat → K) (h : PlaceSays X ρ g i s m)
    (hg : ∀ a, X.get? s = some a → a.L.check.group = g)
    (hn : ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[g]? = some G → G.rows.size = i + 1) :
    LastSays X ρ s m := fun a ha G hG row hr => by
  rw [hg a ha] at hG
  rw [Array.back?_eq_getElem?, hn a ha G hG] at hr
  exact h a ha G hG row hr

/-- K9's part holds the record's own statement. -/
theorem st_part (s : VerifiableInference.Desc.First.S) (a : K9.Part)
    (h : VerifiableInference.Desc.K9.atS.get? s = some a) : a.d.st = s.st := by
  simp only [VerifiableInference.Desc.K9.atS] at h
  obtain ⟨L, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [← Option.some.inj h]

/-- **From "all rows of a run of places in group g's list say their claims" to the row at the run's
first place**: the left side is, to the letter, what the closing's files' layer for the table's
letter "row" unfolds to at a class that lies in the list (its classRows: the rows at the places
i + j, j < n, of the record's group number g). -/
theorem placeSays_of_run (ρ : Reading K) (g i n : Nat) (hn : 0 < n)
    (s : VerifiableInference.Desc.First.S) (m : Nat → OnBytes.Part → Nat → K)
    (h : OnBytes.Means.AllSay ρ s.st
      (match s.st.groups[g]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[i + j]?) m) :
    PlaceSays VerifiableInference.Desc.K9.atS ρ g i s m := by
  intro a ha G hG row hr
  rw [st_part s a ha] at hG ⊢
  rw [hG] at h
  exact h row (List.mem_filterMap.2 ⟨0, List.mem_range.2 hn, hr⟩)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.placeSays_of_run
#print axioms VerifiableInference.Desc.K9L.lastSays_of_place
#print axioms VerifiableInference.Desc.K9L.fit_of_inOrder
#print axioms VerifiableInference.Desc.K9L.lastRow_of_inOrder
