-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/ItemsTab.lean: the words of a statement's oracle messages, read off tables that
are given by mask or main row, row and place.

A witness may give the table of an oracle message as a function of three things: whether the row is
a mask row, the row's number, and the place. wordsOn lays such tables out as words: the entry with
the index i of a table with 2^(row bits) rows is the entry of row i mod 2^(row bits) at place i /
2^(row bits), and 0 on the rows beyond the real ones.

This file shows: such words are 0 beyond the real rows (padded_wordsOn); they read a message's table
at its real rows alone (wordsOn_agree); they do not turn at a message that is there when the
statement goes on to a later one (wordsOn_extends). So the two terms of
Johnson/Desc/Means/ItemsAt.lean, with the words made anew at each statement, ride as one proposition
(openItem_rides_on, sampleItem_rides_on), and read the tables of the group's members, or of the
listed messages, alone (openItem_reads_on, sampleItem_reads_on).

Main definitions: wordsOn.
Main theorems: padded_wordsOn, wordsOn_agree, wordsOn_extends, openItem_reads_on,
sampleItem_reads_on, openItem_rides_on, sampleItem_rides_on.

What is not claimed. How a table is made of a witness, or that any of its entries is fixed by the
statement. The places are not cut at the code's length: an index below the table's size has a place
below 2^(place bits). Nothing on soundness.

-/
import Johnson.Desc.Means.ItemsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S S' : Statement}

/-- The words that tables give at a statement. T o: the table of the oracle message o, by mask row
or main row (true: mask), row and place. -/
def wordsOn (S : Statement) (T : Nat → Bool → Nat → Nat → K) : Words K :=
  fun o part i =>
    if i % 2 ^ S.rowBits o part < realRows S o part then
      T o (part == .mask) (i % 2 ^ S.rowBits o part) (i / 2 ^ S.rowBits o part)
    else 0

/-- Such words are 0 on the rows beyond the real ones. -/
theorem padded_wordsOn (S : Statement) (T : Nat → Bool → Nat → Nat → K) :
    Padded S (wordsOn S T) := by
  intro o part i h
  unfold wordsOn
  rw [if_neg (Nat.not_lt.2 h)]

/-- They read a message's table at its real rows alone. -/
theorem wordsOn_agree (S : Statement) {T T' : Nat → Bool → Nat → Nat → K} {o : Nat}
    (h : ∀ part row place, row < realRows S o part →
      T o (part == .mask) row place = T' o (part == .mask) row place) (part : Part) (i : Nat) :
    wordsOn S T o part i = wordsOn S T' o part i := by
  unfold wordsOn
  split
  · next c => exact h part _ _ c
  · rfl

theorem Extends.realRows (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : Part) :
    realRows S' o part = realRows S o part := by
  obtain ⟨x', hx', e⟩ := h.shape o _ (Array.getElem?_eq_getElem ho)
  unfold Means.realRows
  rw [hx', Array.getElem?_eq_getElem ho]
  dsimp only
  rw [e]

/-- They do not turn at a message that is there when the statement goes on. -/
theorem wordsOn_extends (h : Extends S S') (T : Nat → Bool → Nat → Nat → K) {o : Nat}
    (ho : o < S.oracles.size) (part : Part) (i : Nat) :
    wordsOn S' T o part i = wordsOn S T o part i := by
  unfold wordsOn
  rw [h.rowBits ho part, h.realRows ho part]

/-- A member of a group of a statement in order is there. -/
theorem member_lt (hI : InOrder S) {g : Nat} {G : Group} (hG : S.groups[g]? = some G) {o : Nat}
    (ho : o ∈ G.members.toList) : o < S.oracles.size :=
  (hI.groups g G hG).there o ho

/-- **An open rows' term reads the tables of the group's members alone**, at their real rows. -/
theorem openItem_reads_on (hI : InOrder S) (g : Nat) (places : List Nat)
    {T T' : Nat → Bool → Nat → Nat → K}
    (h : ∀ G : Group, S.groups[g]? = some G → ∀ o ∈ G.members.toList, ∀ part row place,
      row < realRows S o part → T o (part == .mask) row place = T' o (part == .mask) row place) :
    openItem ρ S g places (wordsOn S T) ↔ openItem ρ S g places (wordsOn S T') := by
  cases hG : S.groups[g]? with
  | none =>
    have no : ∀ i r, ¬ RowAt S g i r := by
      intro i r hr
      obtain ⟨G, hG', _⟩ := rowAt_iff.1 hr
      rw [hG] at hG'
      cases hG'
    exact ⟨fun _ i _ r hr => absurd hr (no i r), fun _ i _ r hr => absurd hr (no i r)⟩
  | some G =>
    have key := fun i => openSays_agree ρ hI hG i (m := wordsOn S T) (m' := wordsOn S T')
      fun o ho part j => wordsOn_agree S (h G hG o ho) part j
    exact ⟨fun c i hi => (key i).1 (c i hi), fun c i hi => (key i).2 (c i hi)⟩

/-- **A sample rows' term reads the tables of the listed messages alone**, at their real rows. -/
theorem sampleItem_reads_on (hI : InOrder S) (os : List Nat) {T T' : Nat → Bool → Nat → Nat → K}
    (h : ∀ o ∈ os, ∀ part row place, row < realRows S o part →
      T o (part == .mask) row place = T' o (part == .mask) row place) :
    sampleItem ρ S os (wordsOn S T) ↔ sampleItem ρ S os (wordsOn S T') := by
  have key := fun o (ho : o ∈ os) => sampleSays_agree ρ hI o (m := wordsOn S T)
    (m' := wordsOn S T') fun part j => wordsOn_agree S (h o ho) part j
  exact ⟨fun c o ho => (key o ho).1 (c o ho), fun c o ho => (key o ho).2 (c o ho)⟩

/-- **An open rows' term rides, the words made anew at the later statement.** -/
theorem openItem_rides_on (hI : InOrder S) (hE : Extends S S') {g : Nat}
    (hr : rowsOf S' g = rowsOf S g) (places : List Nat) (T : Nat → Bool → Nat → Nat → K) :
    openItem ρ S' g places (wordsOn S' T) ↔ openItem ρ S g places (wordsOn S T) := by
  rw [openItem_rides ρ hI hE hr places (wordsOn S' T)]
  cases hG : S.groups[g]? with
  | none =>
    have no : ∀ i r, ¬ RowAt S g i r := by
      intro i r hr'
      obtain ⟨G, hG', _⟩ := rowAt_iff.1 hr'
      rw [hG] at hG'
      cases hG'
    exact ⟨fun _ i _ r hr' => absurd hr' (no i r), fun _ i _ r hr' => absurd hr' (no i r)⟩
  | some G =>
    have key := fun i => openSays_agree ρ hI hG i (m := wordsOn S' T) (m' := wordsOn S T)
      fun o ho part j => wordsOn_extends hE T (member_lt hI hG ho) part j
    exact ⟨fun c i hi => (key i).1 (c i hi), fun c i hi => (key i).2 (c i hi)⟩

/-- **A sample rows' term rides, the words made anew at the later statement**: for messages that are
there and keep their sample rows. -/
theorem sampleItem_rides_on (hI : InOrder S) (hE : Extends S S') (os : List Nat)
    (ht : ∀ o ∈ os, o < S.oracles.size)
    (hs : ∀ o ∈ os, (S'.oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map (fun x : Oracle => x.sampleRows)) (T : Nat → Bool → Nat → Nat → K) :
    sampleItem ρ S' os (wordsOn S' T) ↔ sampleItem ρ S os (wordsOn S T) := by
  rw [sampleItem_rides ρ hI hE os hs (wordsOn S' T)]
  have key := fun o (ho : o ∈ os) => sampleSays_agree ρ hI o (m := wordsOn S' T)
    (m' := wordsOn S T) fun part j => wordsOn_extends hE T (ht o ho) part j
  exact ⟨fun c o ho => (key o ho).1 (c o ho), fun c o ho => (key o ho).2 (c o ho)⟩

end OnBytes.Means
