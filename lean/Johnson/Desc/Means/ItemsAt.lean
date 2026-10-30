-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/ItemsAt.lean: the claims on rows that a table of a chain's borders names, as two
terms, with the laws that such a table asks of them.

A table of borders names a claim "the rows of this class on this segment's group hold". Two terms
say it. openItem: the open rows at the listed places of a group hold. sampleItem: the sample rows of
the listed oracle messages hold. Both speak of words; wordsFrom makes the words out of a witness
that has one message for each number: the table says which number each oracle message holds
(numberAt), and a reading of a message gives its two tables (tab).

The laws. Which part of the witness a term reads (openItem_reads, sampleItem_reads). A term rides
past a step that leaves its rows (openItem_rides, sampleItem_rides). What the beginning of a
proximity test takes in holds just if all open rows of the group and all sample rows of its members
hold (runRows_iff_items): this is what the block that closes the items spends.

Main definitions: openItem, sampleItem, wordsFrom.
Main theorems: openItem_reads, sampleItem_reads, openItem_rides, sampleItem_rides,
runRows_iff_items.

What is not claimed. Which places and which oracle messages a class has: numbers of the plan and of
the blocks' texts. That numberAt and tab are the code's. Nothing on soundness.

-/
import Johnson.Desc.Means.ItemsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S S' : Statement} {G : Group}

/-- The open rows at the listed places of the group g hold of the words. -/
def openItem (S : Statement) (g : Nat) (places : List Nat) (m : Words K) : Prop :=
  ∀ i ∈ places, OpenSays ρ S g i m

/-- The sample rows of the listed oracle messages hold of the words. -/
def sampleItem (S : Statement) (os : List Nat) (m : Words K) : Prop :=
  ∀ o ∈ os, SampleSays ρ S o m

/-- The words that a witness gives. numberAt: which of the witness's messages the oracle message o
holds, if any. tab: a message's two tables. msg: the witness's messages by number. -/
def wordsFrom {M : Type} (numberAt : Nat → Option Nat) (tab : M → Part → Nat → K)
    (msg : Nat → M) : Words K :=
  fun o part i =>
    match numberAt o with
    | some k => tab (msg k) part i
    | none => 0

/-- Two witnesses that have the same message at the number of o give the same words at o. -/
theorem wordsFrom_agree {M : Type} (numberAt : Nat → Option Nat) (tab : M → Part → Nat → K)
    {msg msg' : Nat → M} {o : Nat} (h : ∀ k, numberAt o = some k → msg k = msg' k) (part : Part)
    (i : Nat) : wordsFrom numberAt tab msg o part i = wordsFrom numberAt tab msg' o part i := by
  unfold wordsFrom
  cases hk : numberAt o with
  | none => rfl
  | some k =>
    show tab (msg k) part i = tab (msg' k) part i
    rw [h k hk]

/-- **An open rows' term reads the messages of the group's members alone.** Where the group is not
there the term is true of all words. -/
theorem openItem_reads {M : Type} (hI : InOrder S) (g : Nat) (places : List Nat)
    (numberAt : Nat → Option Nat) (tab : M → Part → Nat → K) {msg msg' : Nat → M}
    (h : ∀ G : Group, S.groups[g]? = some G →
      ∀ o ∈ G.members.toList, ∀ k, numberAt o = some k → msg k = msg' k) :
    openItem ρ S g places (wordsFrom numberAt tab msg) ↔
      openItem ρ S g places (wordsFrom numberAt tab msg') := by
  cases hG : S.groups[g]? with
  | none =>
    have no : ∀ i r, ¬ RowAt S g i r := by
      intro i r hr
      obtain ⟨G, hG', _⟩ := rowAt_iff.1 hr
      rw [hG] at hG'
      cases hG'
    exact ⟨fun _ i _ r hr => absurd hr (no i r), fun _ i _ r hr => absurd hr (no i r)⟩
  | some G =>
    have key := fun i => openSays_agree ρ hI hG i
      (m := wordsFrom numberAt tab msg) (m' := wordsFrom numberAt tab msg')
      fun o ho part j => wordsFrom_agree numberAt tab (h G hG o ho) part j
    exact ⟨fun c i hi => (key i).1 (c i hi), fun c i hi => (key i).2 (c i hi)⟩

/-- **A sample rows' term reads the listed messages alone.** -/
theorem sampleItem_reads {M : Type} (hI : InOrder S) (os : List Nat)
    (numberAt : Nat → Option Nat) (tab : M → Part → Nat → K) {msg msg' : Nat → M}
    (h : ∀ o ∈ os, ∀ k, numberAt o = some k → msg k = msg' k) :
    sampleItem ρ S os (wordsFrom numberAt tab msg) ↔
      sampleItem ρ S os (wordsFrom numberAt tab msg') := by
  have key := fun o (ho : o ∈ os) => sampleSays_agree ρ hI o
    (m := wordsFrom numberAt tab msg) (m' := wordsFrom numberAt tab msg')
    fun part j => wordsFrom_agree numberAt tab (h o ho) part j
  exact ⟨fun c o ho => (key o ho).1 (c o ho), fun c o ho => (key o ho).2 (c o ho)⟩

/-- An open rows' term rides past a step that leaves the group's open rows. -/
theorem openItem_rides (hI : InOrder S) (hE : Extends S S') {g : Nat}
    (hr : rowsOf S' g = rowsOf S g) (places : List Nat) (m : Words K) :
    openItem ρ S' g places m ↔ openItem ρ S g places m :=
  ⟨fun c i hi => (openSays_rides ρ hI hE hr i m).1 (c i hi),
    fun c i hi => (openSays_rides ρ hI hE hr i m).2 (c i hi)⟩

/-- A sample rows' term rides past a step that leaves the listed messages' sample rows. -/
theorem sampleItem_rides (hI : InOrder S) (hE : Extends S S') (os : List Nat)
    (hs : ∀ o ∈ os, (S'.oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map (fun x : Oracle => x.sampleRows)) (m : Words K) :
    sampleItem ρ S' os m ↔ sampleItem ρ S os m :=
  ⟨fun c o ho => (sampleSays_rides ρ hI hE (hs o ho) m).1 (c o ho),
    fun c o ho => (sampleSays_rides ρ hI hE (hs o ho) m).2 (c o ho)⟩

/-- **What a proximity test takes in holds just if the group's items hold**: all its open rows, and
all sample rows of its members. -/
theorem runRows_iff_items (hK : OpenKinds S) (g : Nat) (hG : S.groups[g]? = some G)
    (m : Words K) :
    AllSay ρ S (Slice.runRows S G).toList m ↔
      (∀ i, OpenSays ρ S g i m) ∧ sampleItem ρ S G.members.toList m := by
  constructor
  · intro h
    refine ⟨fun i r hr => ?_, fun o ho x hx r hr => h r (samples_taken S G ho hx r hr)⟩
    obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
    rw [hG] at hG'
    obtain rfl := Option.some.inj hG'
    exact h r (open_taken hK g G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi)))
  · rintro ⟨h1, h2⟩ r hr
    have open_ : ∀ r ∈ G.rows.toList, Says ρ S r m := by
      intro r hr'
      obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hr')
      exact h1 i r (rowAt_iff.2 ⟨G, hG, by rw [Array.getElem?_eq_getElem hi, e]⟩)
    unfold Slice.runRows at hr
    simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
    rcases hr with (c | c) | c
    · exact open_ r c.1
    · rw [← Array.foldl_toList] at c
      rcases mem_samples S r _ _ c with c' | ⟨o, ho, x, hx, hr'⟩
      · simp at c'
      · exact h2 o ho x hx r hr'
    · exact open_ r c.1

end OnBytes.Means
