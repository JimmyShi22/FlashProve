-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/ItemsLen.lean: where every message length is a power of two, the claims on rows
read a table
inside its ranges alone: at its real rows, and at places below the code's message length.

wordsOn (Johnson/Desc/Means/ItemsTab.lean) cuts a table's rows at the real ones and does not cut its
places: an
index below the table's size has a place below 2^(place bits), and the place bits are the rounded-up
logarithm of the message length. A table that a witness gives may be fixed by the statement inside
its ranges alone. So at a length that is no power of two a row could read entries that nothing
fixes. This file shows that the test on the codes which every run makes (Codes.lengthsOk) shuts
that out.

lengths_base and lengths_mask: under that test 2^(the rounded-up logarithm of the length) is the
length, for every code in the two lists. placeBits_ell: so 2^(place bits) is the length of the
table's code, if the code's number is in its list. place_lt_ell: so an index below the table's size
has a place below the length. says_agree_in: what a row says reads the words below the tables' sizes
alone. openItem_inside and sampleItem_inside: so the two terms of Johnson/Desc/Means/ItemsAt.lean
read the tables
inside their ranges alone. wordsOn_congr: what wordsOn reads of a statement at a message is its
shape alone: the statement, and the proof but for small turns, are those of the lemma of
the same name, Johnson/Desc/Sound/WordsAt.lean, taken over.

Main definitions: ellOf, CodeThere.
Main theorems: lengths_base, lengths_mask, placeBits_ell, place_lt_ell, says_agree_in,
wordsOn_agree_inside, openItem_inside, sampleItem_inside, wordsOn_congr.

What is not claimed. That a text tests Codes.lengthsOk, or that a message's code is in its list.
Nothing on soundness.

-/
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

/-! ## The lengths -/

theorem two_pow_of_powerOfTwo {n : Nat} (h : powerOfTwo n = true) : 2 ^ ceilLog2 n = n := by
  unfold powerOfTwo at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **Under the test on the codes, 2^(the rounded-up logarithm of the length) is the length**, for
every code of main rows. -/
theorem lengths_base {c : Codes} (h : c.lengthsOk = true) {k : Nat} (hk : k < c.base.size) :
    2 ^ ceilLog2 (c.base.getD k default).ell = (c.base.getD k default).ell := by
  unfold Codes.lengthsOk at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  have e : c.base.getD k default = c.base[k] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    rfl
  rw [e]
  exact two_pow_of_powerOfTwo (h.1 _ (Array.getElem_mem hk))

/-- The like for every code of mask rows. -/
theorem lengths_mask {c : Codes} (h : c.lengthsOk = true) {k : Nat} (hk : k < c.mask.size) :
    2 ^ ceilLog2 (c.mask.getD k default).ell = (c.mask.getD k default).ell := by
  unfold Codes.lengthsOk at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  have e : c.mask.getD k default = c.mask[k] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    rfl
  rw [e]
  exact two_pow_of_powerOfTwo (h.2 _ (Array.getElem_mem hk))

variable {S S' : Statement}

/-- The message length of the code of a table; 0 for a message that is not there. -/
def ellOf (S : Statement) (o : Nat) (part : Part) : Nat :=
  match S.oracles[o]? with
  | some x =>
    match part with
    | .main => (S.codes.base.getD x.shape.code default).ell
    | .mask => (S.codes.mask.getD x.shape.maskCode default).ell
  | none => 0

/-- The number of the table's code is in its list. -/
def CodeThere (S : Statement) (o : Nat) (part : Part) : Prop :=
  ∀ x : Oracle, S.oracles[o]? = some x →
    match part with
    | .main => x.shape.code < S.codes.base.size
    | .mask => x.shape.maskCode < S.codes.mask.size

/-- **2^(place bits) is the message length of the table's code.** -/
theorem placeBits_ell (hc : S.codes.lengthsOk = true) {o : Nat} {part : Part}
    (hh : S.has o part = true) (ht : CodeThere S o part) :
    2 ^ S.placeBits o part = ellOf S o part := by
  unfold Statement.has at hh
  unfold Statement.placeBits ellOf
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at hh
    cases hh
  | some x =>
    rw [hx] at hh
    have hpos : 0 < x.shape.rows part := by simpa using hh
    have hne : (x.shape.rows part == 0) = false := by
      simp
      omega
    have hk := ht x hx
    dsimp only
    rw [hne]
    cases part with
    | main => exact lengths_base hc hk
    | mask => exact lengths_mask hc hk

/-- **An index below a table's size has a place below the message length.** -/
theorem place_lt_ell (hc : S.codes.lengthsOk = true) {o : Nat} {part : Part}
    (ht : CodeThere S o part) {i : Nat} (hi : i < tableSize S o part) :
    i / 2 ^ S.rowBits o part < ellOf S o part := by
  unfold tableSize at hi
  by_cases hh : S.has o part = true
  · rw [if_pos hh] at hi
    rw [← placeBits_ell hc hh ht]
    apply Nat.div_lt_of_lt_mul
    unfold Statement.tableBits at hi
    rw [pow_add] at hi
    exact hi
  · rw [if_neg hh] at hi
    cases hi

/-! ## What a row reads -/

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {G : Group} {row : Row}

/-- A row applied to words reads the members' words below their tables' sizes alone. -/
theorem value_agree_in (hr : RowIn S G row) {m m' : Words K}
    (h : ∀ o ∈ G.members.toList, ∀ part, ∀ i < tableSize S o part, m o part i = m' o part i) :
    value ρ S row m = value ρ S row m' := by
  unfold value onTable
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : o ∈ G.members.toList
  · congr 1 <;>
    · apply Finset.sum_congr rfl
      intro i hi
      rw [h o ho _ i (Finset.mem_range.1 hi)]
  · congr 1 <;>
    · apply Finset.sum_congr rfl
      intro i _
      rw [coefficient_off ρ hr ho, zero_mul, zero_mul]

theorem says_agree_in (hr : RowIn S G row) {m m' : Words K}
    (h : ∀ o ∈ G.members.toList, ∀ part, ∀ i < tableSize S o part, m o part i = m' o part i) :
    Says ρ S row m ↔ Says ρ S row m' := by
  unfold Says
  rw [value_agree_in ρ hr h]

/-- Two families of tables agree inside the ranges of the message o: at its real rows, at places
below its codes' message lengths. -/
def AgreeInside (S : Statement) (T T' : Nat → Bool → Nat → Nat → K) (o : Nat) : Prop :=
  ∀ part row place, row < realRows S o part → place < ellOf S o part →
    T o (part == .mask) row place = T' o (part == .mask) row place

/-- Such families give the same words at o below its tables' sizes. -/
theorem wordsOn_agree_inside (hc : S.codes.lengthsOk = true) {T T' : Nat → Bool → Nat → Nat → K}
    {o : Nat} (ht : ∀ part, CodeThere S o part) (h : AgreeInside S T T' o) (part : Part) (i : Nat)
    (hi : i < tableSize S o part) : wordsOn S T o part i = wordsOn S T' o part i := by
  unfold wordsOn
  split
  · next c => exact h part _ _ c (place_lt_ell hc (ht part) hi)
  · rfl

/-- **An open rows' term reads the members' tables inside their ranges alone.** -/
theorem openItem_inside (hI : InOrder S) (hc : S.codes.lengthsOk = true) (g : Nat)
    (places : List Nat) {T T' : Nat → Bool → Nat → Nat → K}
    (h : ∀ G : Group, S.groups[g]? = some G → ∀ o ∈ G.members.toList,
      (∀ part, CodeThere S o part) ∧ AgreeInside S T T' o) :
    openItem ρ S g places (wordsOn S T) ↔ openItem ρ S g places (wordsOn S T') := by
  have key : ∀ i r, RowAt S g i r → (Says ρ S r (wordsOn S T) ↔ Says ρ S r (wordsOn S T')) := by
    intro i r hr
    obtain ⟨G, hG, hi⟩ := rowAt_iff.1 hr
    exact says_agree_in ρ
      (hI.rows g G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi)))
      fun o ho part j hj => wordsOn_agree_inside hc (h G hG o ho).1 (h G hG o ho).2 part j hj
  exact ⟨fun c i hi r hr => (key i r hr).1 (c i hi r hr),
    fun c i hi r hr => (key i r hr).2 (c i hi r hr)⟩

/-- **A sample rows' term reads the listed messages' tables inside their ranges alone.** -/
theorem sampleItem_inside (hI : InOrder S) (hc : S.codes.lengthsOk = true) (os : List Nat)
    {T T' : Nat → Bool → Nat → Nat → K}
    (h : ∀ o ∈ os, (∀ part, CodeThere S o part) ∧ AgreeInside S T T' o) :
    sampleItem ρ S os (wordsOn S T) ↔ sampleItem ρ S os (wordsOn S T') := by
  have key : ∀ o ∈ os, ∀ x : Oracle, S.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList,
      (Says ρ S r (wordsOn S T) ↔ Says ρ S r (wordsOn S T')) := by
    intro o ho x hx r hr
    refine says_agree_in ρ (hI.samples o x hx r hr) fun o' ho' part j hj => ?_
    have e : o' = o := by simpa using ho'
    subst e
    exact wordsOn_agree_inside hc (h o' ho).1 (h o' ho).2 part j hj
  exact ⟨fun c o ho x hx r hr => (key o ho x hx r hr).1 (c o ho x hx r hr),
    fun c o ho x hx r hr => (key o ho x hx r hr).2 (c o ho x hx r hr)⟩

/-! ## What wordsOn reads of a statement -/

/-- **What wordsOn reads of a statement at a message is its shape alone.** -/
theorem wordsOn_congr (S S' : Statement) (T T' : Nat → Bool → Nat → Nat → K) (o o' : Nat)
    (hx : (S'.oracles[o']?).map (·.shape) = (S.oracles[o]?).map (·.shape)) (hT : T' o' = T o)
    (part : Part) (i : Nat) : wordsOn S' T' o' part i = wordsOn S T o part i := by
  have hb : S'.rowBits o' part = S.rowBits o part ∧ realRows S' o' part = realRows S o part := by
    unfold Statement.rowBits realRows
    cases h : S.oracles[o]? with
    | none =>
      rw [h, Option.map_none, Option.map_eq_none_iff] at hx
      rw [hx]
      exact ⟨rfl, rfl⟩
    | some x =>
      rw [h, Option.map_some] at hx
      obtain ⟨x', h', e⟩ := Option.map_eq_some_iff.1 hx
      rw [h']
      dsimp only
      rw [e]
      exact ⟨rfl, rfl⟩
  unfold wordsOn
  rw [hb.1, hb.2, hT]

end OnBytes.Means
