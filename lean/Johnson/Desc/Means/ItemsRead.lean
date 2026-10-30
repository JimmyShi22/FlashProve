-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/ItemsRead.lean: which words an item reads.

An item of Johnson/Desc/Means/Items.lean is a proposition on all words. This file shows which of
them it reads: a row that has passed the tests of the adding at a group has coefficients on the
group's members alone, so what it says is the same of two families of words that agree on the
members (says_agree). So, at a statement in order, the item of an open row reads the words of its
group's members alone (openSays_agree), and the item of a message's sample rows the words of that
message alone (sampleSays_agree).

Main theorems: value_agree, says_agree, openSays_agree, sampleSays_agree.

What is not claimed. How the words are made of a witness. Nothing on soundness.

-/
import Johnson.Desc.Means.Items

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S : Statement} {G : Group} {row : Row}

/-- A row applied to words reads the words of the group's members alone. -/
theorem value_agree (hr : RowIn S G row) {m m' : Words K}
    (h : ∀ o ∈ G.members.toList, ∀ part i, m o part i = m' o part i) :
    value ρ S row m = value ρ S row m' := by
  unfold value onTable
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : o ∈ G.members.toList
  · congr 1 <;>
    · apply Finset.sum_congr rfl
      intro i _
      rw [h o ho]
  · congr 1 <;>
    · apply Finset.sum_congr rfl
      intro i _
      rw [coefficient_off ρ hr ho, zero_mul, zero_mul]

/-- What such a row says is the same of words that agree on the members. -/
theorem says_agree (hr : RowIn S G row) {m m' : Words K}
    (h : ∀ o ∈ G.members.toList, ∀ part i, m o part i = m' o part i) :
    Says ρ S row m ↔ Says ρ S row m' := by
  unfold Says
  rw [value_agree ρ hr h]

/-- **The item of an open row reads the words of its group's members alone.** -/
theorem openSays_agree (hI : InOrder S) {g : Nat} (hG : S.groups[g]? = some G) (i : Nat)
    {m m' : Words K} (h : ∀ o ∈ G.members.toList, ∀ part j, m o part j = m' o part j) :
    OpenSays ρ S g i m ↔ OpenSays ρ S g i m' := by
  have key : ∀ r, RowAt S g i r → (Says ρ S r m ↔ Says ρ S r m') := by
    intro r hr
    obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
    rw [hG] at hG'
    obtain rfl := Option.some.inj hG'
    exact says_agree ρ
      (hI.rows g G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))) h
  exact ⟨fun c r hr => (key r hr).1 (c r hr), fun c r hr => (key r hr).2 (c r hr)⟩

/-- **The item of a message's sample rows reads the words of that message alone.** -/
theorem sampleSays_agree (hI : InOrder S) (o : Nat) {m m' : Words K}
    (h : ∀ part j, m o part j = m' o part j) :
    SampleSays ρ S o m ↔ SampleSays ρ S o m' := by
  have key : ∀ (x : Oracle), S.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList,
      (Says ρ S r m ↔ Says ρ S r m') := by
    intro x hx r hr
    refine says_agree ρ (hI.samples o x hx r hr) fun o' ho' part j => ?_
    have e : o' = o := by simpa using ho'
    rw [e]
    exact h part j
  exact ⟨fun c x hx r hr => (key x hx r hr).1 (c x hx r hr),
    fun c x hx r hr => (key x hx r hr).2 (c x hx r hr)⟩

end OnBytes.Means
