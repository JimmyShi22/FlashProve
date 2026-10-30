-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieRiders.lean: WHICH ITEMS RIDE AT K9's FOUR PLACES OF EACH OF THE
25 SEGMENTS, AT THE WRITTEN FULL LIST: THE TWO FACTS ON THE TABLE THAT `t5_quiet` (FifthTie.lean)
AND `t5_eq` (FifthTieEq.lean) ASK OF EVERY RIDER, BY THE KERNEL, in the rule's own letters
(`openAfter`, `insQ`). Tests with code on the written list, each evaluated by `decide +kernel`; and
the bridge from the rule's open set to the table's computed list.

What is said.
  `batchIx l`: the number of segment l's batching in the flat list of places; the frame's
    sub-protocol behind it, the one equation and the shutting stand 1, 2 and 4 behind it.
  `quietAt`, `eqAt`: the 75 quiet places; the 25 places of the one equation.
  `kinds_full`: at these numbers stand, by the list's own kinds and segments: K9, frame, K9, K9.
  `ridersAt k`: what is open in front of place k and is neither closed nor read there, nor "no
    mark": a list.
  `rider_mem`: a rider in the rule's letters stands in that list. (`open_mem9`: the bridge: it is
    `open_mem` of Johnson/P1L20R/FramePays.lean, typed here anew
    over the same two tests.)
  `quietB_full`, `riders_quiet`: **at the 75: every rider has no part of a segment of its own or is
    "wo", and is not the digits' part.**
  `eqB_full`, `riders_eq`: **at the 25: every rider is of a sort in `pushRider`, and is not the
    digits' part.**
  Three tests that fail, by the kernel: `noWo_fails`: "no rider has a part of its own" is FALSE at
    the 75 ("wo" rides); `push_fails_at_shut`: `pushRider` is FALSE of a rider at the shuttings
    ("carry" rides there); `quiet_fails_in_front`: the first test is FALSE one place in front of the
    batchings (forms ride there).

Limits. Facts on the table at the written full list alone: another list wants its own evaluation.
The third fact on a rider (its pins' trees lie below the piece's first tree) reads the plan's
numbers: not here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTieEq
import Johnson.Desc.Sound.SpineList
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item start openSets readsOpen flatPlacesOf)
open Johnson.Desc.First.Walk.Tied

/-- The written full list of places. -/
abbrev plF : List Place := flatPlacesOf linksFull true

/-- The number of segment l's batching. -/
def batchIx (l : ℕ) : ℕ := if l = 24 then 347 else 14 * l + 9

/-- The batchings, the sub-protocols behind them, the shuttings. -/
def quietAt : List ℕ :=
  (List.range 25).flatMap fun l => [batchIx l, batchIx l + 1, batchIx l + 4]

/-- The one equation's places. -/
def eqAt : List ℕ := (List.range 25).map fun l => batchIx l + 2

/-- A test with code: what stands at these numbers. -/
def kindsB : Bool :=
  (List.range 25).all fun l =>
    [(0, KindName.K9), (1, KindName.frame), (2, KindName.K9), (4, KindName.K9)].all fun x =>
      (plF[batchIx l + x.1]?).any fun p => p.kind == x.2 && p.link == some l

set_option maxRecDepth 1000000 in
theorem kinds_full : kindsB = true := by decide +kernel

/-- What rides at place k, as a list. -/
def ridersAt (k : ℕ) : List Item :=
  ((openSets linksFull plF (start linksFull))[k]?.getD []).filter fun i =>
    !(insL linksFull plF k).contains i

set_option maxRecDepth 1000000 in
theorem readsOpen9 : readsOpen linksFull plF (start linksFull) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowsApart9 : rowsApart linksFull plF = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem length9 : plF.length = 358 := by decide +kernel

/-- An item that is open at a border stands in the table's computed list there. -/
theorem open_mem9 {k : ℕ} {i : Item} (hk : k ≤ plF.length)
    (h : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i) :
    i ∈ (openSets linksFull plF (start linksFull))[k]?.getD [] := by
  have hu : Item.unmarked ∈ start linksFull := List.mem_append_left _ List.mem_cons_self
  have hL : i ∈ openL (insL linksFull plF) (outsL linksFull plF) (start linksFull) k :=
    (openIsList Item (insL linksFull plF) (outsL linksFull plF) (start linksFull) k i).1 h
  exact (openL_iff_openSets linksFull plF (start linksFull) readsOpen9 rowsApart9 hu k hk i).1 hL

/-- A rider in the rule's letters stands in the list. -/
theorem rider_mem {k : ℕ} {i : Item} (hk : k ≤ plF.length)
    (ho : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i)
    (hn : ¬ insQ linksFull plF k i) : i ∈ ridersAt k := by
  refine List.mem_filter.2 ⟨open_mem9 hk ho, ?_⟩
  have hn' : i ∉ insL linksFull plF k := hn
  simpa using hn'

/-- "Not the digits' part", with code. -/
def notDigitsB : Item → Bool
  | .constr _ p => !(p == .lookDigits)
  | _ => true

theorem notOwn_of_B {i : Item} (h : notDigitsB i = true) : notOwn ownDigits i := by
  cases i with
  | constr m p =>
    show (p == .lookDigits) = false
    simpa [notDigitsB] using h
  | _ => trivial

/-- "wo", with code. -/
def isWo : Item → Bool
  | .wo _ => true
  | _ => false

/-- The test at the 75. -/
def quietB : Bool :=
  quietAt.all fun k => (ridersAt k).all fun i => (i.part.isNone || isWo i) && notDigitsB i

/-- The test at the 25. -/
def eqB : Bool := eqAt.all fun k => (ridersAt k).all fun i => pushRider i && notDigitsB i

set_option maxRecDepth 1000000 in
theorem quietB_full : quietB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem eqB_full : eqB = true := by decide +kernel

theorem quietAt_le {k : ℕ} (hk : k ∈ quietAt) : k ≤ plF.length := by
  rw [length9]
  unfold quietAt at hk
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.1 hk
  have hl' : l < 25 := List.mem_range.1 hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  unfold batchIx at hk
  split at hk <;> omega

theorem eqAt_le {k : ℕ} (hk : k ∈ eqAt) : k ≤ plF.length := by
  rw [length9]
  unfold eqAt at hk
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hk
  have hl' : l < 25 := List.mem_range.1 hl
  unfold batchIx
  split <;> omega

/-- **AT THE 75 QUIET PLACES.** -/
theorem riders_quiet {k : ℕ} (hk : k ∈ quietAt) {i : Item}
    (ho : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i)
    (hn : ¬ insQ linksFull plF k i) :
    (i.part = none ∨ ∃ m, i = .wo m) ∧ notOwn ownDigits i := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 quietB_full k hk) i
    (rider_mem (quietAt_le hk) ho hn)
  rw [Bool.and_eq_true, Bool.or_eq_true] at h1
  refine ⟨?_, notOwn_of_B h1.2⟩
  rcases h1.1 with h | h
  · exact Or.inl (Option.isNone_iff_eq_none.1 h)
  · cases i with
    | wo m => exact Or.inr ⟨m, rfl⟩
    | _ => cases h

/-- **AT THE 25 PLACES OF THE ONE EQUATION.** -/
theorem riders_eq {k : ℕ} (hk : k ∈ eqAt) {i : Item}
    (ho : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i)
    (hn : ¬ insQ linksFull plF k i) : pushRider i = true ∧ notOwn ownDigits i := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 eqB_full k hk) i
    (rider_mem (eqAt_le hk) ho hn)
  rw [Bool.and_eq_true] at h1
  exact ⟨h1.1, notOwn_of_B h1.2⟩

/-! ### three tests that fail -/

set_option maxRecDepth 1000000 in
/-- "No rider has a part of a segment of its own" is false at the 75. -/
theorem noWo_fails :
    (quietAt.all fun k => (ridersAt k).all fun i => i.part.isNone) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- `pushRider` is false of a rider at the shuttings. -/
theorem push_fails_at_shut :
    (((List.range 25).map fun l => batchIx l + 4).all fun k =>
      (ridersAt k).all fun i => pushRider i) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test of the 75 is false one place in front of the batchings. -/
theorem quiet_fails_in_front :
    (((List.range 25).map fun l => batchIx l - 1).all fun k =>
      (ridersAt k).all fun i => (i.part.isNone || isWo i) && notDigitsB i) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kinds_full
#print axioms VerifiableInference.Desc.LinkJoin.rider_mem
#print axioms VerifiableInference.Desc.LinkJoin.riders_quiet
#print axioms VerifiableInference.Desc.LinkJoin.riders_eq
#print axioms VerifiableInference.Desc.LinkJoin.noWo_fails
#print axioms VerifiableInference.Desc.LinkJoin.push_fails_at_shut
#print axioms VerifiableInference.Desc.LinkJoin.quiet_fails_in_front
