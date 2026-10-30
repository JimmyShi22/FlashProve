-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Tests.lean: what follows where the book passes its tests at a
description (Honest/Frame.lean: `B.word F = none`) and the description passes its test on the places
(Johnson/Desc/Block.lean: `FileDescription.placesOk`): four of the tests (numbers 1, 4, 5 and 6), each as a
proposition; and lemmas on the order of parts (`Addr.before`, `orderOf`). No part and no run of a
protocol occurs here.

  1  `findIdx_at`, `findIdx_lt`, `nodup_of_count`   the first index of an element of a list; a list
     in which every element counts once
  2  `Addr.before_irrefl`, `Addr.before_asymm`, `Addr.before_of_split`, `Addr.before_same`   the
     order of parts: no part is before itself; not both ways; a place of a list's beginning, before
     a place that first occurs after it; two parts of one place
  3  `places_order`, `orderOf_nodup`, `chain_first`, `chain_shared`, `chain_second`   where the test
     on the places passes: no place is twice in the order; each chain's places carry its number (1,
     2, 3: `Place.chain` counts from 1)
  4  `ProverCoinCounts.tests`, `ProverCoinCounts.rowsAt`, `ProverCoinCounts.within`, `ProverCoinCounts.behind`, `ProverCoinCounts.notUp`   the book's tests
     number 1, 4, 5 and 6
  5  `noRow_of`, `ProverCoinCounts.noRow₁`, `ProverCoinCounts.noRow₂`, `ProverCoinCounts.noRow₃`   an address of one chain has no row in
     another chain's table

Beside the library. `rows_chain` (Johnson/RunOne/Sound/KeyListsAtFK.lean, with the key file's
imports) says what `chain_first` says, for a list of another form; it is
not imported here.

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place placesOf)

variable {Xi : Type}

/-! ## 1 The first index -/

section
variable {α : Type} [BEq α] [LawfulBEq α]

/-- After a list that does not hold x, the first index of x is that list's length. -/
theorem findIdx_at (x : α) (l₂ : List α) : ∀ l₁ : List α, x ∉ l₁ →
    (l₁ ++ x :: l₂).findIdx (· == x) = l₁.length
  | [], _ => by simp [List.findIdx_cons]
  | y :: l₁, h => by
    have hy : (y == x) = false := beq_eq_false_iff_ne.2 fun e => h (List.mem_cons.2 (Or.inl e.symm))
    have ih := findIdx_at x l₂ l₁ fun hx => h (List.mem_cons_of_mem _ hx)
    simp only [List.cons_append, List.findIdx_cons, hy, cond_false, ih, List.length_cons]

/-- An element of a list has its first index within that list, whatever follows the list. -/
theorem findIdx_lt (x : α) (l₂ : List α) : ∀ l₁ : List α, x ∈ l₁ →
    (l₁ ++ l₂).findIdx (· == x) < l₁.length
  | [], h => by cases h
  | y :: l₁, h => by
    cases hy : y == x with
    | true => simp [List.findIdx_cons, hy]
    | false =>
      have hx : x ∈ l₁ := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd (beq_iff_eq.2 e.symm) (by rw [hy]; exact Bool.false_ne_true)
        · exact e
      have ih := findIdx_lt x l₂ l₁ hx
      simp only [List.cons_append, List.findIdx_cons, hy, cond_false, List.length_cons]
      omega

/-- A list in which every element counts once has no element twice. -/
theorem nodup_of_count : ∀ l : List α, (∀ x ∈ l, l.count x = 1) → l.Nodup
  | [], _ => List.nodup_nil
  | y :: l, h => by
    have hy : (y :: l).count y = 1 := h y (List.mem_cons.2 (Or.inl rfl))
    rw [List.count_cons_self] at hy
    have hy0 : l.count y = 0 := by omega
    have hnot : y ∉ l := List.count_eq_zero.1 hy0
    refine List.nodup_cons.2 ⟨hnot, nodup_of_count l fun x hx => ?_⟩
    have hx1 := h x (List.mem_cons_of_mem _ hx)
    have hne : (y == x) = false := beq_eq_false_iff_ne.2 fun e => hnot (by rw [e]; exact hx)
    rw [List.count_cons, hne] at hx1
    simpa using hx1

end

/-! ## 2 The order of parts -/

theorem Addr.before_irrefl (ord : List Place) (a : Addr) : a.before ord a = false := by
  simp [Addr.before]

theorem Addr.before_asymm (ord : List Place) {a b : Addr} (h : a.before ord b = true) :
    b.before ord a = false := by
  unfold Addr.before at h ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  rcases h with h | ⟨h1, h2⟩
  · refine ⟨by omega, ?_⟩
    left
    intro e
    rw [e] at h
    omega
  · refine ⟨by rw [h1]; omega, ?_⟩
    right
    omega

/-- A part at a place of l₁ is before a part at a place that first occurs after l₁. -/
theorem Addr.before_of_split {l₁ l₂ : List Place} {a b : Addr} (ha : a.place ∈ l₁)
    (hb : b.place ∉ l₁) : a.before (l₁ ++ b.place :: l₂) b = true := by
  unfold Addr.before
  have h1 := findIdx_lt a.place (b.place :: l₂) l₁ ha
  have h2 := findIdx_at b.place l₂ l₁ hb
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  left
  omega

/-- Two parts of one place. -/
theorem Addr.before_same (ord : List Place) (p : Place) {i j : Nat} (h : i < j) :
    (⟨p, i⟩ : Addr).before ord ⟨p, j⟩ = true := by
  simp [Addr.before, h]

/-! ## 3 The test on the places -/

/-- The table of places, read as places, is the order. -/
theorem places_order (F : FileDescription Xi) : F.places.map (·.2.1) = orderOf F := by
  simp [FileDescription.places, placesOf, orderOf, List.map_append, List.map_map, Function.comp_def]

theorem orderOf_nodup {F : FileDescription Xi} (h : F.placesOk = true) : (orderOf F).Nodup := by
  simp only [FileDescription.placesOk, Bool.and_eq_true] at h
  have h4 := h.2
  have hn : (F.places.map fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)).Nodup :=
    nodup_of_count _ fun x hx => beq_iff_eq.1 (List.all_eq_true.1 h4 x hx)
  have e : (F.places.map fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)) =
      (orderOf F).map fun p => (p.chain, p.link, p.piece) := by
    rw [← places_order, List.map_map]
    rfl
  rw [e] at hn
  exact List.Nodup.of_map _ hn

theorem chain_first {F : FileDescription Xi} (h : F.placesOk = true) :
    ∀ p ∈ F.first.blocksInOrder.map (·.place), p.chain = 1 := by
  simp only [FileDescription.placesOk, Bool.and_eq_true] at h
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
  have := List.all_eq_true.1 h.1.1.1 (b.name, b.place, b.rounds.length)
    (List.mem_map.2 ⟨b, hb, rfl⟩)
  exact beq_iff_eq.1 this

theorem chain_shared {F : FileDescription Xi} (h : F.placesOk = true) :
    ∀ p ∈ F.shared.blocksInOrder.map (·.place), p.chain = 2 := by
  simp only [FileDescription.placesOk, Bool.and_eq_true] at h
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
  have := List.all_eq_true.1 h.1.1.2 (b.name, b.place, b.rounds.length)
    (List.mem_map.2 ⟨b, hb, rfl⟩)
  exact beq_iff_eq.1 this

theorem chain_second {F : FileDescription Xi} (h : F.placesOk = true) :
    ∀ p ∈ F.second.blocksInOrder.map (·.place), p.chain = 3 := by
  simp only [FileDescription.placesOk, Bool.and_eq_true] at h
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
  have := List.all_eq_true.1 h.1.2 (b.name, b.place, b.rounds.length)
    (List.mem_map.2 ⟨b, hb, rfl⟩)
  exact beq_iff_eq.1 this

/-! ## 4 The book's tests -/

section
variable {F : FileDescription Xi} {B : ProverCoinCounts}

/-- Where no test's name is returned, every test passes. -/
theorem ProverCoinCounts.tests (h : B.word F = none) : (B.clauses F).all (fun c => c.2) = true := by
  unfold ProverCoinCounts.word at h
  have h1 : (B.clauses F).find? (fun c => !c.2) = none := by
    cases hf : (B.clauses F).find? (fun c => !c.2) with
    | none => rfl
    | some c =>
      rw [hf] at h
      cases h
  rw [List.all_eq_true]
  intro c hc
  have h2 := List.find?_eq_none.1 h1 c hc
  simpa using h2

/-- The first test: a row is at a place of its chain. -/
theorem ProverCoinCounts.rowsAt (h : B.word F = none) :
    (∀ r ∈ B.first, r.1.place ∈ F.first.blocksInOrder.map (·.place)) ∧
      (∀ r ∈ B.shared, r.1.place ∈ F.shared.blocksInOrder.map (·.place)) ∧
      ∀ r ∈ B.second, r.1.place ∈ F.second.blocksInOrder.map (·.place) := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, -⟩ := t
  exact ⟨fun r hr => List.contains_iff_mem.1 (List.all_eq_true.1 t1 r hr),
    fun r hr => List.contains_iff_mem.1 (List.all_eq_true.1 t2 r hr),
    fun r hr => List.contains_iff_mem.1 (List.all_eq_true.1 t3 r hr)⟩

/-- The fourth test: an entry's block is within its owner's count. -/
theorem ProverCoinCounts.within (h : B.word F = none) : ∀ e ∈ B.ahead,
    e.start.f + e.count.f ≤ (dueAt (B.first ++ B.shared ++ B.second) e.owner).f ∧
      e.start.e + e.count.e ≤ (dueAt (B.first ++ B.shared ++ B.second) e.owner).e := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, t4, -⟩ := t
  intro e he
  have := List.all_eq_true.1 t4 e he
  simpa using this

/-- Of the fifth test, its last clause: an entry's spender is after its owner. -/
theorem ProverCoinCounts.behind (h : B.word F = none) : ∀ e ∈ B.ahead,
    e.owner.before (orderOf F) e.spender = true := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, t5, -⟩ := t
  intro e he
  have := List.all_eq_true.1 t5 e he
  simp only [Bool.and_eq_true] at this
  exact this.2

/-- The sixth test: the shared chain is given no coin of the first chain. -/
theorem ProverCoinCounts.notUp (h : B.word F = none) : ∀ e ∈ B.ahead,
    e.owner.place ∈ F.first.blocksInOrder.map (·.place) → e.spender.place ∉ F.shared.blocksInOrder.map (·.place) := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, -, t6, -⟩ := t
  intro e he h1 h2
  have := List.all_eq_true.1 t6 e he
  rw [List.contains_iff_mem.2 h1, List.contains_iff_mem.2 h2] at this
  cases this

/-! ## 5 One table alone -/

/-- From the proposition to the test: if no row of a table is at the address, `any` is false. -/
theorem noRow_of {l : List (Addr × Due)} {a : Addr} (h : ∀ r ∈ l, r.1 ≠ a) :
    l.any (fun r => r.1 == a) = false := by
  rw [List.any_eq_false]
  intro r hr e
  exact h r hr (beq_iff_eq.1 e)

/-- An address of the first chain has no row in the two other tables. -/
theorem ProverCoinCounts.noRow₁ (h : B.word F = none) (hp : F.placesOk = true) {a : Addr}
    (ha : a.place ∈ F.first.blocksInOrder.map (·.place)) :
    B.shared.any (fun r => r.1 == a) = false ∧ B.second.any (fun r => r.1 == a) = false := by
  have c1 := chain_first hp a.place ha
  refine ⟨noRow_of fun r hr e => ?_, noRow_of fun r hr e => ?_⟩
  · have c2 := chain_shared hp r.1.place ((ProverCoinCounts.rowsAt h).2.1 r hr)
    rw [e] at c2
    omega
  · have c3 := chain_second hp r.1.place ((ProverCoinCounts.rowsAt h).2.2 r hr)
    rw [e] at c3
    omega

/-- An address of the shared chain has no row in the two other tables. -/
theorem ProverCoinCounts.noRow₂ (h : B.word F = none) (hp : F.placesOk = true) {a : Addr}
    (ha : a.place ∈ F.shared.blocksInOrder.map (·.place)) :
    B.first.any (fun r => r.1 == a) = false ∧ B.second.any (fun r => r.1 == a) = false := by
  have c2 := chain_shared hp a.place ha
  refine ⟨noRow_of fun r hr e => ?_, noRow_of fun r hr e => ?_⟩
  · have c1 := chain_first hp r.1.place ((ProverCoinCounts.rowsAt h).1 r hr)
    rw [e] at c1
    omega
  · have c3 := chain_second hp r.1.place ((ProverCoinCounts.rowsAt h).2.2 r hr)
    rw [e] at c3
    omega

/-- An address of the second chain has no row in the two other tables. -/
theorem ProverCoinCounts.noRow₃ (h : B.word F = none) (hp : F.placesOk = true) {a : Addr}
    (ha : a.place ∈ F.second.blocksInOrder.map (·.place)) :
    B.first.any (fun r => r.1 == a) = false ∧ B.shared.any (fun r => r.1 == a) = false := by
  have c3 := chain_second hp a.place ha
  refine ⟨noRow_of fun r hr e => ?_, noRow_of fun r hr e => ?_⟩
  · have c1 := chain_first hp r.1.place ((ProverCoinCounts.rowsAt h).1 r hr)
    rw [e] at c1
    omega
  · have c2 := chain_shared hp r.1.place ((ProverCoinCounts.rowsAt h).2.1 r hr)
    rw [e] at c2
    omega

end

end ProofFile.Honest

#print axioms ProofFile.Honest.findIdx_at
#print axioms ProofFile.Honest.findIdx_lt
#print axioms ProofFile.Honest.nodup_of_count
#print axioms ProofFile.Honest.Addr.before_irrefl
#print axioms ProofFile.Honest.Addr.before_asymm
#print axioms ProofFile.Honest.Addr.before_of_split
#print axioms ProofFile.Honest.Addr.before_same
#print axioms ProofFile.Honest.places_order
#print axioms ProofFile.Honest.orderOf_nodup
#print axioms ProofFile.Honest.chain_first
#print axioms ProofFile.Honest.chain_shared
#print axioms ProofFile.Honest.chain_second
#print axioms ProofFile.Honest.ProverCoinCounts.tests
#print axioms ProofFile.Honest.ProverCoinCounts.rowsAt
#print axioms ProofFile.Honest.ProverCoinCounts.within
#print axioms ProofFile.Honest.ProverCoinCounts.behind
#print axioms ProofFile.Honest.ProverCoinCounts.notUp
#print axioms ProofFile.Honest.noRow_of
#print axioms ProofFile.Honest.ProverCoinCounts.noRow₁
#print axioms ProofFile.Honest.ProverCoinCounts.noRow₂
#print axioms ProofFile.Honest.ProverCoinCounts.noRow₃
