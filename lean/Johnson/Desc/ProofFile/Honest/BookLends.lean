-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLends.lean: where a book of coins passes its own tests
(`ProverCoinCounts.word F = none`, Honest/Frame.lean), the function that gives a part its coins (`lendPart`, the
same file) returns at every run's coins, if the three lists that the part states are the book's.
Lemmas with their proofs; no definition.

  `ProverCoinCounts.ownerIn`   the first two clauses of the book's fifth test: an entry's owner and its spender
     are at places of the description
  `ProverCoinCounts.dueInChain`   at an address of one chain, the count in the three tables joined is the count
     in that chain's table, and the two other tables have no row for it
  `ProverCoinCounts.cutThere`   the block that an entry names can be cut from its owner's coins, as the
     look-up of the spender's chain returns them, at every run's coins
  `ProverCoinCounts.lendThere`   so `lend` returns at a list of entries, at the entries' own names and counts
  `lendPart_of_fit`   so `lendPart` returns at a part whose `takes` is the book's count for its
     address and whose `spends` and `carries` are the names and counts of the book's entries for it,
     in the book's order

What it is for. `lendPart` and `lend` can return an error for six reasons: the part's `takes` is not
the book's count; its own coins cannot be cut; an entry's name is not the one that the part states;
its count is not; the two lists differ in length; the owner's coins cannot be cut. The two on cuts
are excluded by the book's tests. The four others compare the book with what the part states. They
are the three equations that `lendPart_of_fit` has as hypotheses: equations of public lists.

Related lemmas. `fit_of_lent` (Honest/Law/Rule/PartCell.lean) is the converse: a part that is given
its coins at one run's coins meets these three equations (the fields `due`, `sp` and `ca` of `Fit`).
`lendPart_any` (Honest/Law/ReadyAny.lean): if `lendPart` returns at one look-up, it returns at every
look-up with the same counts.

Limits.
  * That a book passes its tests, and the library's test `FileDescription.placesOk`, are hypotheses.
  * The three equations are hypotheses. They are stated of no part of the protocol here.
  * Nothing is said of `lendRow`, of the four tests that `chainSteps` makes before it gives a row
    its coins, or of `ready` (all three: Honest/Frame.lean).
  * What is returned is not described: only that something is.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi V W Y : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- Of the fifth test, its first two clauses: an entry's owner and its spender are at places of the
description. -/
theorem ProverCoinCounts.ownerIn (h : B.word F = none) : ∀ e ∈ B.ahead,
    e.owner.place ∈ orderOf F ∧ e.spender.place ∈ orderOf F := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, t5, -⟩ := t
  intro e he
  have := List.all_eq_true.1 t5 e he
  simp only [Bool.and_eq_true] at this
  exact ⟨List.contains_iff_mem.1 this.1.1, List.contains_iff_mem.1 this.1.2⟩

/-- At an address of the chain number t, from 0: the count in the three tables joined is the count
in that chain's table, and the two other tables have no row for the address. -/
theorem ProverCoinCounts.dueInChain (h : B.word F = none) (hp : F.placesOk = true) {a : Addr} {t : Nat}
    (ht : t = 0 ∨ t = 1 ∨ t = 2) (ha : a.place ∈ placesAt F t) :
    dueAt (B.first ++ B.shared ++ B.second) a = dueAt (B.rowsOf t) a ∧
      (t ≠ 0 → B.first.any (fun r => r.1 == a) = false) ∧
      (t ≠ 1 → B.shared.any (fun r => r.1 == a) = false) ∧
      (t ≠ 2 → B.second.any (fun r => r.1 == a) = false) := by
  rcases ht with rfl | rfl | rfl
  · have n := ProverCoinCounts.noRow₁ h hp ha
    refine ⟨?_, fun e => absurd rfl e, fun _ => n.1, fun _ => n.2⟩
    show dueAt (B.first ++ B.shared ++ B.second) a = dueAt B.first a
    rw [dueAt_right _ _ a n.2, dueAt_right _ _ a n.1]
  · have n := ProverCoinCounts.noRow₂ h hp ha
    refine ⟨?_, fun _ => n.1, fun e => absurd rfl e, fun _ => n.2⟩
    show dueAt (B.first ++ B.shared ++ B.second) a = dueAt B.shared a
    rw [dueAt_right _ _ a n.2, dueAt_left _ _ a n.1]
  · have n := ProverCoinCounts.noRow₃ h hp ha
    refine ⟨?_, fun _ => n.1, fun _ => n.2, fun e => absurd rfl e⟩
    show dueAt (B.first ++ B.shared ++ B.second) a = dueAt B.second a
    rw [List.append_assoc, dueAt_left _ _ a n.1, dueAt_left _ _ a n.2]

/-- **The block that an entry names can be cut from its owner's coins**, as the look-up of the
spender's chain returns them, at every run's coins. `ch`: the number, from 0, of a chain in which
the spender's place is. -/
theorem ProverCoinCounts.cutThere (h : B.word F = none) (hp : F.placesOk = true) {e : Ahead}
    (he : e ∈ B.ahead) {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2)
    (hs : e.spender.place ∈ placesAt F ch) (k : Coins B) :
    ∃ y, (k.look ch e.owner).2.cut e.start e.count = some y := by
  have ho := (ProverCoinCounts.ownerIn h e he).1
  have hot : ∃ t, (t = 0 ∨ t = 1 ∨ t = 2) ∧ e.owner.place ∈ placesAt F t := by
    unfold orderOf at ho
    rcases List.mem_append.1 ho with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact ⟨0, Or.inl rfl, h2⟩
      · exact ⟨1, Or.inr (Or.inl rfl), h2⟩
    · exact ⟨2, Or.inr (Or.inr rfl), h1⟩
  obtain ⟨t, ht, hot⟩ := hot
  have hv := ProverCoinCounts.visible h hp he ht hch hot hs
  have hw := ProverCoinCounts.within h e he
  obtain ⟨hdue, r1, r2, r3⟩ := ProverCoinCounts.dueInChain h hp ht hot
  rw [hdue] at hw
  obtain ⟨get, put, -, -, hself⟩ :=
    Coins.lens e.owner (dueAt (B.rowsOf t) e.owner) t ht rfl r1 r2 r3
  rw [hself ch hv k]
  exact Cs.cut_some (get k) hw

/-- **`lend` returns at a list of the book's entries**, at the entries' own names and counts, in the
look-up of a chain in which all their spenders' places are. -/
theorem ProverCoinCounts.lendThere (h : B.word F = none) (hp : F.placesOk = true) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) (k : Coins B) : ∀ es : List Ahead,
    (∀ e ∈ es, e ∈ B.ahead ∧ e.spender.place ∈ placesAt F ch) →
    ∃ y, lend (k.look ch) (es.map Ahead.named) es = .ok y
  | [], _ => ⟨(), rfl⟩
  | e :: es, hall => by
    obtain ⟨x, hx⟩ := ProverCoinCounts.cutThere h hp (hall e (List.Mem.head _)).1 hch
      (hall e (List.Mem.head _)).2 k
    obtain ⟨y, hy⟩ := ProverCoinCounts.lendThere h hp hch k es fun e' he' => hall e' (List.Mem.tail _ he')
    refine ⟨(x, y), ?_⟩
    show lend (k.look ch) (e.named :: es.map Ahead.named) (e :: es) = .ok (x, y)
    simp only [lend, Ahead.named, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    show (lend (k.look ch) (es.map Ahead.named) es).map (fun y => (x, y)) = .ok (x, y)
    rw [hy]
    rfl

/-- **A part whose three stated lists are the book's is given its coins, at every run's coins.** The
converse of `fit_of_lent` (Honest/Law/Rule/PartCell.lean). `ch`: the number, from 0, of a chain in
which the part's place is. -/
theorem lendPart_of_fit (h : B.word F = none) (hp : F.placesOk = true) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {a : Addr} (ha : a.place ∈ placesAt F ch) {p : Part V W Y}
    (hd : p.takes = dueAt (B.rowsOf ch) a) (hsp : (spentE B a).map Ahead.named = p.spends)
    (hca : (carryE B a).map Ahead.named = p.carries) (k : Coins B) :
    ∃ c, lendPart B (B.rowsOf ch) (k.look ch) a p = .ok c := by
  have c1 : ¬ (p.takes != dueAt (B.rowsOf ch) a) = true := by
    rw [hd]
    simp
  obtain ⟨-, r1, r2, r3⟩ := ProverCoinCounts.dueInChain h hp hch ha
  obtain ⟨get, put, -, -, hself⟩ := Coins.lens a (dueAt (B.rowsOf ch) a) ch hch rfl r1 r2 r3
  have hown : ∃ own, (k.look ch a).2.cut ⟨0, 0⟩ p.takes = some own := by
    rw [hself ch (Or.inl rfl) k, hd]
    exact Cs.cut_some (get k) ⟨Nat.le_of_eq (Nat.zero_add _), Nat.le_of_eq (Nat.zero_add _)⟩
  have mS : ∀ e ∈ spentE B a, e ∈ B.ahead ∧ e.spender.place ∈ placesAt F ch := by
    intro e he
    unfold spentE at he
    obtain ⟨h1, -⟩ := List.mem_filter.1 he
    obtain ⟨h3, h4⟩ := List.mem_filter.1 h1
    exact ⟨h3, by rw [beq_iff_eq.1 h4]; exact ha⟩
  have mC : ∀ e ∈ carryE B a, e ∈ B.ahead ∧ e.spender.place ∈ placesAt F ch := by
    intro e he
    unfold carryE at he
    obtain ⟨h1, -⟩ := List.mem_filter.1 he
    obtain ⟨h3, h4⟩ := List.mem_filter.1 h1
    exact ⟨h3, by rw [beq_iff_eq.1 h4]; exact ha⟩
  have hS : ∃ sp, lend (k.look ch) p.spends (spentE B a) = .ok sp := by
    rw [← hsp]
    exact ProverCoinCounts.lendThere h hp hch k _ mS
  have hC : ∃ ca, lend (k.look ch) p.carries (carryE B a) = .ok ca := by
    rw [← hca]
    exact ProverCoinCounts.lendThere h hp hch k _ mC
  obtain ⟨own, hown⟩ := hown
  obtain ⟨sp, hS⟩ := hS
  obtain ⟨ca, hC⟩ := hC
  refine ⟨(own, sp, ca), ?_⟩
  unfold lendPart
  simp only
  rw [if_neg c1, hown]
  show ((lend (k.look ch) p.spends (spentE B a)).bind fun sp =>
    (lend (k.look ch) p.carries (carryE B a)).map fun ca => (own, sp, ca)) = .ok (own, sp, ca)
  rw [hS, hC]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.ProverCoinCounts.ownerIn
#print axioms ProofFile.Honest.ProverCoinCounts.dueInChain
#print axioms ProofFile.Honest.ProverCoinCounts.cutThere
#print axioms ProofFile.Honest.ProverCoinCounts.lendThere
#print axioms ProofFile.Honest.lendPart_of_fit
