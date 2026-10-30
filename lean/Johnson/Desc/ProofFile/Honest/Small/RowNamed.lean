-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/RowNamed.lean: CONDITIONAL: NO KIND IS NAMED: TWO TESTS WITH
CODE ON A BOOK AT A PLACE AND A ROW OF PARTS, AND THAT EACH GIVES THAT THE FRAME's LENDING TO THAT
ROW RETURNS. On public data alone: of a part they read what it takes, spends and carries: names and
counts. Four definitions with code; eight statements with their proofs.

  partFits · rowFits       a test, at one part and along the row, for parts that take nothing and
                           carry nothing: the chain's table counts nothing at the part's address;
                           every entry with that spender is a spent one; these entries, by name and
                           count, are what the part states; each lies inside its owner's coins (due:
                           how many are at hand at an address)
  partBook_of_fits · rowBook_of_rowFits · lends_of_rowFits   CONDITIONAL: in the first chain, where
                           rowFits accepts at the book's own numbers, lendRow returns, at all coins
  partNamed · rowNamed     the same test without its last clause
  inside_first · partFits_of_named · rowFits_of_named · lends_of_rowNamed   CONDITIONAL: where the
                           book passes its own tests, the description's test on its places accepts
                           and the place stands in the first chain's list: rowNamed gives rowFits at
                           the book's own numbers
  lendsRow_of_rowNamed     CONDITIONAL: under the same: **rowNamed gives the frame's own test
                           lendsRow** (Honest/Small/LendsRow.lean, of other authors)

Called, of other authors: PartBook · RowBook · lendRow_ok · look_due_first
(Honest/K3/Law/RowLends.lean: general in the row by their statements, in the folder of the kind K3)
· dueAt_right · Addr.not_before (Honest/Law/Rule/Lent.lean) · lendsRow_iff
(Honest/Small/LendsRow.lean).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. That a test accepts at any book is not said here. They say whether the lending
returns: nothing on what is lent. The first chain alone. No module of the kind K5 and none under the
library's folder ThirdParty/ lies in the import closure; thirteen of the kind K3's do. THE TESTS'
FIRST TWO CLAUSES NARROW THEM TO PLAIN PARTS: they are stricter than the lending (lendPart,
Honest/Frame.lean), which also lends to a part that takes coins of its own, where the book has as
many, and to one that carries runs; at a part that meets the two the other four are, by lendPart's
text, what it enforces itself: that is not proved here. partNamed is partFits's text without its
last clause, typed a second time: partFits_of_named leans on the two texts' bracketing. No property
is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.RowLends
import Johnson.Desc.ProofFile.Honest.Law.Rule.Lent
import Johnson.Desc.ProofFile.Honest.Small.LendsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Place FileDescription)
open ProofFile.Honest.K3.Law (PartBook RowBook lendRow_ok look_due_first)

variable {V W X : Type}

/-- **What the lending asks at one part, as a test with code.** due: how many coins are at hand at
an address. -/
def partFits (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (p : Part V W X)
    (a : Addr) : Bool :=
  p.takes == ⟨0, 0⟩ && p.carries == [] && dueAt rows a == ⟨0, 0⟩ &&
    (B.ahead.filter fun e => e.spender == a).all (·.once) &&
    (B.ahead.filter fun e => e.spender == a).map Ahead.named == p.spends &&
    (B.ahead.filter fun e => e.spender == a).all fun e =>
      decide (e.start.f + e.count.f ≤ (due e.owner).f) &&
        decide (e.start.e + e.count.e ≤ (due e.owner).e)

/-- The like at every part of a row, from the number j on. -/
def rowFits (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Place) :
    List (Part V W X) → Nat → Bool
  | [], _ => true
  | p :: ps, j => partFits B rows due p ⟨a, j⟩ && rowFits B rows due a ps (j + 1)

/-- Where the test accepts at the look-up's own numbers: PartBook. -/
theorem partBook_of_fits {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {p : Part V W X} {a : Addr}
    (h : partFits B rows (fun o => (look o).1) p a = true) : PartBook B rows look p a := by
  simp only [partFits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := h
  exact ⟨g1, g2, g3, g4, g5, g6⟩

/-- The like at a row: RowBook. -/
theorem rowBook_of_rowFits {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : Place} : ∀ (ps : List (Part V W X)) (j : Nat),
    rowFits B rows (fun o => (look o).1) a ps j = true → RowBook B rows look a ps j
  | [], _, _ => trivial
  | p :: ps, j, h => by
    have h' : (partFits B rows (fun o => (look o).1) p ⟨a, j⟩ &&
      rowFits B rows (fun o => (look o).1) a ps (j + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨partBook_of_fits h'.1, rowBook_of_rowFits ps (j + 1) h'.2⟩

/-- **In the first chain: where the test accepts at the book's own numbers, the lending to the row
returns at every run's coins.** CONDITIONAL: the test accepts. -/
theorem lends_of_rowFits {B : ProverCoinCounts} {a : Place} {ps : List (Part V W X)}
    (h : rowFits B (B.rowsOf 0) (dueAt B.first) a ps 0 = true) (k : Coins B) :
    ∃ u, lendRow B (B.rowsOf 0) (k.look 0) a ps 0 = .ok u := by
  have e : (fun o => (k.look 0 o).1) = dueAt B.first := funext (look_due_first B k)
  obtain ⟨c, hc, -⟩ := lendRow_ok B (B.rowsOf 0) (k.look 0) a ps 0
    (rowBook_of_rowFits ps 0 (by rw [e]; exact h))
  exact ⟨c, hc⟩

/-! ## 2 "Inside" out of the book's own tests -/

/-- The test at one part without its last clause ("each entry lies inside its owner's coins"). -/
def partNamed (B : ProverCoinCounts) (rows : List (Addr × Due)) (p : Part V W X) (a : Addr) : Bool :=
  p.takes == ⟨0, 0⟩ && p.carries == [] && dueAt rows a == ⟨0, 0⟩ &&
    (B.ahead.filter fun e => e.spender == a).all (·.once) &&
    (B.ahead.filter fun e => e.spender == a).map Ahead.named == p.spends

/-- The like at every part of a row, from the number j on. -/
def rowNamed (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : Place) : List (Part V W X) → Nat → Bool
  | [], _ => true
  | p :: ps, j => partNamed B rows p ⟨a, j⟩ && rowNamed B rows a ps (j + 1)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- **An entry whose spender stands in the first chain lies inside its owner's coins as the first
chain's table counts them.** CONDITIONAL: the book passes its own tests; the description's test on
its places accepts; e is an entry of the book; its spender's place stands in the first chain's list.
-/
theorem inside_first (h : B.word F = none) (hp : F.placesOk = true) {e : Ahead} (he : e ∈ B.ahead)
    (hs : e.spender.place ∈ F.first.blocksInOrder.map (·.place)) :
    e.start.f + e.count.f ≤ (dueAt B.first e.owner).f ∧
      e.start.e + e.count.e ≤ (dueAt B.first e.owner).e := by
  have ho : e.owner.place ∈ F.first.blocksInOrder.map (·.place) := by
    by_contra hq
    have hb := ProverCoinCounts.behind h e he
    have hnb : Addr.before (F.first.blocksInOrder.map (·.place) ++
        (F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place))) e.owner e.spender = false :=
      Addr.not_before (a := e.spender) (b := e.owner) hs hq
    unfold orderOf at hb
    rw [List.append_assoc, hnb] at hb
    cases hb
  obtain ⟨n2, n3⟩ := ProverCoinCounts.noRow₁ h hp ho
  have hw := ProverCoinCounts.within h e he
  rw [dueAt_right _ _ _ n3, dueAt_right _ _ _ n2] at hw
  exact hw

/-- At such a book the shorter test gives the longer, at a part of the first chain. CONDITIONAL: as
`inside_first`; the shorter test accepts. -/
theorem partFits_of_named (h : B.word F = none) (hp : F.placesOk = true)
    {rows : List (Addr × Due)} {p : Part V W X} {a : Addr}
    (ha : a.place ∈ F.first.blocksInOrder.map (·.place)) (hn : partNamed B rows p a = true) :
    partFits B rows (dueAt B.first) p a = true := by
  unfold partNamed at hn
  unfold partFits
  rw [hn, Bool.true_and]
  refine List.all_eq_true.2 fun e he => ?_
  obtain ⟨he1, he2⟩ := List.mem_filter.1 he
  obtain ⟨i1, i2⟩ := inside_first h hp he1 (by rw [beq_iff_eq.1 he2]; exact ha)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨i1, i2⟩

/-- The like at a row. -/
theorem rowFits_of_named (h : B.word F = none) (hp : F.placesOk = true)
    {rows : List (Addr × Due)} {a : Place} (ha : a ∈ F.first.blocksInOrder.map (·.place)) :
    ∀ (ps : List (Part V W X)) (j : Nat), rowNamed B rows a ps j = true →
      rowFits B rows (dueAt B.first) a ps j = true
  | [], _, _ => rfl
  | p :: ps, j, hn => by
    have hn' : (partNamed B rows p ⟨a, j⟩ && rowNamed B rows a ps (j + 1)) = true := hn
    rw [Bool.and_eq_true] at hn'
    show (partFits B rows (dueAt B.first) p ⟨a, j⟩ &&
      rowFits B rows (dueAt B.first) a ps (j + 1)) = true
    rw [partFits_of_named h hp ha hn'.1, rowFits_of_named h hp ha ps (j + 1) hn'.2]
    rfl

/-- **In the first chain, at a book that passes its own tests: where the shorter test accepts, the
lending to the row returns at every run's coins.** CONDITIONAL: as `inside_first`; the row's place
stands in the first chain's list; the shorter test accepts. -/
theorem lends_of_rowNamed (h : B.word F = none) (hp : F.placesOk = true) {a : Place}
    (ha : a ∈ F.first.blocksInOrder.map (·.place)) {ps : List (Part V W X)}
    (hn : rowNamed B (B.rowsOf 0) a ps 0 = true) (k : Coins B) :
    ∃ u, lendRow B (B.rowsOf 0) (k.look 0) a ps 0 = .ok u :=
  lends_of_rowFits (rowFits_of_named h hp ha ps 0 hn) k

/-- **The shorter test on plain parts gives the frame's.** CONDITIONAL: the book passes its own
tests; the description's test on its places accepts; the place stands in the first chain's list; the
shorter test. -/
theorem lendsRow_of_rowNamed {V W X Yi : Type} {F : FileDescription Yi} {B : ProverCoinCounts}
    (h : B.word F = none) (hp : F.placesOk = true) {a : Place}
    (ha : a ∈ F.first.blocksInOrder.map (·.place)) {ps : List (Part V W X)}
    (hn : rowNamed B (B.rowsOf 0) a ps 0 = true) : lendsRow B 0 a ps = true :=
  (lendsRow_iff default 0 a ps).1 (lends_of_rowNamed h hp ha hn default)

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.partBook_of_fits
#print axioms ProofFile.Honest.Small.rowBook_of_rowFits
#print axioms ProofFile.Honest.Small.lends_of_rowFits
#print axioms ProofFile.Honest.Small.inside_first
#print axioms ProofFile.Honest.Small.partFits_of_named
#print axioms ProofFile.Honest.Small.rowFits_of_named
#print axioms ProofFile.Honest.Small.lends_of_rowNamed
#print axioms ProofFile.Honest.Small.lendsRow_of_rowNamed
