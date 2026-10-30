-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OwnerAt.lean: A TEST ON THE BOOK OF COINS (OwnerTest,
Honest/BookGuard.lean) WHOSE fits SAYS THE SAME AT TWO BOOKS WITH THE SAME ENTRIES AT ONE OWNER SAYS
THE SAME AT BOTH THERE: OF A BOOK IT READS THE ENTRIES WITH THAT OWNER, AND NO OTHER. No kind is
named but in the statements on spFits and spOwnerTest. Statements with their proofs; no definition
(aheadAt, onlyAt: Honest/K14/OwnerWholeTest.lean).

  filter_onlyAt, spentBy_onlyAt, knownBy_onlyAt   what a part spends of the owner's coins, and
                  what else of them is known there, are the same at both books
  ok_onlyAt       **a test whose fits says the same at both books says the same at both**: the
                  frame's "at every spender of the book" is idle where nothing of the owner's is
                  spent
  spendersOf_onlyAt, withinCount_onlyAt, spFits_onlyAt, spOwner_ok_onlyAt   so at the test for the
                  part at "send o_omega" (Honest/K14/FreshOwner.lean)
  spenders_of_aheadAt, knownBy_of_aheadAt   the entries that spend of the owner's coins, and what is
                  known at a part, written as filters of the entries at the owner
  spentBy_congr, knownBy_congr, spendersOf_congr, wholeOrSpent_congr, ownerOk_congr, spFits_congr,
  spOwner_ok_congr   **two books with the same entries at the owner**: what is spent and known
                  there, the short test wholeOrSpent, every test whose fits says the same at both,
                  and the test for the part at "send o_omega" say the same at both: so each can be
                  asked of a book, or of that book with another list laid for its entries, where the
                  two lists agree at the owner

Kin. The frame's bookWhole_spent_known_shared (Honest/BookSharedLaw.lean) has the conclusions of
spentBy_congr and knownBy_congr at one pair of books: the whole book and that book with the short
list; its filter_owner_and (Honest/BookSharedKit.lean) is the general lemma beneath: two texts of
one thing. Its ok_shared, with guardAll_iff and guardClearB_congr (Honest/BookSharedOk.lean), says,
where bookWhole returns, at an owner that stands at no place of the first or the second chain, of
every test at that same pair of books: the test at the whole book is its fits there and its guard's
half at the short list: kin of ownerOk_congr, which is general in the two books and the owner and
asks that fits says the same at both.
How it is used. A test is evaluated or shown at the short book; the verdict is carried to the raw or
the whole book by a congruence (Honest/K14/BookAtOmega.lean). Honest/K14/OwnerWhole.lean's
statements can be called AT THE WHOLE BOOK alone, which has passed its own tests: of the short
book's own tests nothing is known.

What it is for. A maker's book has thousands of entries; at one owner a handful. Whoever knows the
handful can evaluate the test at a short book.
What is not claimed. Which entries any book has. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OwnerWholeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)

variable (B : ProverCoinCounts) (ord : List Place) (o p : Addr)

/-- A filter that asks the owner first is the same at both books. -/
theorem filter_onlyAt (f : Ahead → Bool) :
    (onlyAt B o).ahead.filter (fun e => e.owner == o && f e) =
      B.ahead.filter fun e => e.owner == o && f e := by
  show (B.ahead.filter (·.owner == o)).filter (fun e => e.owner == o && f e) = _
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  cases e.owner == o <;> simp

/-- What a part spends of the owner's coins is the same at both books. -/
theorem spentBy_onlyAt : (onlyAt B o).spentBy o p = B.spentBy o p := by
  have h := filter_onlyAt B o fun e => e.spender == p && e.once
  simpa only [ProverCoinCounts.spentBy, Bool.and_assoc] using h

/-- What else of the owner's coins is known at a part is the same at both books. -/
theorem knownBy_onlyAt : (onlyAt B o).knownBy ord o p = B.knownBy ord o p := by
  have h := filter_onlyAt B o fun e =>
    !(e.spender == p && e.once) && (e.spender == p || e.spender.before ord p)
  simpa only [ProverCoinCounts.knownBy, Bool.and_assoc] using h

/-- **A test whose fits says the same at both books says the same at both.** -/
theorem ok_onlyAt (t : OwnerTest) (hf : t.fits (onlyAt B o) ord o = t.fits B ord o) :
    t.ok (onlyAt B o) ord o = t.ok B ord o := by
  have hg : ∀ q, (((onlyAt B o).spentBy o q).isEmpty ||
      guardClearB (t.guard o) (onlyAt B o) ord o q) =
        ((B.spentBy o q).isEmpty || guardClearB (t.guard o) B ord o q) := fun q => by
    unfold guardClearB ProverCoinCounts.spentRuns ProverCoinCounts.knownRuns
    rw [spentBy_onlyAt, knownBy_onlyAt]
  unfold OwnerTest.ok
  rw [hf]
  congr 1
  simp only [hg]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_map]
  constructor
  · rintro h q ⟨e, he, rfl⟩
    by_cases hs : B.spentBy o e.spender = []
    · rw [hs]
      rfl
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hs
      have hx' := List.mem_filter.1 hx
      have h2 := hx'.2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact h e.spender ⟨x, List.mem_filter.2 ⟨hx'.1, by rw [h2.1.1]; exact beq_self_eq_true _⟩,
        h2.1.2⟩
  · rintro h q ⟨e, he, rfl⟩
    exact h e.spender ⟨e, (List.mem_filter.1 he).1, rfl⟩

/-- The entries that spend of the owner's coins are the same at both books. -/
theorem spendersOf_onlyAt : spendersOf (onlyAt B o) o = spendersOf B o := by
  have h := filter_onlyAt B o fun e => e.once
  have e1 : ∀ l : List Ahead, (l.filter fun e => e.once && e.owner == o) =
      l.filter fun e => e.owner == o && e.once := fun l =>
    List.filter_congr fun e _ => Bool.and_comm _ _
  unfold spendersOf
  rw [e1, e1]
  exact h

/-- withinCount says the same at both books. -/
theorem withinCount_onlyAt (d : Due) : withinCount d (onlyAt B o) o = withinCount d B o := by
  apply Bool.eq_iff_iff.2
  unfold withinCount
  simp only [List.all_eq_true]
  constructor
  · intro h e he
    by_cases ho : (e.owner == o) = true
    · exact h e (List.mem_filter.2 ⟨he, ho⟩)
    · simp [ho]
  · intro h e he
    exact h e (List.mem_filter.1 he).1

/-- spFits says the same at both books. -/
theorem spFits_onlyAt (A : SendPub) (n : Nat) : spFits A n (onlyAt B o) o = spFits A n B o := by
  unfold spFits oneSpender
  rw [spendersOf_onlyAt, withinCount_onlyAt]

/-- **The test for the part at "send o_omega" reads the entries with that owner alone.** -/
theorem spOwner_ok_onlyAt (A : SendPub) (n : Nat) :
    (spOwnerTest A n).ok (onlyAt B o) ord o = (spOwnerTest A n).ok B ord o :=
  ok_onlyAt B ord o _ (spFits_onlyAt B o A n)

variable {B} {o} {B' : ProverCoinCounts}

/-- Two books with the same entries at the owner: what a part spends of its coins is the same. -/
theorem spentBy_congr (h : aheadAt B' o = aheadAt B o) : B'.spentBy o p = B.spentBy o p := by
  rw [← spentBy_onlyAt B', ← spentBy_onlyAt B]
  unfold ProverCoinCounts.spentBy onlyAt
  rw [h]

/-- And what else of them is known at a part. -/
theorem knownBy_congr (h : aheadAt B' o = aheadAt B o) :
    B'.knownBy ord o p = B.knownBy ord o p := by
  rw [← knownBy_onlyAt B', ← knownBy_onlyAt B]
  unfold ProverCoinCounts.knownBy onlyAt
  rw [h]

/-- And the entries that spend of them. -/
theorem spendersOf_congr (h : aheadAt B' o = aheadAt B o) : spendersOf B' o = spendersOf B o := by
  rw [← spendersOf_onlyAt B', ← spendersOf_onlyAt B]
  unfold spendersOf onlyAt
  rw [h]

/-- **The short test says the same at both.** -/
theorem wholeOrSpent_congr (h : aheadAt B' o = aheadAt B o) (st ct : Due)
    (ms : List (Due × Due)) : wholeOrSpent st ct ms B' o = wholeOrSpent st ct ms B o := by
  unfold wholeOrSpent
  rw [spendersOf_congr h, h]

/-- **Every test whose fits says the same at both says the same at both.** -/
theorem ownerOk_congr (h : aheadAt B' o = aheadAt B o) (t : OwnerTest)
    (hf : t.fits B' ord o = t.fits B ord o) : t.ok B' ord o = t.ok B ord o := by
  have key : ∀ C : ProverCoinCounts, t.ok C ord o = (t.fits C ord o &&
                  ({ t with fits := fun _ _ _ => true } : OwnerTest).ok
                    (⟨[], [], [], aheadAt C o, []⟩ : ProverCoinCounts) ord o) := fun C => by
    have h1 := ok_onlyAt C ord o { t with fits := fun _ _ _ => true } rfl
    have h2 : ({ t with fits := fun _ _ _ => true } : OwnerTest).ok (onlyAt C o) ord o =
        ({ t with fits := fun _ _ _ => true } : OwnerTest).ok
          (⟨[], [], [], aheadAt C o, []⟩ : ProverCoinCounts) ord o := rfl
    rw [← h2, h1]
    unfold OwnerTest.ok
    rw [Bool.true_and]
  rw [key B', key B, hf, h]

/-- spFits says the same at both. -/
theorem spFits_congr (h : aheadAt B' o = aheadAt B o) (A : SendPub) (n : Nat) :
    spFits A n B' o = spFits A n B o := by
  rw [← spFits_onlyAt B', ← spFits_onlyAt B]
  unfold spFits oneSpender spendersOf withinCount onlyAt
  rw [h]

/-- **The test for the part at "send o_omega" says the same at both**: ownerOk_congr, called. -/
theorem spOwner_ok_congr (h : aheadAt B' o = aheadAt B o) (A : SendPub) (n : Nat) :
    (spOwnerTest A n).ok B' ord o = (spOwnerTest A n).ok B ord o :=
  ownerOk_congr ord h _ (spFits_congr h A n)

/-- The entries that spend of an owner's coins, of the entries at the owner. -/
theorem spenders_of_aheadAt (B : ProverCoinCounts) (o : Addr) :
    spendersOf B o = (aheadAt B o).filter (·.once) := by
  unfold spendersOf aheadAt
  rw [List.filter_filter]

/-- What is known at a part, of the entries at the owner. -/
theorem knownBy_of_aheadAt (B : ProverCoinCounts) (ord : List Place) (o p : Addr) :
    B.knownBy ord o p = (aheadAt B o).filter fun e =>
      !(e.spender == p && e.once) && (e.spender == p || e.spender.before ord p) := by
  unfold ProverCoinCounts.knownBy aheadAt
  rw [List.filter_filter]
  congr 1
  funext e
  simp only [Bool.and_assoc, Bool.and_comm]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.filter_onlyAt
#print axioms ProofFile.Honest.K14.spentBy_onlyAt
#print axioms ProofFile.Honest.K14.knownBy_onlyAt
#print axioms ProofFile.Honest.K14.ok_onlyAt
#print axioms ProofFile.Honest.K14.spendersOf_onlyAt
#print axioms ProofFile.Honest.K14.withinCount_onlyAt
#print axioms ProofFile.Honest.K14.spFits_onlyAt
#print axioms ProofFile.Honest.K14.spOwner_ok_onlyAt
#print axioms ProofFile.Honest.K14.spentBy_congr
#print axioms ProofFile.Honest.K14.knownBy_congr
#print axioms ProofFile.Honest.K14.spendersOf_congr
#print axioms ProofFile.Honest.K14.wholeOrSpent_congr
#print axioms ProofFile.Honest.K14.ownerOk_congr
#print axioms ProofFile.Honest.K14.spFits_congr
#print axioms ProofFile.Honest.K14.spOwner_ok_congr
#print axioms ProofFile.Honest.K14.spenders_of_aheadAt
#print axioms ProofFile.Honest.K14.knownBy_of_aheadAt
