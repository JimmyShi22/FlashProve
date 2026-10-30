-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/ClearNothing.lean: where no message has a mask row and no table is sent along,
the condition on the book (BookClearAny) holds exactly if the owner's entries lie within the sending
part's coins and no address spends a coin of the owner.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. "Spent" against
"carried": the field once of the structure Ahead (Johnson/Desc/ProofFile/Honest/Frame.lean).
BookClearAny is defined in Johnson/SendSim/At/BookWide.lean. A table is sent along where a message
of the sending is the fresh mask table of a later fold: ride k = some R (the structure Ride,
Johnson/Desc/ProofFile/Honest/K1/Coins.lean). Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has.
  clearAny_iff_nothing   Let P be the public numbers of a place, and let ride say which tables are
        sent along. Suppose that every message of P has 0 mask rows, and ride k = none for all k.
        Let Bk be any book, ord any order and o any owner. Then BookClearAny P ride Bk ord o holds
        if and only if two things hold. (1) Every entry of Bk with the owner o lies within the count
        of coins of the sending part (WithinTakes). (2) For every address p, the entries by which p
        spends coins of o cover no coin of the extension field and none of the base field
        (eAll (Bk.spentBy o p) = ∅ and fAll (Bk.spentBy o p) = ∅).
  spenderAny_iff_nothing   The same equivalence at one address p, without the clause on the count.
  counts_zero_of_nothing   If a list of entries covers no coin of either field, each of its entries
        has length 0 in both fields.
  Small.noMask_padInMain, Small.noRide_none   The two premises hold at the small example
        placePadInMain (Johnson/SendSim/At/SmallPlaceBase.lean) with no table sent along, so the
        lemma is not vacuous.

How it fits. Some statements give the field fresh (Spec.sendFreshAtWide) or the whole structure Good
(Spec.goodSeatedWide, both in Johnson/SendSim/At/BookWide.lean), and others do so at the
description's members (Johnson/SendSim/Seat/). Each takes as a premise BookClearAny or the narrower
BookClear, which implies it (bookClearAny_of_clear). Spec.sendFreshAtPWide
(Johnson/SendSim/At/FreshWide.lean) takes the condition at one spender, SpenderClearAny, and
spenderAny_iff_nothing covers it. By clearAny_iff_nothing, at a place that meets the two premises,
the premise on the book holds only at a book in which nobody spends a coin of this owner. By
counts_zero_of_nothing every run that the equation of fresh samples anew then has length 0, so that
equation holds trivially. With no spending entry at all that is proved (nothingSpent,
Johnson/SendSim/At/NothingSpent.lean); with spending entries of length 0 it is by inspection, not
proved. So at such a place these statements apply only where no coin of this owner is spent: by any
address for Spec.sendFreshAtWide and Spec.goodSeatedWide, by the one spender p for
Spec.sendFreshAtPWide. The lemma is not one of the release's goal statements.

The other names.
  freeNo_of_noMask   a message with 0 mask rows has no free mask entry.
  eOf_empty_of_all, fOf_empty_of_all   if a list of entries covers no coin of a field, so does each
                     of its entries.
  apart_of_nothing   such entries are pairwise disjoint.

Why the right-hand side speaks of coins and not of entries. An entry of length 0 in both fields is
an entry by which p spends, yet it cuts off no coin. BookClearAny allows such entries: they meet
every clause of MaskSpender.

Limits.
The two premises are about P and ride alone. That they hold at a given place of the release's
protocol is not proved here; in this file they are proved at one small example. At each segment's
reads and digits on the proof file's first chain, the two premises follow from a test on the
request's shape that accepts at the full-size value. So if the maker returns and Z.first.shape is
that value, the equivalence holds there (clear_at_later_open,
Johnson/SendSim/Seat/LotsTestTie.lean); that premise is not proved.
The lemma is about the premise on the book. It does not say whether the equation of fresh holds or
fails at a book in which somebody does spend. At the small example the equation at the rows
(the equation that Spec.rowsFreshWide concludes) is false at two such books (said here without a
theorem).
The premise on ride cannot be dropped. With a table sent along, BookClearAny holds at a book in
which one address spends that table's coins, whatever the mask rows are (said here without a
theorem), so the equivalence fails there. That it fails is not stated as a lemma.
-/
import Johnson.SendSim.At.BookWide
import Johnson.SendSim.At.SmallPlaceBase

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- A message with 0 mask rows has no free mask entry. -/
theorem freeNo_of_noMask (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (h : (shapeAt P k).maskRows = 0) : freeNo P ride k = ∅ := by
  have e : OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows (maskCodeAt P k).ell
      (shapeAt P k).answers = 0 := by
    rw [h]
    simp [OnBytes.Send.freeMaskEntries]
  unfold freeNo
  rw [e, Finset.range_zero, Finset.image_empty]

/-- If a list of entries covers no coin of the extension field, so does each of its entries. -/
theorem eOf_empty_of_all : ∀ {l : List Ahead}, eAll l = ∅ → ∀ e ∈ l, eOf e = ∅
  | [], _, _, he => by cases he
  | a :: l, h, e, he => by
    have h' : eOf a ∪ eAll l = ∅ := h
    obtain ⟨h1, h2⟩ := Finset.union_eq_empty.1 h'
    rcases List.mem_cons.1 he with h3 | h3
    · rw [h3]
      exact h1
    · exact eOf_empty_of_all h2 e h3

/-- The same for the base field. -/
theorem fOf_empty_of_all : ∀ {l : List Ahead}, fAll l = ∅ → ∀ e ∈ l, fOf e = ∅
  | [], _, _, he => by cases he
  | a :: l, h, e, he => by
    have h' : fOf a ∪ fAll l = ∅ := h
    obtain ⟨h1, h2⟩ := Finset.union_eq_empty.1 h'
    rcases List.mem_cons.1 he with h3 | h3
    · rw [h3]
      exact h1
    · exact fOf_empty_of_all h2 e h3

/-- If a list of entries covers no coin of either field, each entry has length 0 in both fields. -/
theorem counts_zero_of_nothing {l : List Ahead} (hE : eAll l = ∅) (hF : fAll l = ∅) (e : Ahead)
    (he : e ∈ l) : e.count.e = 0 ∧ e.count.f = 0 := by
  have h1 := Finset.Ico_eq_empty_iff.1 (eOf_empty_of_all hE e he)
  have h2 := Finset.Ico_eq_empty_iff.1 (fOf_empty_of_all hF e he)
  omega

/-- Entries that cover no coin of the extension field are pairwise disjoint there. -/
theorem apart_of_nothing : ∀ {l : List Ahead}, eAll l = ∅ →
    l.Pairwise fun e e' => Disjoint (eOf e) (eOf e')
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    have h' : eOf a ∪ eAll l = ∅ := h
    obtain ⟨h1, h2⟩ := Finset.union_eq_empty.1 h'
    refine List.pairwise_cons.2 ⟨fun b _ => ?_, apart_of_nothing h2⟩
    rw [h1]
    exact Finset.disjoint_empty_left _

/-- At one address: where no message has a mask row and no table is sent along, the address meets
the condition on a spender exactly if the entries by which it spends cover no coin. -/
theorem spenderAny_iff_nothing {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts}
    {ord : List Place} {o p : Addr} (hm : ∀ k < P.sent.size, (shapeAt P k).maskRows = 0)
    (hr : ∀ k, ride k = none) :
    SpenderClearAny P ride Bk ord o p ↔
      eAll (Bk.spentBy o p) = ∅ ∧ fAll (Bk.spentBy o p) = ∅ := by
  constructor
  · rintro (h0 | hM | hF)
    · rw [h0]
      exact ⟨rfl, rfl⟩
    · refine ⟨Finset.eq_empty_of_forall_notMem fun n hn => ?_, hM.noF⟩
      obtain ⟨k, hk, _, _, hfree⟩ := hM.free n hn
      rw [freeNo_of_noMask P ride k (hm k hk)] at hfree
      exact absurd hfree (Finset.notMem_empty n)
    · obtain ⟨k, R, _, _, hR, _⟩ := hF.one
      rw [hr k] at hR
      cases hR
  · rintro ⟨hE, hFz⟩
    refine Or.inr (Or.inl ⟨hFz, ?_, apart_of_nothing hE, ?_, ?_⟩)
    · intro n hn
      rw [hE] at hn
      exact absurd hn (Finset.notMem_empty n)
    · rw [hE]
      exact Finset.disjoint_empty_left _
    · intro k j _ _ _ _ hs
      rw [hE] at hs
      exact absurd hs (Finset.notMem_empty _)

/-- **Where no message has a mask row and no table is sent along, the book meets BookClearAny at an
owner exactly if its entries with that owner lie within the count and no address spends a coin of
the owner.** -/
theorem clearAny_iff_nothing {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts}
    {ord : List Place} {o : Addr} (hm : ∀ k < P.sent.size, (shapeAt P k).maskRows = 0)
    (hr : ∀ k, ride k = none) :
    BookClearAny P ride Bk ord o ↔
      WithinTakes P ride Bk o ∧ ∀ p, eAll (Bk.spentBy o p) = ∅ ∧ fAll (Bk.spentBy o p) = ∅ := by
  unfold BookClearAny
  exact and_congr_right fun _ => forall_congr' fun _ => spenderAny_iff_nothing hm hr

namespace Small

/-- The first premise of clearAny_iff_nothing holds at the small example placePadInMain. -/
theorem noMask_padInMain : ∀ k < placePadInMain.sent.size,
    (shapeAt placePadInMain k).maskRows = 0 := by
  intro k hk
  have hk0 : k = 0 := Nat.lt_one_iff.1 hk
  subst hk0
  rfl

/-- The second premise holds where no table is sent along. -/
theorem noRide_none : ∀ k, noRide k = none := fun _ => rfl

end Small

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.freeNo_of_noMask
#print axioms OnBytes.SendSim.At.counts_zero_of_nothing
#print axioms OnBytes.SendSim.At.apart_of_nothing
#print axioms OnBytes.SendSim.At.spenderAny_iff_nothing
#print axioms OnBytes.SendSim.At.clearAny_iff_nothing
#print axioms OnBytes.SendSim.At.Small.noMask_padInMain
#print axioms OnBytes.SendSim.At.Small.noRide_none
