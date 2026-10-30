-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FastBook.lean: a public test on a book at a sender that walks the book's entries
a few times, and the proof that the wider condition on the book, BookClearAny, holds at the sender
wherever the test accepts.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. P and ride are a sender's public numbers and which table is sent along; Bk is
any book, ord any order of places, o any address.
  clearAny_of_fast  If fastOkB P ride Bk ord o = true, then BookClearAny P ride Bk ord o
                    (BookWide.lean): the premise of the field fresh at the sender whose address is
                    o.
  fastOkB           The test. S is the list of the spending entries on o's coins, in the book's
                    order (spendsOf); C is the list of the carried ones (carriesOf). It accepts if:
                    (1) Every entry on o's coins is within the sender's number of coins (withinB).
                    (2) Every entry of S cuts off no coin of the base field. Its run of the
                        extension field lies within the free mask entries of one sampled message
                        whose table is not sent along (freeAtB), or it is exactly the coefficient
                        coins of one table that is sent along (foldAtB).
                    (3) Along S each run ends before the next begins (risingB).
                    (4) Every run of S is apart from every run of allGuard: for every message, its
                        pads (where it has mask rows) and the tails of all its mask rows.
                    (5) The spender of an entry of S that is not of the first sort in (2) has no
                        other entry in S.
                    (6) Let c be an entry of C and s an entry of S, where c goes to s's spender or
                        to an address in front of it. Then c's run is apart from s's run. It is also
                        apart from guardOf s: the pads (where it has mask rows) and all mask rows'
                        tails of every message whose spendable coins s's run meets.

How it fits. The tests bookClearAnyB (WideTest.lean) and ownerOkB (GuardTest.lean) accept exactly
where BookClearAny holds (bookClearAnyB_iff, BookWide.lean; ownerOkB_iff, GuardTestTie.lean), but
they go address by address, and at each address through all entries. At a book with thousands of
spending entries on one sender's coins that is expected to be too much for an evaluation in Lean's
kernel. For a fixed number of carried entries, messages, mask rows and answers, this test walks the
book a fixed number of times, apart from clause (5) at the entries of the second sort. In this
folder it is evaluated at no book. Statements on public data: no distribution is named. Meant as
steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index
privacy from them. Not one of the release's goal statements.

The other names.
  apart2, runE, risingB
                    two runs share no number; an entry's run of the extension field; each run of a
                    list ends before the next begins.
  touchB, msgGuard  an entry's run meets the coins of a message's mask table that can be spent; a
                    message's pads, where it has mask rows, and all its mask rows' tails, as runs.
  spentBy_eq, mem_spentBy, mem_knownBy
                    the frame's lists of what an address spends and of what is known there, through
                    S and C.

Limits. The test is sufficient, not necessary: it rejects books at which BookClearAny holds (by
inspection, not proved, as all comparisons under Limits). Two ways in which it asks more matter at a
job that fits its place. It asks that the spending runs rise in the book's order, also across
spenders: so it counts every other spender's entries as known, whatever ord says, where BookClearAny
counts those of spenders in front alone. And it takes all mask rows' tails of a message where
BookClearAny names two rows. It also asks that the spending runs are apart from the pads and tails
of all messages, takes a message's pads also at a table that is sent along, and asks one message for
a whole entry.
An entry that spends no coin, alone at its spender or beside entries of free mask entries, passes
BookClearAny wherever it starts within the sender's coins; the test accepts it only where clauses
(2) and (3) do.
Where no entry spends o's coins, clauses (2) to (6) are empty, and the test accepts exactly if
clause (1) does: so at a book that lists nobody, and at an owner whose carried entries are within
the count. BookClearAny holds in just these cases too.
With a list ord that lacks places, BookClearAny and clause (6) are other conditions than with a
description's order (orderOf): they may ask more or less. A place that is not in the list counts as
the last. Under the empty list no part is in front of a part at another place. Clauses (1) to (5) do
not read ord.
That the test can accept at a sender that sends a table along, at a book in which that sender's
coins are spent, and can reject, is checked by evaluation in Lean's kernel
(multiplicities_fast_full, messageW_fast_full, owned_full, fast_full_no, E2E/OfflineClearLines.lean;
key_fast, key_fast_no, AtFullSide/K1/KeyBookClear.lean).
The test reads no description: whether the addresses are parts of a prover, and whether ord is a
description's order of places, is the caller's. All limits of BookWide.lean.
-/
import Johnson.SendSim.At.GuardTest
import Johnson.SendSim.At.BookWide

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-! ## Runs -/

/-- Two runs (first number, length) share no number. -/
def apart2 (x y : Nat × Nat) : Bool :=
  x.2 == 0 || y.2 == 0 || decide (x.1 + x.2 ≤ y.1) || decide (y.1 + y.2 ≤ x.1)

theorem apart2_spec {x y : Nat × Nat} (h : apart2 x y = true) {n : Nat}
    (hx : x.1 ≤ n ∧ n < x.1 + x.2) (hy : y.1 ≤ n ∧ n < y.1 + y.2) : False := by
  unfold apart2 at h
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

theorem touch_of_common {x y : Nat × Nat} {n : Nat} (hx : x.1 ≤ n ∧ n < x.1 + x.2)
    (hy : y.1 ≤ n ∧ n < y.1 + y.2) : apart2 x y = false := by
  cases h : apart2 x y
  · rfl
  · exact (apart2_spec h hx hy).elim

/-- An entry's run of coins of the extension field. -/
def runE (e : Ahead) : Nat × Nat := (e.start.e, e.count.e)

theorem mem_eOf {e : Ahead} {n : Nat} :
    n ∈ eOf e ↔ (runE e).1 ≤ n ∧ n < (runE e).1 + (runE e).2 := by
  simp [eOf, runE, Finset.mem_Ico]

theorem exists_of_mem_eAll : ∀ {l : List Ahead} {n : Nat}, n ∈ eAll l → ∃ e ∈ l, n ∈ eOf e
  | [], _, h => by simp [eAll] at h
  | a :: l, n, h => by
    have h' : n ∈ eOf a ∪ eAll l := h
    rcases Finset.mem_union.1 h' with h1 | h1
    · exact ⟨a, List.mem_cons_self .., h1⟩
    · obtain ⟨e, he, hn⟩ := exists_of_mem_eAll h1
      exact ⟨e, List.mem_cons_of_mem _ he, hn⟩

theorem mem_eAll_of {l : List Ahead} {e : Ahead} (he : e ∈ l) {n : Nat} (hn : n ∈ eOf e) :
    n ∈ eAll l := by
  induction l with
  | nil => cases he
  | cons a l ih =>
    show n ∈ eOf a ∪ eAll l
    rcases List.mem_cons.1 he with rfl | h
    · exact Finset.mem_union_left _ hn
    · exact Finset.mem_union_right _ (ih h)

/-- Each run ends before the next begins. -/
def risingB : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | x :: y :: l => decide (x.1 + x.2 ≤ y.1) && risingB (y :: l)

theorem rising_head : ∀ {l : List (Nat × Nat)} {x : Nat × Nat}, risingB (x :: l) = true →
    ∀ z ∈ l, x.1 + x.2 ≤ z.1
  | [], _, _, _, hz => by cases hz
  | y :: l, x, h, z, hz => by
    simp only [risingB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hz with rfl | hz'
    · exact h.1
    · have := rising_head h.2 z hz'
      omega

theorem rising_pairwise : ∀ {l : List (Nat × Nat)}, risingB l = true →
    l.Pairwise fun x z => x.1 + x.2 ≤ z.1
  | [], _ => List.Pairwise.nil
  | [x], _ => List.pairwise_singleton _ _
  | x :: y :: l, h => by
    refine List.Pairwise.cons (rising_head h) (rising_pairwise ?_)
    simp only [risingB, Bool.and_eq_true] at h
    exact h.2

variable (P : K1.Par) (ride : Nat → Option Ride)

/-! ## The test -/

/-- The number of message number k's free mask entries. -/
abbrev freeCount (k : Nat) : Nat :=
  OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows (maskCodeAt P k).ell (shapeAt P k).answers

/-- The entry's run lies within the free mask entries of message number k, a sampled message whose
table is not sent along. -/
def freeAtB (k : Nat) (e : Ahead) : Bool :=
  (ride k).isNone && (shapeAt P k).answers != 0 && decide (maskStart P ride k ≤ e.start.e) &&
    decide (e.start.e + e.count.e ≤ maskStart P ride k + freeCount P k)

/-- The entry is exactly the coefficient coins of the table that is sent along as message number
k. -/
def foldAtB (k : Nat) (e : Ahead) : Bool :=
  match ride k with
  | some R => (e.count == ⟨0, R.count⟩) && (e.start.e == maskStart P ride k)
  | none => false

/-- The entry's run meets the coins of message number k's mask table that can be spent. -/
def touchB (k : Nat) (e : Ahead) : Bool :=
  match ride k with
  | none => (shapeAt P k).answers != 0 && !apart2 (runE e) (maskStart P ride k, freeCount P k)
  | some R => !apart2 (runE e) (maskStart P ride k, R.count)

/-- The pads of message number k's sample, where it has mask rows, and the tails of all its mask
rows, as runs. Without mask rows padNo names no pad. -/
def msgGuard (k : Nat) : List (Nat × Nat) :=
  (if (shapeAt P k).maskRows == 0 then [] else padRuns P ride k) ++
    (List.range (shapeAt P k).maskRows).map fun r => tailRun P ride k r

/-- The like for all messages. -/
def allGuard : List (Nat × Nat) := (List.range P.sent.size).flatMap fun k => msgGuard P ride k

/-- The like for the messages whose mask tables the entry's run meets. -/
def guardOf (e : Ahead) : List (Nat × Nat) :=
  (List.range P.sent.size).flatMap fun k => if touchB P ride k e then msgGuard P ride k else []

/-- The spending entries on an owner's coins, in the book's order. -/
def spendsOf (Bk : ProverCoinCounts) (o : Addr) : List Ahead := Bk.ahead.filter fun e => e.owner == o && e.once

/-- The carried entries on an owner's coins. -/
def carriesOf (Bk : ProverCoinCounts) (o : Addr) : List Ahead :=
  Bk.ahead.filter fun e => e.owner == o && !e.once

/-- **A test on the book at a sender that walks the spending entries a few times.** -/
def fastOkB (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  withinB P ride Bk o &&
  ((spendsOf Bk o).all fun s => s.count.f == 0 &&
    (List.range P.sent.size).any fun k => freeAtB P ride k s || foldAtB P ride k s) &&
  risingB ((spendsOf Bk o).map runE) &&
  ((spendsOf Bk o).all fun s => (allGuard P ride).all fun t => apart2 (runE s) t) &&
  ((spendsOf Bk o).all fun s => ((List.range P.sent.size).any fun k => freeAtB P ride k s) ||
    ((spendsOf Bk o).filter fun s' => s'.spender == s.spender).length == 1) &&
  ((carriesOf Bk o).all fun c => (spendsOf Bk o).all fun s =>
    !(c.spender == s.spender || c.spender.before ord s.spender) ||
      (apart2 (runE c) (runE s) && (guardOf P ride s).all fun t => apart2 (runE c) t))

/-! ## What it gives -/

variable {P ride}

/-- What an address spends of an owner's coins: the owner's spending entries with that spender. -/
theorem spentBy_eq (Bk : ProverCoinCounts) (o p : Addr) :
    Bk.spentBy o p = (spendsOf Bk o).filter fun s => s.spender == p := by
  unfold ProverCoinCounts.spentBy spendsOf
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  cases e.owner == o <;> cases e.spender == p <;> cases e.once <;> rfl

/-- An entry by which p spends is one of the owner's spending entries, and p is its spender. -/
theorem mem_spentBy {Bk : ProverCoinCounts} {o p : Addr} {s : Ahead} (h : s ∈ Bk.spentBy o p) :
    s ∈ spendsOf Bk o ∧ s.spender = p := by
  rw [spentBy_eq] at h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  exact ⟨h1, beq_iff_eq.1 h2⟩

/-- An entry that is known at p is a spending entry of another spender, or a carried entry that goes
to p or to an address in front of p. -/
theorem mem_knownBy {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} {e : Ahead}
    (h : e ∈ Bk.knownBy ord o p) :
    (e ∈ spendsOf Bk o ∧ e.spender ≠ p) ∨
      (e ∈ carriesOf Bk o ∧ (e.spender == p || e.spender.before ord p) = true) := by
  unfold ProverCoinCounts.knownBy at h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨ho, hn⟩, hb⟩ := h2
  cases hc : e.once
  · exact Or.inr ⟨List.mem_filter.2 ⟨h1, by simp [ho, hc]⟩, hb⟩
  · refine Or.inl ⟨List.mem_filter.2 ⟨h1, by simp [ho, hc]⟩, fun he => ?_⟩
    simp [he, hc] at hn

theorem guardOf_sub {e : Ahead} {t : Nat × Nat} (h : t ∈ guardOf P ride e) :
    t ∈ allGuard P ride := by
  obtain ⟨k, hk, ht⟩ := List.mem_flatMap.1 h
  refine List.mem_flatMap.2 ⟨k, hk, ?_⟩
  split at ht
  · exact ht
  · cases ht

theorem guard_of_touch {e : Ahead} {k : Nat} (hk : k < P.sent.size)
    (h : touchB P ride k e = true) {t : Nat × Nat} (ht : t ∈ msgGuard P ride k) :
    t ∈ guardOf P ride e :=
  List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by rw [if_pos h]; exact ht⟩

theorem pad_in_guard {k i : Nat} (hrows : 0 < (shapeAt P k).maskRows)
    (hi : i < (shapeAt P k).answers) : (padNo P ride k i, 1) ∈ msgGuard P ride k := by
  unfold msgGuard
  rw [if_neg (by simp only [beq_iff_eq]; omega)]
  exact List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem tail_in_guard {k r : Nat} (hr : r < (shapeAt P k).maskRows) :
    tailRun P ride k r ∈ msgGuard P ride k :=
  List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩)

theorem tailNo_in_tailRun (k r q : Nat) (hq : q < (maskCodeAt P k).r) :
    (tailRun P ride k r).1 ≤ maskTailNo P ride k r q ∧
      maskTailNo P ride k r q < (tailRun P ride k r).1 + (tailRun P ride k r).2 := by
  unfold tailRun maskTailNo
  constructor <;> simp only <;> omega

/-- **Where the test accepts, BookClearAny holds at the sender.** -/
theorem clearAny_of_fast {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (h : fastOkB P ride Bk ord o = true) : BookClearAny P ride Bk ord o := by
  unfold fastOkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hW, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h1 := List.all_eq_true.1 h1
  have h3 := List.all_eq_true.1 h3
  have h4 := List.all_eq_true.1 h4
  have h5 := List.all_eq_true.1 h5
  -- the spending entries are pairwise apart
  have hpw : (spendsOf Bk o).Pairwise fun a b => Disjoint (eOf a) (eOf b) := by
    have := List.pairwise_map.1 (rising_pairwise h2)
    refine this.imp fun {a b} hab => Finset.disjoint_left.2 fun n ha hb => ?_
    have ha' := mem_eOf.1 ha
    have hb' := mem_eOf.1 hb
    omega
  refine ⟨within_of_test P ride hW, fun p => ?_⟩
  -- what is spent at p is apart from what is known there
  have K1 : ∀ s ∈ Bk.spentBy o p, ∀ e ∈ Bk.knownBy ord o p, ∀ n, n ∈ eOf s → n ∉ eOf e := by
    intro s hs e he n hn hn'
    obtain ⟨hsS, hsp⟩ := mem_spentBy hs
    rcases mem_knownBy he with ⟨heS, hep⟩ | ⟨heC, heb⟩
    · have hne : s ≠ e := fun hse => hep (hse ▸ hsp)
      exact Finset.disjoint_left.1
        (hpw.forall (fun _ _ hd => hd.symm) hsS heS hne) hn hn'
    · have := List.all_eq_true.1 (h5 e heC) s hsS
      rw [hsp, heb] at this
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
      exact apart2_spec this.1 (mem_eOf.1 hn') (mem_eOf.1 hn)
  -- the guard of what is spent at p is apart from what is known there
  have K2 : ∀ s ∈ Bk.spentBy o p, ∀ t ∈ guardOf P ride s, ∀ n, (t.1 ≤ n ∧ n < t.1 + t.2) →
      n ∉ eAll (Bk.knownBy ord o p) := by
    intro s hs t ht n hn hmem
    obtain ⟨e, he, hne⟩ := exists_of_mem_eAll hmem
    obtain ⟨hsS, hsp⟩ := mem_spentBy hs
    rcases mem_knownBy he with ⟨heS, -⟩ | ⟨heC, heb⟩
    · exact apart2_spec (List.all_eq_true.1 (h3 e heS) t (guardOf_sub ht)) (mem_eOf.1 hne) hn
    · have := List.all_eq_true.1 (h5 e heC) s hsS
      rw [hsp, heb] at this
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
      exact apart2_spec (List.all_eq_true.1 this.2 t ht) (mem_eOf.1 hne) hn
  have hun : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p)) :=
    Finset.disjoint_left.2 fun n hn hn' => by
      obtain ⟨s, hs, h6⟩ := exists_of_mem_eAll hn
      obtain ⟨e, he, h7⟩ := exists_of_mem_eAll hn'
      exact K1 s hs e he n h6 h7
  by_cases hall : ∀ s ∈ Bk.spentBy o p, ((List.range P.sent.size).any fun k =>
      freeAtB P ride k s) = true
  · -- free mask entries alone
    refine Or.inr (Or.inl ⟨?_, ?_, ?_, hun, ?_⟩)
    · refine fAll_of_test (List.all_eq_true.2 fun s hs => ?_)
      have := h1 s (mem_spentBy hs).1
      rw [Bool.and_eq_true] at this
      exact this.1
    · intro n hn
      obtain ⟨s, hs, h6⟩ := exists_of_mem_eAll hn
      obtain ⟨k, hk, hf⟩ := List.any_eq_true.1 (hall s hs)
      unfold freeAtB at hf
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq,
        decide_eq_true_eq] at hf
      obtain ⟨⟨⟨hr, ha⟩, hlo⟩, hhi⟩ := hf
      have h8 := mem_eOf.1 h6
      simp only [runE] at h8
      exact ⟨k, List.mem_range.1 hk, hr, ha, mem_freeNo P ride (by omega)
        (Nat.lt_of_lt_of_le h8.2 hhi)⟩
    · rw [spentBy_eq]
      exact hpw.sublist List.filter_sublist
    · intro k j hk hr ha hfree hmem
      obtain ⟨s, hs, h6⟩ := exists_of_mem_eAll hmem
      have hj := lt_of_mem_freeNo P ride hfree
      have hrows : 0 < (shapeAt P k).maskRows := by
        rcases Nat.eq_zero_or_pos (shapeAt P k).maskRows with h0 | h0
        · rw [h0] at hj
          simp [OnBytes.Send.freeMaskEntries] at hj
        · exact h0
      have ht : touchB P ride k s = true := by
        unfold touchB
        rw [hr]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
        exact ⟨ha, touch_of_common (mem_eOf.1 h6)
          ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩⟩
      refine ⟨fun i hi => K2 s hs _ (guard_of_touch hk ht (pad_in_guard hrows hi)) _
        ⟨Nat.le_refl _, Nat.lt_succ_self _⟩, fun q hq => ⟨?_, ?_⟩⟩
      · exact K2 s hs _ (guard_of_touch hk ht (tail_in_guard (Nat.mod_lt _ hrows))) _
          (tailNo_in_tailRun k _ q hq)
      · exact K2 s hs _ (guard_of_touch hk ht (tail_in_guard (Nat.sub_lt hrows Nat.one_pos))) _
          (tailNo_in_tailRun k _ q hq)
  · -- one table that is sent along
    obtain ⟨s, hall⟩ := not_forall.1 hall
    obtain ⟨hs, hnf⟩ := _root_.not_imp.1 hall
    obtain ⟨hsS, hsp⟩ := mem_spentBy hs
    have hone : Bk.spentBy o p = [s] := by
      have h6 := h4 s hsS
      rw [Bool.or_eq_true] at h6
      rcases h6 with h6 | h6
      · exact (hnf h6).elim
      · rw [hsp, ← spentBy_eq] at h6
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 (beq_iff_eq.1 h6)
        rw [ha] at hs ⊢
        rw [List.mem_singleton.1 hs]
    have h7 := h1 s hsS
    rw [Bool.and_eq_true] at h7
    obtain ⟨k, hk, hf⟩ := List.any_eq_true.1 h7.2
    have hfold : foldAtB P ride k s = true := by
      rcases Bool.or_eq_true _ _ ▸ hf with h8 | h8
      · exact (hnf (List.any_eq_true.2 ⟨k, hk, h8⟩)).elim
      · exact h8
    unfold foldAtB at hfold
    cases hr : ride k with
    | none => rw [hr] at hfold; cases hfold
    | some R =>
      rw [hr] at hfold
      simp only [Bool.and_eq_true, beq_iff_eq] at hfold
      have hk' := List.mem_range.1 hk
      have ht : touchB P ride k s = true := by
        unfold touchB
        rw [hr]
        simp only [Bool.not_eq_true']
        refine touch_of_common (n := maskStart P ride k) ?_ ?_
        · simp only [runE, hfold.1, hfold.2, Ride.count]
          omega
        · simp only [Ride.count]
          omega
      exact Or.inr (Or.inr ⟨⟨k, R, s, hk', hr, hone, hfold.1, hfold.2, fun r hr' q hq =>
        K2 s hs _ (guard_of_touch hk' ht (tail_in_guard hr')) _ (tailNo_in_tailRun k r q hq)⟩, hun⟩)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.clearAny_of_fast
