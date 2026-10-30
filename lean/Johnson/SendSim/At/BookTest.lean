-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/BookTest.lean: an executable test on a book's listed entries that accepts exactly
if the book is clear at the owner (BookClear), and such tests for one address (SpenderClear,
WithinAt).
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. Executable tests (Bool-valued definitions), and theorems on finite lists and
numbers, for all P, ride, books, orders and addresses.
  bookClearB, bookClearB_iff         The test at all addresses: every entry of the owner is within
                      the sender's number of coins, and each address that some entry names as its
                      spender passes spenderClearB. It accepts exactly if BookClear holds.
  spenderClearB, spenderClearB_iff   The test at one address: it spends nothing of the owner's
                      coins, or passes maskB, or passes foldB. It accepts exactly if SpenderClear
                      holds. So a rejection at a concrete book proves that the condition fails.
  withinAtB, withinAtB_iff           The test for WithinAt, on the entries that concern one address.
                      It accepts exactly if WithinAt holds.

Limits. The tests read only numbers of coins: no distribution and no value of a coin is named.
Nothing says that a book of the release passes. The cost of a test grows with the number of coins
that the entries hold.

How it fits. At/FilledBooks.lean evaluates them at made-up books by #guard lines. The tests for the
wider condition (Johnson/SendSim/At/WideTest.lean) are built on them.

The other names.
  inE, mem_eAll_iff   a number is in one of the runs of coins of the extension field that a list of
                      entries holds; that is membership in eAll.
  withinB, noFB, isFreeB, allE, apartB, clearB, maskB, foldB   the clauses of BookClear, MaskSpender
                      and FoldSpender, each as a test.
  bookClear_of_test, spenderClear_of_test   one direction of the two equivalences.

Notes: why a test is possible. BookClear quantifies over every address. A book lists finitely many
entries, and an address that no entry names as its spender spends nothing (spentBy_nil_of_not). So
the condition can be decided entry by entry.
-/
import Johnson.SendSim.At.Fresh

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- The number n is in one of the runs of coins of the extension field that the entries of l hold.
-/
def inE (l : List Ahead) (n : ℕ) : Bool :=
  l.any fun e => decide (e.start.e ≤ n) && decide (n < e.start.e + e.count.e)

theorem mem_eAll_iff (l : List Ahead) (n : ℕ) : n ∈ eAll l ↔ inE l n = true := by
  induction l with
  | nil => simp [eAll, inE]
  | cons e l ih =>
    have : eAll (e :: l) = eOf e ∪ eAll l := rfl
    rw [this, Finset.mem_union, ih]
    simp [inE, eOf, Finset.mem_Ico]

theorem not_mem_eAll {l : List Ahead} {n : ℕ} (h : inE l n = false) : n ∉ eAll l := fun hn => by
  rw [mem_eAll_iff, h] at hn
  cases hn

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- Test: every entry with the owner o is within the sender's number of coins (WithinTakes). -/
def withinB (Bk : ProverCoinCounts) (o : Addr) : Bool :=
  Bk.ahead.all fun e => !(e.owner == o) ||
    (decide (e.start.f + e.count.f ≤ (dueR P ride).f) &&
      decide (e.start.e + e.count.e ≤ (dueR P ride).e))

theorem within_of_test {Bk : ProverCoinCounts} {o : Addr} (h : withinB P ride Bk o = true) :
    WithinTakes P ride Bk o := by
  intro e he ho
  have := List.all_eq_true.1 h e he
  simpa [ho] using this

/-- Test: the entries that concern the address p, those by which it spends and the known ones, are
within the sender's number of coins. -/
def withinAtB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  (Bk.spentBy o p ++ Bk.knownBy ord o p).all fun e =>
    decide (e.start.f + e.count.f ≤ (dueR P ride).f) &&
      decide (e.start.e + e.count.e ≤ (dueR P ride).e)

/-- withinAtB accepts exactly if WithinAt holds. -/
theorem withinAtB_iff {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} :
    withinAtB P ride Bk ord o p = true ↔ WithinAt P ride Bk ord o p := by
  simp only [withinAtB, List.all_eq_true, List.mem_append, Bool.and_eq_true, decide_eq_true_eq]
  exact Iff.rfl

/-- Test: the entries of l hold no coin of the base field. -/
def noFB (l : List Ahead) : Bool := l.all fun e => e.count.f == 0

theorem fAll_of_test {l : List Ahead} (h : noFB l = true) : fAll l = ∅ := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have h' : e.count.f = 0 ∧ noFB l = true := by simpa [noFB] using h
    have : fAll (e :: l) = fOf e ∪ fAll l := rfl
    rw [this, ih h'.2, Finset.union_empty]
    simp [fOf, h'.1]

/-- Test: n is the number of a coin at a free entry of a sampled oracle message that is not sent
along. -/
def isFreeB (n : ℕ) : Bool :=
  (List.range P.sent.size).any fun k =>
    (ride k).isNone && ((shapeAt P k).answers != 0) && decide (maskStart P ride k ≤ n) &&
      decide (n < maskStart P ride k + OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows
        (maskCodeAt P k).ell (shapeAt P k).answers)

theorem mem_freeNo {k n : ℕ} (h₁ : maskStart P ride k ≤ n)
    (h₂ : n < maskStart P ride k + OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows
      (maskCodeAt P k).ell (shapeAt P k).answers) : n ∈ freeNo P ride k := by
  unfold freeNo
  refine Finset.mem_image.2 ⟨n - maskStart P ride k, Finset.mem_range.2 (by omega), by omega⟩

theorem lt_of_mem_freeNo {k j : ℕ} (h : maskStart P ride k + j ∈ freeNo P ride k) :
    j < OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows (maskCodeAt P k).ell
      (shapeAt P k).answers := by
  unfold freeNo at h
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h
  have : t = j := by omega
  exact this ▸ Finset.mem_range.1 ht

/-- Test: the number of every coin of the extension field that the entries of l hold passes f. -/
def allE (l : List Ahead) (f : ℕ → Bool) : Bool :=
  l.all fun e => (List.range e.count.e).all fun t => f (e.start.e + t)

theorem allE_spec {l : List Ahead} {f : ℕ → Bool} (h : allE l f = true) {n : ℕ}
    (hn : n ∈ eAll l) : f n = true := by
  rw [mem_eAll_iff] at hn
  obtain ⟨e, he, h2⟩ := List.any_eq_true.1 hn
  have h3 : e.start.e ≤ n ∧ n < e.start.e + e.count.e := by simpa using h2
  have := List.all_eq_true.1 (List.all_eq_true.1 h e he) (n - e.start.e)
    (List.mem_range.2 (by omega))
  rwa [show e.start.e + (n - e.start.e) = n by omega] at this

/-- Test: no two entries of the list share a coin of the extension field. -/
def apartB : List Ahead → Bool
  | [] => true
  | e :: l => (l.all fun e' => (List.range e.count.e).all fun t => !inE [e'] (e.start.e + t)) &&
      apartB l

theorem disjoint_of_all {e : Ahead} {l : List Ahead}
    (h : ((List.range e.count.e).all fun t => !inE l (e.start.e + t)) = true) :
    Disjoint (eOf e) (eAll l) := by
  rw [Finset.disjoint_left]
  intro n hn hl
  have h1 : e.start.e ≤ n ∧ n < e.start.e + e.count.e := by simpa [eOf] using hn
  have := List.all_eq_true.1 h (n - e.start.e) (List.mem_range.2 (by omega))
  rw [show e.start.e + (n - e.start.e) = n by omega, (mem_eAll_iff l n).1 hl] at this
  cases this

theorem eAll_one (e : Ahead) : eAll [e] = eOf e := by
  show eOf e ∪ ∅ = eOf e
  exact Finset.union_empty _

theorem apart_of_test : ∀ {l : List Ahead}, apartB l = true →
    l.Pairwise fun e e' => Disjoint (eOf e) (eOf e')
  | [], _ => List.Pairwise.nil
  | e :: l, h => by
    have h' : (l.all fun e' => (List.range e.count.e).all fun t => !inE [e'] (e.start.e + t)) =
        true ∧ apartB l = true := by simpa [apartB] using h
    refine List.Pairwise.cons (fun e' he' => ?_) (apart_of_test h'.2)
    have := disjoint_of_all (List.all_eq_true.1 h'.1 e' he')
    rwa [eAll_one] at this

theorem disjoint_of_allE {l l' : List Ahead} (h : allE l (fun n => !inE l' n) = true) :
    Disjoint (eAll l) (eAll l') := by
  rw [Finset.disjoint_left]
  intro n hn hl
  have := allE_spec h hn
  rw [(mem_eAll_iff l' n).1 hl] at this
  cases this

/-- Test for the field clear of MaskSpender, at the spent entries sp and the known entries kn: for
each oracle message that has a spent free entry, no pad of it is known, and no coin of the tail of
that entry's row or of the last mask row is known. -/
def clearB (sp kn : List Ahead) : Bool :=
  (List.range P.sent.size).all fun k => !((ride k).isNone && ((shapeAt P k).answers != 0)) ||
    (List.range (OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows (maskCodeAt P k).ell
      (shapeAt P k).answers)).all fun j =>
      !inE sp (maskStart P ride k + j) ||
        (((List.range (shapeAt P k).answers).all fun i => !inE kn (padNo P ride k i)) &&
          (List.range (maskCodeAt P k).r).all fun q =>
            !inE kn (maskTailNo P ride k (j % (shapeAt P k).maskRows) q) &&
              !inE kn (maskTailNo P ride k ((shapeAt P k).maskRows - 1) q))

/-- Test for MaskSpender: all five of its fields. -/
def maskB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  noFB (Bk.spentBy o p) && allE (Bk.spentBy o p) (isFreeB P ride) && apartB (Bk.spentBy o p) &&
    allE (Bk.spentBy o p) (fun n => !inE (Bk.knownBy ord o p) n) &&
    clearB P ride (Bk.spentBy o p) (Bk.knownBy ord o p)

theorem mask_of_test {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : maskB P ride Bk ord o p = true) : MaskSpender P ride Bk ord o p := by
  simp only [maskB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fAll_of_test h1, fun n hn => ?_, apart_of_test h3, disjoint_of_allE h4,
    fun k j hk hr ha hj hs => ?_⟩
  · obtain ⟨k, hk, hb⟩ := List.any_eq_true.1 (allE_spec h2 hn)
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      Option.isNone_iff_eq_none] at hb
    exact ⟨k, List.mem_range.1 hk, hb.1.1.1, hb.1.1.2, mem_freeNo P ride hb.1.2 hb.2⟩
  · have h6 := List.all_eq_true.1 h5 k (List.mem_range.2 hk)
    have hb : ((ride k).isNone && ((shapeAt P k).answers != 0)) = true := by simp [hr, ha]
    rw [hb, Bool.not_true, Bool.false_or] at h6
    have := List.all_eq_true.1 h6 j (List.mem_range.2 (lt_of_mem_freeNo P ride hj))
    rw [(mem_eAll_iff _ _).1 hs] at this
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    refine ⟨fun i hi => not_mem_eAll ?_, fun q hq => ?_⟩
    · simpa using List.all_eq_true.1 this.1 i (List.mem_range.2 hi)
    · have h7 := List.all_eq_true.1 this.2 q (List.mem_range.2 hq)
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h7
      exact ⟨not_mem_eAll h7.1, not_mem_eAll h7.2⟩

/-- Test for FoldSpender: both of its fields. -/
def foldB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  (match Bk.spentBy o p with
    | [e] => (List.range P.sent.size).any fun k =>
      match ride k with
      | some R => (R.h == 0) && (e.count == ⟨0, R.count⟩) && (e.start.e == maskStart P ride k) &&
          (List.range (shapeAt P k).maskRows).all fun r =>
            (List.range (maskCodeAt P k).r).all fun q =>
              !inE (Bk.knownBy ord o p) (maskTailNo P ride k r q)
      | none => false
    | _ => false) &&
    allE (Bk.spentBy o p) (fun n => !inE (Bk.knownBy ord o p) n)

theorem fold_of_test {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : foldB P ride Bk ord o p = true) : FoldSpender P ride Bk ord o p := by
  simp only [foldB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, disjoint_of_allE h2⟩
  match hs : Bk.spentBy o p, h1 with
  | [e], h1 =>
    obtain ⟨k, hk, hb⟩ := List.any_eq_true.1 h1
    match hr : ride k, hb with
    | some R, hb =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      refine ⟨k, R, e, List.mem_range.1 hk, hr, hb.1.1.1, rfl, hb.1.1.2, hb.1.2,
        fun r hr' q hq => not_mem_eAll ?_⟩
      simpa using List.all_eq_true.1 (List.all_eq_true.1 hb.2 r (List.mem_range.2 hr')) q
        (List.mem_range.2 hq)

/-- The test at one address p: it spends nothing of the owner's coins, or passes maskB, or passes
foldB. -/
def spenderClearB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  (Bk.spentBy o p).isEmpty || maskB P ride Bk ord o p || foldB P ride Bk ord o p

theorem spenderClear_of_test {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : spenderClearB P ride Bk ord o p = true) : SpenderClear P ride Bk ord o p := by
  simp only [spenderClearB, Bool.or_eq_true, List.isEmpty_iff] at h
  rcases h with (h0 | h1) | h2
  · exact Or.inl h0
  · exact Or.inr (Or.inl (mask_of_test P ride h1))
  · exact Or.inr (Or.inr (fold_of_test P ride h2))

/-- The test at all addresses: withinB, and spenderClearB at each address that some entry names as
its spender. -/
def bookClearB (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  withinB P ride Bk o && (Bk.ahead.map (·.spender)).all fun p => spenderClearB P ride Bk ord o p

/-- An address that no entry of the book names as its spender spends nothing. -/
theorem spentBy_nil_of_not {Bk : ProverCoinCounts} {o p : Addr} (h : p ∉ Bk.ahead.map (·.spender)) :
    Bk.spentBy o p = [] := by
  unfold ProverCoinCounts.spentBy
  refine List.filter_eq_nil_iff.2 fun e he hb => h (List.mem_map.2 ⟨e, he, ?_⟩)
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact hb.1.2

/-- If bookClearB accepts, BookClear holds. -/
theorem bookClear_of_test {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (h : bookClearB P ride Bk ord o = true) : BookClear P ride Bk ord o := by
  simp only [bookClearB, Bool.and_eq_true] at h
  refine ⟨within_of_test P ride h.1, fun p => ?_⟩
  by_cases hp : p ∈ Bk.ahead.map (·.spender)
  · exact spenderClear_of_test P ride (List.all_eq_true.1 h.2 p hp)
  · exact Or.inl (spentBy_nil_of_not hp)

/-! ## The other direction: where the condition holds, the test accepts -/

theorem test_of_within {Bk : ProverCoinCounts} {o : Addr} (h : WithinTakes P ride Bk o) :
    withinB P ride Bk o = true := by
  refine List.all_eq_true.2 fun e he => ?_
  by_cases ho : e.owner = o
  · have := h e he ho
    simp [ho, this.1, this.2]
  · simp [ho]

theorem test_of_fAll : ∀ {l : List Ahead}, fAll l = ∅ → noFB l = true
  | [], _ => rfl
  | e :: l, h => by
    have h' : fOf e ∪ fAll l = ∅ := h
    rw [Finset.union_eq_empty] at h'
    have h1 : e.count.f = 0 := by
      have := h'.1
      unfold fOf at this
      rw [Finset.Ico_eq_empty_iff] at this
      omega
    have h2 := test_of_fAll h'.2
    simp only [noFB, List.all_cons, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h1, h2⟩

theorem allE_of {l : List Ahead} {f : ℕ → Bool} (h : ∀ n ∈ eAll l, f n = true) :
    allE l f = true := by
  refine List.all_eq_true.2 fun e he => List.all_eq_true.2 fun t ht => h _ ?_
  rw [mem_eAll_iff]
  refine List.any_eq_true.2 ⟨e, he, ?_⟩
  have := List.mem_range.1 ht
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem test_of_apart : ∀ {l : List Ahead},
    (l.Pairwise fun e e' => Disjoint (eOf e) (eOf e')) → apartB l = true
  | [], _ => rfl
  | e :: l, h => by
    have h' := List.pairwise_cons.1 h
    simp only [apartB, Bool.and_eq_true]
    refine ⟨List.all_eq_true.2 fun e' he' => List.all_eq_true.2 fun t ht => ?_,
      test_of_apart h'.2⟩
    have ht' := List.mem_range.1 ht
    cases hb : inE [e'] (e.start.e + t) with
    | false => rfl
    | true =>
      have h1 : e.start.e + t ∈ eOf e' := by
        rw [← eAll_one, mem_eAll_iff]
        exact hb
      have h2 : e.start.e + t ∈ eOf e := Finset.mem_Ico.2 ⟨by omega, by omega⟩
      exact absurd h1 (Finset.disjoint_left.1 (h'.1 e' he') h2)

theorem not_inE {l : List Ahead} {n : ℕ} (h : n ∉ eAll l) : (!inE l n) = true := by
  cases hb : inE l n with
  | false => rfl
  | true => exact absurd ((mem_eAll_iff l n).2 hb) h

theorem test_of_mask {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : MaskSpender P ride Bk ord o p) : maskB P ride Bk ord o p = true := by
  simp only [maskB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨test_of_fAll h.noF, allE_of fun n hn => ?_⟩, test_of_apart h.apart⟩,
    allE_of fun n hn => not_inE (Finset.disjoint_left.1 h.unknown hn)⟩, ?_⟩
  · obtain ⟨k, hk, hr, ha, hf⟩ := h.free n hn
    refine List.any_eq_true.2 ⟨k, List.mem_range.2 hk, ?_⟩
    unfold freeNo at hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hf
    have := Finset.mem_range.1 ht
    simp only [hr, Option.isNone_none, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    exact ⟨⟨ha, by omega⟩, by omega⟩
  · refine List.all_eq_true.2 fun k hk => ?_
    cases hg : ((ride k).isNone && ((shapeAt P k).answers != 0)) with
    | false => rfl
    | true =>
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at hg
      simp only [Bool.not_true, Bool.false_or]
      refine List.all_eq_true.2 fun j hj => ?_
      cases hs : inE (Bk.spentBy o p) (maskStart P ride k + j) with
      | false => rfl
      | true =>
        have hc := h.clear k j (List.mem_range.1 hk) hg.1 hg.2
          (mem_freeNo P ride (by omega) (by have := List.mem_range.1 hj; omega))
          ((mem_eAll_iff _ _).2 hs)
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
        exact ⟨List.all_eq_true.2 fun i hi => not_inE (hc.1 i (List.mem_range.1 hi)),
          List.all_eq_true.2 fun q hq => by
            simp only [Bool.and_eq_true]
            exact ⟨not_inE (hc.2 q (List.mem_range.1 hq)).1,
              not_inE (hc.2 q (List.mem_range.1 hq)).2⟩⟩

theorem test_of_fold {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : FoldSpender P ride Bk ord o p) : foldB P ride Bk ord o p = true := by
  obtain ⟨k, R, e, hk, hr, hh, hs, hc, hst, ht⟩ := h.one
  simp only [foldB, Bool.and_eq_true]
  refine ⟨?_, allE_of fun n hn => not_inE (Finset.disjoint_left.1 h.unknown hn)⟩
  rw [hs]
  refine List.any_eq_true.2 ⟨k, List.mem_range.2 hk, ?_⟩
  rw [hr]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hh, hc⟩, hst⟩, List.all_eq_true.2 fun r hr' => List.all_eq_true.2 fun q hq =>
    not_inE (ht r (List.mem_range.1 hr') q (List.mem_range.1 hq))⟩

/-- spenderClearB accepts exactly if SpenderClear holds. -/
theorem spenderClearB_iff {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} :
    spenderClearB P ride Bk ord o p = true ↔ SpenderClear P ride Bk ord o p := by
  refine ⟨spenderClear_of_test P ride, fun h => ?_⟩
  simp only [spenderClearB, Bool.or_eq_true, List.isEmpty_iff]
  rcases h with h0 | h1 | h2
  · exact Or.inl (Or.inl h0)
  · exact Or.inl (Or.inr (test_of_mask P ride h1))
  · exact Or.inr (test_of_fold P ride h2)

/-- bookClearB accepts exactly if BookClear holds. -/
theorem bookClearB_iff {Bk : ProverCoinCounts} {ord : List Place} {o : Addr} :
    bookClearB P ride Bk ord o = true ↔ BookClear P ride Bk ord o := by
  refine ⟨bookClear_of_test P ride, fun h => ?_⟩
  simp only [bookClearB, Bool.and_eq_true]
  exact ⟨test_of_within P ride h.1, List.all_eq_true.2 fun p _ =>
    (spenderClearB_iff P ride).2 (h.2 p)⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.withinAtB_iff
#print axioms OnBytes.SendSim.At.spenderClearB_iff
#print axioms OnBytes.SendSim.At.bookClearB_iff
#print axioms OnBytes.SendSim.At.mask_of_test
#print axioms OnBytes.SendSim.At.fold_of_test
#print axioms OnBytes.SendSim.At.spenderClear_of_test
#print axioms OnBytes.SendSim.At.bookClear_of_test
