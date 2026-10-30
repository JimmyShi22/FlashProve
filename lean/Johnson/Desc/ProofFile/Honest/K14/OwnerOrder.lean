-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OwnerOrder.lean: WHERE A SHORT PUBLIC TEST ON A BOOK's ENTRIES AT
ONE OWNER (wholeOrSpent, Honest/K14/OwnerWholeTest.lean) AND A PUBLIC TEST ON THE ORDER OF PLACES
(behindSpenderB, here) ACCEPT, AND THE SPENT RUN LIES IN THE GUARD's RUN, AND NEITHER IT NOR A
LISTED STRETCH HAS A COIN OF THE BASE FIELD, THE FRAME's FORM GuardClear (Honest/BookGuard.lean)
HOLDS AT A GUARD THAT IS ONE RUN, AT EVERY ORDER OF PLACES; and so, where o_sp has an entry that is
no pad (0 < n) and the three tests on the plan accept (sendingsFit, the split, freshPublicB), the
test for the part at "send o_omega" (Honest/K14/FreshOwner.lean) accepts. One definition with code;
statements with their proofs. No maker of a book is opened; none of a book's own tests is used.

  behindSpenderB first len B ord o   the test on the order: every entry with the owner o that
                  carries a coin of the run (first, len) OF THE EXTENSION FIELD's COINS (the base
                  field's numbers are not read) is handed to a part that is neither a part that
                  spends of o's coins nor in front of one
  behindSpender_congr   it says the same at two books with the same entries at the owner
  behindSpender_of_knownBelow   **the tie to the test knownBelow** (Honest/K14/FreshDefs.lean):
                  where that accepts at a number, this accepts at every run that begins there: this
                  is the weaker test
  known_of_order  **what is known at a spender, where both tests accept**: every member of
                  ProverCoinCounts.knownBy there carries; its run is one of the listed stretches; it does not
                  meet the run (first, len)
  guardClear_of_order   **the frame's form**, at every part that spends
  spFits_of_whole, spOwner_ok_of_order   **so the test for the part at "send o_omega" accepts**

THREE WAYS TO THAT TEST's YES, SIDE BY SIDE. (1) guardClear_of_tests, ok_of_tests
(Honest/K14/FreshOwnerLaw.lean): from oneSpender and knownBelow (and withinCount): every order; no
test of the book's own. (2) guardClear_of_order, spOwner_ok_of_order (here): from wholeOrSpent, "no
stretch has a coin of the base field" and behindSpenderB: every order; no test of the book's own;
withinCount is shown. (3) guardClear_of_whole, spOwner_ok_of_whole (Honest/K14/OwnerWhole.lean):
from wholeOrSpent, runsFit and the book's own tests: the order orderOf F alone: a corollary of (2).
behindSpenderB lets a known run reach above the number where it does not meet the guard's run:
knownBelow does not. AT THE FRAME's SHORT LIST BOTH TESTS ACCEPT (Honest/K14/BookAtOmega.lean): so
(1) serves there as well as (2): (2) is kept because its test on the order asks less of a book (its
other test, wholeOrSpent, asks more than oneSpender: the two ways are not comparable).
A place that is not in ord counts as the last (the frame's Addr.before): at a general ord a carrier
at such a place passes behindSpenderB, unless the spender stands at that place too; the frame's
knownBy has the same move.
Kin. The frame's OwnerTest.ok_clear, spender_of_spentBy (Honest/BookGuard.lean).
What is not claimed. That any maker's book passes either test: Honest/K14/BookAtOmega.lean. THE
SHORT TEST IS NARROWER THAN THE OWNER's TEST: a no of wholeOrSpent is no no of the owner's test
(narrower_toy, Honest/K14/OwnerWholeToy.lean). Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OwnerAt
import Johnson.Desc.ProofFile.Honest.K14.FreshRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)

/-- **A test on the order**: every entry with the owner o that carries a coin of the run
(first, len) of the extension field's coins is handed to a part that neither spends of o's coins nor
stands in front of a part that does. The base field's numbers are not read. -/
def behindSpenderB (first len : Nat) (B : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  (spendersOf B o).all fun e => (aheadAt B o).all fun k =>
    k.once || !meets k.start.e k.count.e first len ||
      (!k.spender.before ord e.spender && k.spender != e.spender)

/-- The test on the order says the same at two books with the same entries at the owner. -/
theorem behindSpender_congr {B B' : ProverCoinCounts} {o : Addr} (h : aheadAt B' o = aheadAt B o)
    (first len : Nat) (ord : List Place) :
    behindSpenderB first len B' ord o = behindSpenderB first len B ord o := by
  unfold behindSpenderB
  rw [spendersOf_congr h, h]

/-- **THE TIE OF THE TWO TESTS ON THE ORDER** (no kind's part is named): where knownBelow accepts at
a number, behindSpenderB accepts at every run that begins there: the second is a weakening of the
first. -/
theorem behindSpender_of_knownBelow {B : ProverCoinCounts} {ord : List Place} {o : Addr} {g : Nat}
    (h : knownBelow B ord o g = true) (n : Nat) : behindSpenderB g n B ord o = true := by
  unfold behindSpenderB
  unfold knownBelow at h
  rw [List.all_eq_true] at h ⊢
  intro e he
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_filter.1 hk
  cases hc : k.once with
  | true => rfl
  | false =>
    rw [Bool.false_or]
    by_cases hin : (k.spender == e.spender || k.spender.before ord e.spender) = true
    · have hmem : k ∈ B.knownBy ord o e.spender :=
        List.mem_filter.2 ⟨hk'.1, by rw [hk'.2, hc, hin]; simp⟩
      have hle := of_decide_eq_true (List.all_eq_true.1 (h e he) k hmem)
      have hm : meets k.start.e k.count.e g n = false := by
        cases hmm : meets k.start.e k.count.e g n with
        | false => rfl
        | true =>
          obtain ⟨x, ⟨-, x2⟩, x3, -⟩ := (meets_iff _ _ _ _).1 hmm
          omega
      rw [hm]
      rfl
    · simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hin
      rw [hin.2]
      simp [hin.1]

/-- **What is known at a spender, where both tests accept**: it carries; its run is one of the
listed stretches; it does not meet the run (first, len). -/
theorem known_of_order {B : ProverCoinCounts} {ord : List Place} {o : Addr} {s c : Due} {first len : Nat}
    {ms : List (Due × Due)} (hW : wholeOrSpent s c ms B o = true)
    (hO : behindSpenderB first len B ord o = true) :
    ∀ e ∈ spendersOf B o, ∀ k ∈ B.knownBy ord o e.spender,
      k.once = false ∧ (k.start, k.count) ∈ ms ∧
        meets k.start.e k.count.e first len = false := by
  unfold wholeOrSpent at hW
  rw [Bool.and_eq_true] at hW
  obtain ⟨hS, hA⟩ := hW
  intro e he k hk
  have hone : ∀ y ∈ spendersOf B o, y = e := by
    cases hsp : spendersOf B o with
    | nil => rw [hsp] at he; cases he
    | cons z l =>
      cases l with
      | cons _ _ => rw [hsp] at hS; cases hS
      | nil =>
        rw [hsp] at he
        intro y hy
        rw [List.mem_singleton.1 hy, List.mem_singleton.1 he]
  have hk' := List.mem_filter.1 hk
  have hq := hk'.2
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at hq
  obtain ⟨⟨hko, hkn⟩, hkb⟩ := hq
  have hkc : k.once = false := by
    cases hc : k.once with
    | false => rfl
    | true =>
      have hm : k ∈ spendersOf B o :=
        List.mem_filter.2 ⟨hk'.1, by rw [hc, hko]; exact beq_self_eq_true _⟩
      rw [hone k hm] at hkn hc
      rw [hc] at hkn
      simp at hkn
  have hat : k ∈ aheadAt B o := List.mem_filter.2 ⟨hk'.1, by
    rw [hko]; exact beq_self_eq_true _⟩
  have hin := List.all_eq_true.1 hA k hat
  rw [hkc, Bool.false_or] at hin
  refine ⟨hkc, List.contains_iff_mem.1 hin, ?_⟩
  have hb := List.all_eq_true.1 (List.all_eq_true.1 hO e he) k hat
  rw [hkc, Bool.false_or] at hb
  cases hm : meets k.start.e k.count.e first len with
  | false => rfl
  | true =>
    exfalso
    rw [hm] at hb
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
      ne_eq] at hb
    rcases hkb with q | q
    · exact hb.2 q
    · rw [hb.1] at q
      cases q

/-- **From the short test and the test on the order to the frame's form**, at a guard that is one
run: where the spent run lies in the guard's run and neither it nor a listed stretch has a coin of
the base field. -/
theorem guardClear_of_order {B : ProverCoinCounts} {ord : List Place} {o : Addr} {a c first len : Nat}
    {ms : List (Due × Due)} (hW : wholeOrSpent ⟨0, a⟩ ⟨0, c⟩ ms B o = true)
    (h1 : first ≤ a) (h2 : a + c ≤ first + len) (hf : ∀ m ∈ ms, m.2.f = 0)
    (hO : behindSpenderB first len B ord o = true) :
    ∀ p, B.spentBy o p ≠ [] →
      GuardClear (fun _ => { f := [], e := [(first, len)] }) B ord o p := by
  have hK := known_of_order hW hO
  unfold wholeOrSpent at hW
  rw [Bool.and_eq_true] at hW
  obtain ⟨hS, -⟩ := hW
  cases hsp : spendersOf B o with
  | nil => rw [hsp] at hS; cases hS
  | cons e l =>
    cases l with
    | cons _ _ => rw [hsp] at hS; cases hS
    | nil =>
      rw [hsp] at hS
      simp only [Bool.and_eq_true, beq_iff_eq] at hS
      obtain ⟨es, ec⟩ := hS
      have hem : e ∈ spendersOf B o := by rw [hsp]; exact List.mem_singleton.2 rfl
      intro p hp
      have hone : ∀ x ∈ B.spentBy o p, x = e := fun x hx => by
        have hx' := List.mem_filter.1 hx
        have hq := hx'.2
        simp only [Bool.and_eq_true, beq_iff_eq] at hq
        have : x ∈ spendersOf B o :=
          List.mem_filter.2 ⟨hx'.1, by rw [hq.2, hq.1.1]; exact beq_self_eq_true _⟩
        rw [hsp] at this
        exact List.mem_singleton.1 this
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hp
      have hpe : e.spender = p := by
        have hx' := (List.mem_filter.1 hx).2
        simp only [Bool.and_eq_true, beq_iff_eq] at hx'
        rw [← hone x hx]
        exact hx'.1.2
      have hkn : ∀ k ∈ B.knownBy ord o p,
          k.count.f = 0 ∧ meets k.start.e k.count.e first len = false := fun k hk => by
        obtain ⟨-, hm, hn⟩ := hK e hem k (by rw [hpe]; exact hk)
        exact ⟨hf _ hm, hn⟩
      have noF : ∀ n, ¬ inRuns (B.knownRuns ord o p).f n := fun n ⟨r, hr, q1, q2⟩ => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
        have := (hkn k hk).1
        simp only at q1 q2
        omega
      have noE : ∀ n, first ≤ n → n < first + len →
          ¬ inRuns (B.knownRuns ord o p).e n := fun n g1 g2 ⟨r, hr, q1, q2⟩ => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
        have hm := (hkn k hk).2
        have : meets k.start.e k.count.e first len = true :=
          (meets_iff _ _ _ _).2 ⟨n, ⟨q1, q2⟩, g1, g2⟩
        rw [hm] at this
        cases this
      refine ⟨⟨fun n hn => noF n hn.2, fun n hn => ?_⟩, ⟨fun n hn => noF n hn.2, fun n hn => ?_⟩⟩
      · obtain ⟨⟨r, hr, q1, q2⟩, hk⟩ := hn
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr
        rw [hone y hy, es, ec] at q1 q2
        simp only at q1 q2
        exact noE n (by omega) (by omega) hk
      · obtain ⟨⟨r, hr, q1, q2⟩, hk⟩ := hn
        obtain rfl := List.mem_singleton.1 hr
        exact noE n q1 q2 hk

/-- The owner's fits, from the short test, 0 < n and the three tests on the plan. -/
theorem spFits_of_whole {B : ProverCoinCounts} (A : SendPub) (n : Nat)
    (hW : wholeOrSpent ⟨0, spFirstCoin A⟩ ⟨0, 1⟩ (spStretches A n) B
      { place := sendPlace 5, part := 0 } = true) (hn : 0 < n)
    (hfit : sendingsFit A.P = true) (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S n (spMaskCode A).r = true) :
    spFits A n B { place := sendPlace 5, part := 0 } = true := by
  unfold wholeOrSpent at hW
  rw [Bool.and_eq_true] at hW
  obtain ⟨hS, hA⟩ := hW
  have hT := takes_omega A hs (Desc.K14.Honest.freshPublic_of hP).shape
  have h1 : oneSpender B { place := sendPlace 5, part := 0 } (spFirstCoin A) n = true := by
    unfold oneSpender
    cases hsp : spendersOf B { place := sendPlace 5, part := 0 } with
    | nil => rfl
    | cons e l =>
      cases l with
      | cons _ _ => rw [hsp] at hS; cases hS
      | nil =>
        rw [hsp] at hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hS
        simp [hS.1, hS.2, hn]
  have h2 : withinCount (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) B
      { place := sendPlace 5, part := 0 } = true := by
    have hT' : takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort =
        ⟨0, spFirstCoin A + (n + 1) + (spMaskCode A).r⟩ := hT
    rw [hT']
    unfold withinCount
    rw [List.all_eq_true]
    intro e he
    by_cases ho : (e.owner == ({ place := sendPlace 5, part := 0 } : Addr)) = true
    · rw [ho]
      have hin := List.all_eq_true.1 hA e (List.mem_filter.2 ⟨he, ho⟩)
      cases hc : e.once with
      | true =>
        have hm : e ∈ spendersOf B { place := sendPlace 5, part := 0 } :=
          List.mem_filter.2 ⟨he, by rw [hc, ho]; rfl⟩
        cases hsp : spendersOf B { place := sendPlace 5, part := 0 } with
        | nil => rw [hsp] at hm; cases hm
        | cons x l =>
          cases l with
          | cons _ _ => rw [hsp] at hS; cases hS
          | nil =>
            rw [hsp] at hS hm
            obtain rfl := List.mem_singleton.1 hm
            simp only [Bool.and_eq_true, beq_iff_eq] at hS
            simp [hS.1, hS.2]
            omega
      | false =>
        rw [hc, Bool.false_or] at hin
        have hm := List.contains_iff_mem.1 hin
        simp only [spStretches, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · simp [q1, q2]
          omega
        · simp [q1, q2]
          omega
    · simp [ho]
  unfold spFits
  rw [h1, hfit, hs, hP, h2]
  rfl

/-- **The test for the part at "send o_omega" accepts**, at every order of places at which the test
on the order accepts. -/
theorem spOwner_ok_of_order {B : ProverCoinCounts} {ord : List Place} (A : SendPub) (n : Nat)
    (hW : wholeOrSpent ⟨0, spFirstCoin A⟩ ⟨0, 1⟩ (spStretches A n) B
      { place := sendPlace 5, part := 0 } = true)
    (hO : behindSpenderB (spFirstCoin A) (n + 1 + (spMaskCode A).r) B ord
      { place := sendPlace 5, part := 0 } = true) (hn : 0 < n)
    (hfit : sendingsFit A.P = true) (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S n (spMaskCode A).r = true) :
    (spOwnerTest A n).ok B ord { place := sendPlace 5, part := 0 } = true := by
  have hG := guardClear_of_order (first := spFirstCoin A) (len := n + 1 + (spMaskCode A).r) hW
    (Nat.le_refl _) (by omega) (fun m hm => by
      simp only [spStretches, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> rfl) hO
  unfold OwnerTest.ok
  rw [Bool.and_eq_true]
  refine ⟨spFits_of_whole A n hW hn hfit hs hP, List.all_eq_true.2 fun p _ => ?_⟩
  by_cases hp : B.spentBy { place := sendPlace 5, part := 0 } p = []
  · rw [hp]
    rfl
  · rw [Bool.or_eq_true]
    exact Or.inr ((guardClearB_iff _ _ _ _ _).2 (hG p hp))

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.behindSpender_congr
#print axioms ProofFile.Honest.K14.behindSpender_of_knownBelow
#print axioms ProofFile.Honest.K14.known_of_order
#print axioms ProofFile.Honest.K14.guardClear_of_order
#print axioms ProofFile.Honest.K14.spFits_of_whole
#print axioms ProofFile.Honest.K14.spOwner_ok_of_order
