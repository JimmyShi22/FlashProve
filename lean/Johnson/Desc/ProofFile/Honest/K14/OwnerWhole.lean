-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OwnerWhole.lean: WHERE A BOOK FAILS NONE OF ITS OWN TESTS
(ProverCoinCounts.clauses, Honest/Frame.lean) AND A SHORT PUBLIC TEST ON ITS ENTRIES AT ONE OWNER ACCEPTS
(wholeOrSpent, runsFit, Honest/K14/OwnerWholeTest.lean), THE TEST ON THE ORDER behindSpenderB
(Honest/K14/OwnerOrder.lean) ACCEPTS AT THE DESCRIPTION's OWN ORDER OF PLACES; so the frame's form
GuardClear (Honest/BookGuard.lean) holds there at a guard that is one run, and the test for the part
at "send o_omega" (Honest/K14/FreshOwner.lean) accepts. Statements with their proofs; no definition.
No maker of a book is opened.

  spent_not_known **the book's eighth test, drawn out at a carrying entry**: an entry that carries
                  a coin which another entry spends is handed to no part in front of the spender,
                  nor to the spender. (Of the book's tests Honest/Law/Rule/Tests.lean draws out the
                  first, fourth, fifth and sixth, Lent.lean the ninth)
  behindSpender_of_word   **so the test on the order accepts**: a stretch that is apart from the
                  guard's run is not asked; one that holds a spent coin is handed behind, by the
                  eighth test
  guardClear_of_whole, spOwner_ok_of_whole, spOwner_ok_of_wholeB   the frame's form, where moreover
                  the spent run lies in the guard's run; and the yes of the test for the part at
                  "send o_omega", where the stretches are o_omega's and
                  o_sp's whole runs among the part's coins, the spent run is o_sp's first coin, o_sp
                  has an entry that is no pad (0 < n), and the three tests on the plan accept: CALLS
                  of guardClear_of_order and spOwner_ok_of_order

The three ways to that yes, side by side: Honest/K14/OwnerOrder.lean's head. What this one has over
guardClear_of_tests and ok_of_tests (Honest/K14/FreshOwnerLaw.lean): no order of places is
evaluated; a known or carried run may reach into the guard's run, where it holds a spent coin;
withinCount is shown, not assumed. What it has under them: the order orderOf F alone; a book without
a spender does not pass.
What is assumed. B.word F = none: a maker's book has passed it (bookWhole_word,
Honest/AtPureLaw.lean).
THE SHORT TEST IS NARROWER THAN THE OWNER's TEST: A NO OF wholeOrSpent OR spWholeB IS NO NO OF THE
OWNER's TEST: at the book without an entry the first rejects and the second accepts (narrower_toy,
Honest/K14/OwnerWholeToy.lean). spStretches are o_omega's and o_sp's whole runs only where the shape
splits and the library's SpShape holds.
What is not claimed here. That any maker's book passes wholeOrSpent: for the frame's bookWhole:
Honest/K14/BookAtOmega.lean. All holds at ord := orderOf F alone: the eighth test orders by it.
Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OwnerOrder
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription Place)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- **The book's eighth test, drawn out at a carrying entry.** (The test also bars a SPENDING entry
that shares a coin from a part in front: not drawn out here.) -/
theorem spent_not_known (h : B.word F = none) {e k : Ahead} (he : e ∈ B.ahead) (hk : k ∈ B.ahead)
    (ho : e.once = true) (hc : k.once = false) (hs : e.shares k = true) :
    k.spender.before (orderOf F) e.spender = false ∧ k.spender ≠ e.spender := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, -, -, -, t8, -⟩ := t
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hk
  have hij : i ≠ j := by
    rintro rfl
    rw [hi] at hj
    obtain rfl := Option.some.inj hj
    rw [ho] at hc
    cases hc
  have h1 := List.all_eq_true.1 t8 (e, i) (List.mem_zipIdx_iff_getElem?.2 hi)
  rw [ho] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 (k, j) (List.mem_zipIdx_iff_getElem?.2 hj)
  simp only [hs, hc, Bool.not_true, Bool.not_false, Bool.or_false, Bool.and_true,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hij
  · exact h2

/-- **Where the book fails none of its own tests and the short tests accept, the test on the order
accepts**, at the description's own order of places. -/
theorem behindSpender_of_word {o : Addr} {a c first len : Nat} {ms : List (Due × Due)}
    (h : B.word F = none) (hW : wholeOrSpent ⟨0, a⟩ ⟨0, c⟩ ms B o = true)
    (hR : runsFit first len a c ms = true) :
    behindSpenderB first len B (orderOf F) o = true := by
  unfold wholeOrSpent at hW
  rw [Bool.and_eq_true] at hW
  obtain ⟨hS, hA⟩ := hW
  unfold behindSpenderB
  rw [List.all_eq_true]
  intro e he
  have he' := List.mem_filter.1 he
  have heo := he'.2
  simp only [Bool.and_eq_true, beq_iff_eq] at heo
  obtain ⟨es, ec⟩ : e.start = ⟨0, a⟩ ∧ e.count = ⟨0, c⟩ := by
    cases hsp : spendersOf B o with
    | nil => rw [hsp] at he; cases he
    | cons z l =>
      cases l with
      | cons _ _ => rw [hsp] at hS; cases hS
      | nil =>
        rw [hsp] at hS he
        obtain rfl := List.mem_singleton.1 he
        simpa only [Bool.and_eq_true, beq_iff_eq] using hS
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_filter.1 hk
  cases hc : k.once with
  | true => rfl
  | false =>
    rw [Bool.false_or]
    have hin := List.all_eq_true.1 hA k hk
    rw [hc, Bool.false_or] at hin
    have hm := List.all_eq_true.1 hR _ (List.contains_iff_mem.1 hin)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hm
    rcases hm.2 with hm2 | hm2
    · rw [hm2]
      rfl
    · have hsh : e.shares k = true := by
        unfold Ahead.shares
        rw [heo.2, beq_iff_eq.1 hk'.2, es, ec]
        have : meets a c k.start.e k.count.e = true := by
          simp only [meets, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hm2 ⊢
          obtain ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩ := hm2
          exact ⟨⟨⟨q2, q1⟩, q4⟩, q3⟩
        simp [this]
      obtain ⟨n1, n2⟩ := spent_not_known h he'.1 hk'.1 heo.1 hc hsh
      rw [n1]
      simp [n2]

/-- **From the short test and the book's own tests to the frame's form**, at a guard that is one
run. -/
theorem guardClear_of_whole {o : Addr} {a c first len : Nat} {ms : List (Due × Due)}
    (h : B.word F = none) (hW : wholeOrSpent ⟨0, a⟩ ⟨0, c⟩ ms B o = true)
    (h1 : first ≤ a) (h2 : a + c ≤ first + len) (hR : runsFit first len a c ms = true) :
    ∀ p, B.spentBy o p ≠ [] →
      GuardClear (fun _ => { f := [], e := [(first, len)] }) B (orderOf F) o p :=
  guardClear_of_order hW h1 h2 (fun m hm => by
    have := List.all_eq_true.1 hR m hm
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1) (behindSpender_of_word h hW hR)

/-- **So the test for the part at "send o_omega" accepts.** The stretches: o_omega's and o_sp's
whole runs among the part's coins; the spent run: o_sp's first coin. -/
theorem spOwner_ok_of_whole (A : SendPub) (n : Nat) (h : B.word F = none)
    (hW : wholeOrSpent ⟨0, spFirstCoin A⟩ ⟨0, 1⟩ (spStretches A n) B
      { place := sendPlace 5, part := 0 } = true) (hn : 0 < n)
    (hfit : sendingsFit A.P = true) (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S n (spMaskCode A).r = true) :
    (spOwnerTest A n).ok B (orderOf F) { place := sendPlace 5, part := 0 } = true :=
  spOwner_ok_of_order A n hW (behindSpender_of_word h hW (by
    simp only [runsFit, spStretches, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_self_eq_true, true_and, Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨Or.inl ?_, Or.inr ?_⟩
    · simp [meets]
    · simp [meets])) hn hfit hs hP

/-- **The same from the one test spWholeB**, at the number n that is read off the mask code. -/
theorem spOwner_ok_of_wholeB (A : SendPub) (h : B.word F = none) (hW : spWholeB A B = true)
    (hn : 0 < spEntries A) (hfit : sendingsFit A.P = true)
    (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S (spEntries A) (spMaskCode A).r = true) :
    (spOwner A).ok B (orderOf F) { place := sendPlace 5, part := 0 } = true :=
  spOwner_ok_of_whole A (spEntries A) h hW hn hfit hs hP

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.spent_not_known
#print axioms ProofFile.Honest.K14.behindSpender_of_word
#print axioms ProofFile.Honest.K14.guardClear_of_whole
#print axioms ProofFile.Honest.K14.spOwner_ok_of_whole
#print axioms ProofFile.Honest.K14.spOwner_ok_of_wholeB
