-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Sim/BookLists.lean: a public test on TWO LISTS, the spending and the
carried entries on one sender's coins, and the proof that the wider condition on the book,
BookClearAny (Johnson/SendSim/At/BookWide.lean), holds at the sender at every book that has these two
lists there. It is the test fastOkB of Johnson/SendSim/At/FastBook.lean with three turns: it reads the
two lists and no book; for "along the spending entries each run ends before the next begins" it asks
"no two spending runs share a number", in whatever order they stand; and in the sixth clause the two
arms of the "or" have changed places, so that an evaluation looks at the order of places only where
the numbers do not settle it. Three definitions; three
theorems. Public data alone: no distribution is named.

  apartAllB, apartAll_pairwise   no two runs of a list share a number
  inTakesB         an entry is within the sender's number of coins
  listsOkB         THE TEST, on S (spending) and C (carried): fastOkB's six clauses, the third turned
  clearAny_of_lists   where spendsOf Bk o = S, carriesOf Bk o = C and the test accepts:
                   BookClearAny P ride Bk ord o

WHOSE THE PROOF IS. From the line "what is spent at p is apart from what is known there" to its end the
proof of clearAny_of_lists IS THAT OF clearAny_of_fast (Johnson/SendSim/At/FastBook.lean), cut by
program, to the letter: that proof reads its third clause at one place alone, to have the spending
entries pairwise apart.

Why. At a book whose spending entries on one sender's coins do not rise in the book's order fastOkB
rejects though BookClearAny holds (that file's Limits). And a test that filters a book of thousands of
entries anew at each entry is much for an evaluation in Lean's kernel; two written lists are not.

Limits. The test is sufficient, not necessary: all limits of FastBook.lean but the one on the order of
the spending runs. It counts every other spender's entries as known, whatever ord says. Nothing is
evaluated here. No property of the protocol is claimed.
-/
import Johnson.SendSim.At.FastBook

set_option autoImplicit false

namespace ProofFile.Honest.K1.Sim
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)
open OnBytes.SendSim.At

/-- No two runs of the list share a number. -/
def apartAllB : List (Nat × Nat) → Bool
  | [] => true
  | x :: l => l.all (apart2 x) && apartAllB l

theorem apartAll_pairwise : ∀ {l : List (Nat × Nat)}, apartAllB l = true →
    l.Pairwise fun x z => apart2 x z = true
  | [], _ => List.Pairwise.nil
  | x :: l, h => by
    simp only [apartAllB, Bool.and_eq_true] at h
    exact List.Pairwise.cons (fun z hz => List.all_eq_true.1 h.1 z hz) (apartAll_pairwise h.2)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The entry is within the sender's number of coins. -/
def inTakesB (e : Ahead) : Bool :=
  decide (e.start.f + e.count.f ≤ (dueR P ride).f) &&
    decide (e.start.e + e.count.e ≤ (dueR P ride).e)

/-- **The test on the two lists.** -/
def listsOkB (S C : List Ahead) (ord : List Place) : Bool :=
  (S.all (inTakesB P ride) && C.all (inTakesB P ride)) &&
  (S.all fun s => s.count.f == 0 &&
    (List.range P.sent.size).any fun k => freeAtB P ride k s || foldAtB P ride k s) &&
  apartAllB (S.map runE) &&
  (S.all fun s => (allGuard P ride).all fun t => apart2 (runE s) t) &&
  (S.all fun s => ((List.range P.sent.size).any fun k => freeAtB P ride k s) ||
    (S.filter fun s' => s'.spender == s.spender).length == 1) &&
  (C.all fun c => S.all fun s =>
    (apart2 (runE c) (runE s) && (guardOf P ride s).all fun t => apart2 (runE c) t) ||
      !(c.spender == s.spender || c.spender.before ord s.spender))

variable {P ride}

/-- **Where the book has these two lists at the sender and the test accepts, BookClearAny holds
there.** -/
theorem clearAny_of_lists {Bk : ProverCoinCounts} {ord : List Place} {o : Addr} {S C : List Ahead}
    (hS : spendsOf Bk o = S) (hC : carriesOf Bk o = C)
    (h : listsOkB P ride S C ord = true) : BookClearAny P ride Bk ord o := by
  subst hS
  subst hC
  unfold listsOkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hWs, hWc⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h1 := List.all_eq_true.1 h1
  have h3 := List.all_eq_true.1 h3
  have h4 := List.all_eq_true.1 h4
  have h5 : ∀ c ∈ carriesOf Bk o, ((spendsOf Bk o).all fun s =>
      !(c.spender == s.spender || c.spender.before ord s.spender) ||
        (apart2 (runE c) (runE s) && (guardOf P ride s).all fun t => apart2 (runE c) t)) = true := by
    intro c hc
    refine List.all_eq_true.2 fun s hs => ?_
    have h6 := List.all_eq_true.1 (List.all_eq_true.1 h5 c hc) s hs
    rwa [Bool.or_comm] at h6
  -- the spending entries are pairwise apart
  have hpw : (spendsOf Bk o).Pairwise fun a b => Disjoint (eOf a) (eOf b) := by
    have := List.pairwise_map.1 (apartAll_pairwise h2)
    refine this.imp fun {a b} hab => Finset.disjoint_left.2 fun n ha hb => ?_
    exact apart2_spec hab (mem_eOf.1 ha) (mem_eOf.1 hb)
  have hW : WithinTakes P ride Bk o := by
    intro e he ho
    have hin : inTakesB P ride e = true := by
      cases hc : e.once
      · exact List.all_eq_true.1 hWc e (List.mem_filter.2 ⟨he, by simp [ho, hc]⟩)
      · exact List.all_eq_true.1 hWs e (List.mem_filter.2 ⟨he, by simp [ho, hc]⟩)
    unfold inTakesB at hin
    simpa using hin
  refine ⟨hW, fun p => ?_⟩
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

end ProofFile.Honest.K1.Sim

#print axioms ProofFile.Honest.K1.Sim.apartAll_pairwise
#print axioms ProofFile.Honest.K1.Sim.clearAny_of_lists
