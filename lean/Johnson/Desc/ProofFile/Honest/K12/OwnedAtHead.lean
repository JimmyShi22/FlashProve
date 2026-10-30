-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OwnedAtHead.lean: K12's LOTS AND THE TEN WRITTEN SEATS THAT THE
TEST's FIVE SWITCHES FILL. PUBLIC DATA ALONE: seats, sendings' numbers, the witness's numbers. No
definition, eight theorems.

Why. To show the frame's authors' joined list fit at the full size, the code switch's authors split
two of its conditions by the sending of a seat (Honest/K2/Law/OwnedSplitAtHead.lean,
SharesApartAtHead.lean). One class of that split
has the sendings numbered 76, …, 80: the proximity test's five switches. For that class they ask of
its sender two things per seat (one lot of messages numbered like the seat, one lot of pads placed
at it) and three facts on what the sender's lists look like from outside. This file proves these for
K12's lists. It imports neither.

  `tenInFirstW`, `tenInFirstW_bite`   in `psFull`, the library's written list of the first chain's
                 seats, the seats with such a sending are (77, 0), (77, 1), …, (81, 1), in this
                 order; the second is a control on the two bounds
  `msgsOwned_k12`, `padsOwned_k12`   every such seat has a lot in `testMsgLots`, and one in `testPl`
  `faceMsgs_k12`, `facePads_k12`   conversely every lot of the two lists belongs to such a seat
  `faceMsgs_nodup_k12`   with the written numbering, the ten numbers are pairwise different
  `testTn_354`   `testTn 354` is [354]

All but the two closed facts and the last assume hJ (the job has six stages) and are at t₀ = 77. No
head is assumed: the seats are those of the written list itself.

How it is meant to fit [read at the authors' files, not tried in Lean within the library]. Their
`lastSeatsW` is `psFull.filter fun q => lastSend q.send` with `lastSend s := decide (76 ≤ s) &&
decide (s ≤ 80)`: the filter of `tenInFirstW` once `lastSend` is unfolded. Their `MsgsOwnedAt ml arr
qs` and `PadsOwnedAt pl qs` are the conclusions of our two laws with q ranging over qs. So a seat of
`lastSeatsW` gives q ∈ psFull and the two bounds by `List.mem_filter`. Their premises ask for the
lot in the joined list; ours gives it in our own list, which the joined list contains when the
record of the other senders does. That their filter is ours has been tried outside the library: a
small file of ours that waits for theirs proves `lastPadsW` = the ten seats by the bare term
`tenInFirstW`.

Near it in the library, not called: `P5J.AtMg.arr_is` (Johnson/LPFE1R/K10ClearAt.lean) and
`arr_at_head` (Johnson/P5J/L0/PlanFourAtJoin.lean): under the head `P5J.At.arr Zp` is `arrOf
seatsAllFull`; a closed fact in the latter file that the written numbering differs at three named
seats; `P5T.mineAt` (the seats of one sending). The authors' own closed fact has the length of
`lastSeatsW`, 10, and not its seats.

Limits.
- All that binds whoever builds on ScriptLots.lean (its head) binds here.
- THESE ARE FACTS ON WHICH LOTS THERE ARE, NOT ON WHAT THEY ANSWER. A lot whose text returns nothing
  counts here like any other.
- THE STATEMENTS ARE ABOUT `testMsgLots`, `testPl` AND `testTn`, NOT ABOUT A RECORD. The record made
  of them (`k12Share`, JoinShare.lean) is not in the library.
- `faceMsgs_nodup_k12` IS AT `arrOf seatsAllFull`. A share laid at `P5J.At.arr Zp` needs one of the
  two sealed equations named above in between, and with it the head. That step is not written.
- t₀ = 77, the number 354 and hJ are fixed by hand or assumed here, and no law is called that ties
  them to the chain. Had elsewhere, under the head: 77 is `treesTo cF.blocksInOrder 354` (`treesTo_354`,
  OffAt354.lean); the block at 354 stands at the test's place (`places_at_L`, AtProof/CutAtL.lean).
  hJ is shown of no job here.
- Of the eight only `tenInFirstW` has a control, and that one tries its two bounds.
- The files whose premises these are meant to meet may still change.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShareAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open P5T (psFull seatsAllFull arrOf)
open ProofFile.Honest.FirstThread

variable {Bk : ProverCoinCounts} {W X : Type}

/-- **In the written first chain's list the seats whose sending lies between 76 and 80 are these
ten**, in this order. -/
theorem tenInFirstW :
    (psFull.filter fun p => decide (76 ≤ p.send) && decide (p.send ≤ 80)).map (fun p => (p.j, p.t))
      =
      [(77, 0), (77, 1), (78, 0), (78, 1), (79, 0), (79, 1), (80, 0), (80, 1), (81, 0),
        (81, 1)] := by
  decide +kernel

/-- A control on the two bounds: sending 75 has the seats of tree 76, sending 81 those of tree 82.
-/
theorem tenInFirstW_bite :
    (psFull.filter fun p => p.send == 75).map (fun p => (p.j, p.t)) = [(76, 0), (76, 1)] ∧
    (psFull.filter fun p => p.send == 81).map (fun p => (p.j, p.t)) = [(82, 0), (82, 1)] := by
  decide +kernel

/-- **Every such seat has a lot of messages of ours with arr at that seat for its number**, whatever
arr is. -/
theorem msgsOwned_k12 (ch : ℕ) (J : TestJob W X) (hJ : J.p.nums.stages.length = 6) (own₀ : X)
    (n₀ : ℕ) (arr : ℕ → ℕ → ℕ) (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    ∀ q ∈ psFull, 76 ≤ q.send → q.send ≤ 80 →
      ∃ L ∈ testMsgLots (Bk := Bk) ch J own₀ n₀ 77 arr ok, L.n = arr q.j q.t := by
  intro q hq h1 h2
  have hm : (q.j, q.t) ∈ (psFull.filter fun p => decide (76 ≤ p.send) &&
      decide (p.send ≤ 80)).map (fun p => (p.j, p.t)) :=
    List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp [h1, h2]⟩, rfl⟩
  rw [tenInFirstW] at hm
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  have hτ : ∀ τ, τ < 5 → τ < J.p.nums.stages.length - 1 := fun τ h => by
    rw [hJ]
    omega
  rcases hm with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ |
    ⟨a, b⟩ | ⟨a, b⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 0 (by omega))
      (show 0 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 0 (by omega))
      (show 1 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 1 (by omega))
      (show 0 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 1 (by omega))
      (show 1 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 2 (by omega))
      (show 0 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 2 (by omega))
      (show 1 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 3 (by omega))
      (show 0 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 3 (by omega))
      (show 1 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 4 (by omega))
      (show 0 < 2 by omega), rfl⟩
  · rw [a, b]
    exact ⟨_, mem_testMsgLots ch J own₀ n₀ 77 arr ok (hτ 4 (by omega))
      (show 1 < 2 by omega), rfl⟩

/-- **Every such seat has a lot of pads of ours.** -/
theorem padsOwned_k12 (ch : ℕ) (J : TestJob W X) (hJ : J.p.nums.stages.length = 6)
    (codes : OnBytes.Codes) (sh sh₁ : ℕ → OnBytes.OracleShape) :
    ∀ q ∈ psFull, 76 ≤ q.send → q.send ≤ 80 →
      ∃ L ∈ testPl (Bk := Bk) ch J codes sh sh₁ 77, L.j = q.j ∧ L.t = q.t := by
  intro q hq h1 h2
  have hm : (q.j, q.t) ∈ (psFull.filter fun p => decide (76 ≤ p.send) &&
      decide (p.send ≤ 80)).map (fun p => (p.j, p.t)) :=
    List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp [h1, h2]⟩, rfl⟩
  rw [tenInFirstW] at hm
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  have hτ : ∀ τ, τ < 5 → τ < J.p.nums.stages.length - 1 := fun τ h => by
    rw [hJ]
    omega
  rcases hm with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ |
    ⟨a, b⟩ | ⟨a, b⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 0 (by omega))).1, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 0 (by omega))).2, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 1 (by omega))).1, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 1 (by omega))).2, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 2 (by omega))).1, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 2 (by omega))).2, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 3 (by omega))).1, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 3 (by omega))).2, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 4 (by omega))).1, rfl, rfl⟩
  · rw [a, b]
    exact ⟨_, (mem_testPl (Bk := Bk) ch J codes sh sh₁ 77 (hτ 4 (by omega))).2, rfl, rfl⟩

/-- Conversely: the number of each of our lots of messages is arr at such a seat. -/
theorem faceMsgs_k12 (ch : ℕ) (J : TestJob W X) (hJ : J.p.nums.stages.length = 6) (own₀ : X)
    (n₀ : ℕ) (arr : ℕ → ℕ → ℕ) (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    ∀ L ∈ testMsgLots (Bk := Bk) ch J own₀ n₀ 77 arr ok, ∃ q ∈ psFull, 76 ≤ q.send ∧ q.send ≤ 80 ∧
      L.n = arr q.j q.t := by
  have key : ∀ τ t, τ < 5 → (t = 0 ∨ t = 1) →
      ∃ q ∈ psFull, 76 ≤ q.send ∧ q.send ≤ 80 ∧ q.j = 77 + τ ∧ q.t = t := by
    intro τ t hτ ht
    have hp : (77 + τ, t) ∈ (psFull.filter fun p => decide (76 ≤ p.send) &&
        decide (p.send ≤ 80)).map (fun p => (p.j, p.t)) := by
      rw [tenInFirstW]
      rcases ht with rfl | rfl <;> interval_cases τ <;> simp
    obtain ⟨q, hq, e⟩ := List.mem_map.1 hp
    have hb := (List.mem_filter.1 hq).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨q, (List.mem_filter.1 hq).1, hb.1, hb.2, congrArg Prod.fst e, congrArg Prod.snd e⟩
  intro L hL
  unfold testMsgLots at hL
  rw [hJ] at hL
  obtain ⟨τ, hτ, hL⟩ := List.mem_flatMap.1 hL
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hL
  obtain ⟨q, hq, b1, b2, ej, et⟩ := key τ t (by simpa using List.mem_range.1 hτ) (by simpa using ht)
  exact ⟨q, hq, b1, b2, by rw [ej, et]⟩

/-- With the written numbering no number occurs twice among our lots of messages. -/
theorem faceMsgs_nodup_k12 (ch : ℕ) (J : TestJob W X) (hJ : J.p.nums.stages.length = 6) (own₀ : X)
    (n₀ : ℕ) (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    ((testMsgLots (Bk := Bk) ch J own₀ n₀ 77 (arrOf seatsAllFull) ok).map (·.n)).Nodup := by
  rw [nums_testMsgLots, hJ]
  decide +kernel

/-- Conversely: each of our lots of pads sits at such a seat. (That no seat occurs twice:
`testPl_seats_nodup`, ShareAtHead.lean.) -/
theorem facePads_k12 (ch : ℕ) (J : TestJob W X) (hJ : J.p.nums.stages.length = 6)
    (codes : OnBytes.Codes) (sh sh₁ : ℕ → OnBytes.OracleShape) :
    ∀ L ∈ testPl (Bk := Bk) ch J codes sh sh₁ 77, ∃ q ∈ psFull, 76 ≤ q.send ∧ q.send ≤ 80 ∧ L.j =
      q.j ∧ L.t = q.t := by
  have key : ∀ τ t, τ < 5 → (t = 0 ∨ t = 1) →
      ∃ q ∈ psFull, 76 ≤ q.send ∧ q.send ≤ 80 ∧ q.j = 77 + τ ∧ q.t = t := by
    intro τ t hτ ht
    have hp : (77 + τ, t) ∈ (psFull.filter fun p => decide (76 ≤ p.send) &&
        decide (p.send ≤ 80)).map (fun p => (p.j, p.t)) := by
      rw [tenInFirstW]
      rcases ht with rfl | rfl <;> interval_cases τ <;> simp
    obtain ⟨q, hq, e⟩ := List.mem_map.1 hp
    have hb := (List.mem_filter.1 hq).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨q, (List.mem_filter.1 hq).1, hb.1, hb.2, congrArg Prod.fst e, congrArg Prod.snd e⟩
  intro L hL
  unfold testPl testPadLots testPadLotsB at hL
  rw [hJ] at hL
  rcases List.mem_append.1 hL with hL | hL
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hL
    obtain ⟨q, hq, b1, b2, ej, et⟩ := key τ 0 (by simpa using List.mem_range.1 hτ) (Or.inl rfl)
    exact ⟨q, hq, b1, b2, ej.symm, et.symm⟩
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hL
    obtain ⟨q, hq, b1, b2, ej, et⟩ := key τ 1 (by simpa using List.mem_range.1 hτ) (Or.inr rfl)
    exact ⟨q, hq, b1, b2, ej.symm, et.symm⟩

/-- Our list of members' numbers at 354. -/
theorem testTn_354 : testTn 354 = [354] :=
  rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.tenInFirstW
#print axioms ProofFile.Honest.K12.tenInFirstW_bite
#print axioms ProofFile.Honest.K12.msgsOwned_k12
#print axioms ProofFile.Honest.K12.padsOwned_k12
#print axioms ProofFile.Honest.K12.faceMsgs_k12
#print axioms ProofFile.Honest.K12.faceMsgs_nodup_k12
#print axioms ProofFile.Honest.K12.facePads_k12
#print axioms ProofFile.Honest.K12.testTn_354
