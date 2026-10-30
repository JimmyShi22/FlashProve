-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/HeldAtHeadW.lean: AT THE MAKER's BOOK, AT THE ENTRIES OF W's PAIR: THE STRETCH THAT
THE FRAME HANDS A PART READS THE SENDER's OWN COINS, at the message's own
coins, at the written numbers.
PUBLIC DATA ALONE in what is read of the book.

  `rideGF`, `rideWF`   the two senders' rides at the written plans
  `written_W`, `written_W_bite`   the written list and the written rows against the senders' own
                 reckoning: the two owners' rows count `K1.dueR`; they have no row in the two later
                 tables; entries 0 and 1 to both parts, and entry 3 to the second, start at `startR`
                 and count `dueMsg`; the spent run's bound; a control. Evaluations in Lean's kernel
  `members_held`   `member_held` (HandedW.lean) at these two, at either part of the pair
  `fresh_held`, `spent_W_held`   the fresh table's stretch at the second part; the spent run at the
                 first
  `written_O`   the written list and rows at Omega's message
  `omega_held`   AT OMEGA's MEMBER, at either part: its rows at the stretch that the frame carries
                 are its rows at the sender's own coins: `member_held_shared` and `mem_rows_below`

Limits.
- `c₀` is the own cut of the sender's coins, at the sender's count: that it is what `lendPart` hands
  the sender is `lendPart`'s text; no run is named, and no filling.
- AT THE WRITTEN DESCRIPTION's BOOK (hB): `lendRow_W_at_head` has the step to the head's book;
  not taken here.
- `omega_held` ends at the member's rows at the sender's coins: that the sender's own rows are these
  is of `sameCut_of_book`'s kind: not here. Its start and count are literals against the
  written entry: the sender's number comes in by hq.
- The message's own coins alone. `omega_held` has hq, that the member is the written row, and hs,
  the sort, as premises.
- The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
- What may be said of this pair on hiding stands in the head of
  Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.HandedAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HandedW
import Johnson.Desc.ProofFile.Honest.K12.LaidBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K1 (parGF parWF qFull)
open Johnson.Prover.Send (shapeAt)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawAheadW rawCarriesWW rawRowsFirstW rawRowsSharedW rawRowsSecondW
  rawBookRows_written rawWhole_is_raw bookWhole_returns_written_ahead)

/-- The first opening's ride, as the filling's sender has it. -/
abbrev rideGF : Nat → Option K1.Ride := K1.rideOf (K1.firstFold qFull)

/-- W's ride. -/
abbrev rideWF : Nat → Option K1.Ride := K1.rideOf (K1.wFold qFull.lin)

set_option maxRecDepth 1000000 in
/-- **THE WRITTEN LIST AND ROWS AGAINST THE SENDERS' OWN RECKONING**, to both parts; the fresh table
to the second; the spent run to the first. -/
theorem written_W :
    dueAt rawRowsFirstW senderI = K1.dueR parGF rideGF ∧
    dueAt rawRowsFirstW senderW = K1.dueR parWF rideWF ∧
    rawRowsSharedW.any (fun r => r.1 == senderI) = false ∧
    rawRowsSecondW.any (fun r => r.1 == senderI) = false ∧
    rawRowsSharedW.any (fun r => r.1 == senderW) = false ∧
    rawRowsSecondW.any (fun r => r.1 == senderW) = false ∧
    parGF.sent.size - 1 < parGF.sent.size ∧ 1 < parWF.sent.size ∧
    (∀ j ∈ [0, 1], ((rawCarriesWW.filter fun e => e.spender == ⟨placeW, j⟩).map
      (fun e => (e.owner, e.start, e.count))).take 2 =
      [(senderI, K1.startR parGF rideGF (parGF.sent.size - 1),
          K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
            (rideGF (parGF.sent.size - 1))),
       (senderW, K1.startR parWF rideWF 0,
          K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0))]) ∧
    ((rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map
      (fun e => (e.owner, e.start, e.count)))[3]? =
      some (senderW, K1.startR parWF rideWF 1,
        K1.dueMsg parWF.codes (shapeAt parWF 1) (rideWF 1)) ∧
    K1.startR parWF rideWF 1 = ⟨0, 3882⟩ ∧
    (K1.startR parWF rideWF 1).e + 11 ≤ (K1.dueR parWF rideWF).e := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: with the two owners' rows turned it says no. -/
theorem written_W_bite :
    decide (dueAt rawRowsFirstW senderI = K1.dueR parWF rideWF) = false := by decide +kernel

variable {V W X : Type}

/-- hB is a premise. **AT THE MAKER's BOOK K1's TWO MEMBERS' STRETCHES READ THE SENDERS' OWN
COINS**, at either part of the pair. p, y: the part and what the frame hands it: `hl` does the work
of the job's public fields. -/
theorem members_held {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {p : Part V W X} {y : p.Coins} {j : Nat}
    (hj : j ∈ [0, 1]) (k : Coins B)
    (hl : lendPart B (B.rowsOf 2) (k.look 2) ⟨placeW, j⟩ p = .ok y) :
    (∀ {c₀ : Cs (K1.dueR parGF rideGF)},
      (k.look 0 senderI).2.cut ⟨0, 0⟩ (K1.dueR parGF rideGF) = some c₀ →
      (∀ i, i < (K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))).f →
        K1.cf c₀ ((K1.startR parGF rideGF (parGF.sent.size - 1)).f + i) =
          (stretches p.carries y.2.2 0).f i) ∧
      ∀ i, i < (K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))).e →
        K1.ce c₀ ((K1.startR parGF rideGF (parGF.sent.size - 1)).e + i) =
          (stretches p.carries y.2.2 0).e i) ∧
    (∀ {c₀ : Cs (K1.dueR parWF rideWF)},
      (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c₀ →
      (∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)).f →
        K1.cf c₀ ((K1.startR parWF rideWF 0).f + i) = (stretches p.carries y.2.2 1).f i) ∧
      ∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)).e →
        K1.ce c₀ ((K1.startR parWF rideWF 0).e + i) = (stretches p.carries y.2.2 1).e i) := by
  obtain ⟨dI, dW, sI, tI, sW, tW, mI, mW, hAll, -, -, -⟩ := written_W
  have hL := hAll j hj
  obtain ⟨r1, r2, r3⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  have ha : (⟨placeW, j⟩ : Addr) = ⟨placeW, 0⟩ ∨ (⟨placeW, j⟩ : Addr) = ⟨placeW, 1⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc := carryE_at_W hB ha
  obtain ⟨e₀, e₁, he₀, he₁, q₀, q₁⟩ : ∃ e₀ e₁ : Ahead, (carryE B ⟨placeW, j⟩)[0]? = some e₀ ∧
      (carryE B ⟨placeW, j⟩)[1]? = some e₁ ∧
      (e₀.owner, e₀.start, e₀.count) = (senderI, K1.startR parGF rideGF (parGF.sent.size - 1),
        K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))) ∧
      (e₁.owner, e₁.start, e₁.count) = (senderW, K1.startR parWF rideWF 0,
        K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)) := by
    rw [hc]
    cases hLs : rawCarriesWW.filter (fun e => e.spender == ⟨placeW, j⟩) with
    | nil =>
      rw [hLs] at hL
      simp at hL
    | cons a l =>
      cases l with
      | nil =>
        rw [hLs] at hL
        simp at hL
      | cons b l =>
        rw [hLs] at hL
        simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.cons.injEq,
          and_true] at hL
        exact ⟨a, b, rfl, rfl, hL.1, hL.2⟩
  obtain ⟨o₀, s₀, c₀'⟩ : e₀.owner = senderI ∧ e₀.start = _ ∧ e₀.count = _ := by
    simpa [Prod.mk.injEq] using q₀
  obtain ⟨o₁, s₁, c₁'⟩ : e₁.owner = senderW ∧ e₁.start = _ ∧ e₁.count = _ := by
    simpa [Prod.mk.injEq] using q₁
  refine ⟨fun {c₀} h₀ => ?_, fun {c₀} h₀ => ?_⟩
  · exact member_held k hl he₀ parGF rideGF _ mI s₀ c₀'
      (by rw [o₀]; show dueAt B.first _ = _; rw [r1]; exact dI)
      (by rw [o₀, r2]; exact sI) (by rw [o₀, r3]; exact tI) (by rw [o₀]; exact h₀)
  · exact member_held k hl he₁ parWF rideWF _ (Nat.lt_of_le_of_lt (Nat.zero_le _) mW) s₁ c₁'
      (by rw [o₁]; show dueAt B.first _ = _; rw [r1]; exact dW)
      (by rw [o₁, r2]; exact sW) (by rw [o₁, r3]; exact tW) (by rw [o₁]; exact h₀)

/-- hB is a premise. **THE FRESH TABLE's STRETCH, AT THE SECOND PART, READS W's OWN COINS.** -/
theorem fresh_held {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {p : Part V W X} {y : p.Coins} (k : Coins B)
    (hl : lendPart B (B.rowsOf 2) (k.look 2) ⟨placeW, 1⟩ p = .ok y)
    {c₀ : Cs (K1.dueR parWF rideWF)}
    (h₀ : (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c₀) :
    (∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 1) (rideWF 1)).f →
      K1.cf c₀ ((K1.startR parWF rideWF 1).f + i) = (stretches p.carries y.2.2 3).f i) ∧
    ∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 1) (rideWF 1)).e →
      K1.ce c₀ ((K1.startR parWF rideWF 1).e + i) = (stretches p.carries y.2.2 3).e i := by
  obtain ⟨-, dW, -, -, sW, tW, -, mW, -, hL, -, -⟩ := written_W
  obtain ⟨r1, r2, r3⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  have hc := carryE_at_W hB (a := ⟨placeW, 1⟩) (Or.inr rfl)
  rw [List.getElem?_map] at hL
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 hL
  obtain ⟨o, s, c⟩ : e.owner = senderW ∧ e.start = _ ∧ e.count = _ := by
    simpa [Prod.mk.injEq] using q
  have he' : (carryE B ⟨placeW, 1⟩)[3]? = some e := by
    rw [hc]
    exact he
  exact member_held k hl he' parWF rideWF 1 mW s c
    (by rw [o]; show dueAt B.first _ = _; rw [r1]; exact dW)
    (by rw [o, r2]; exact sW) (by rw [o, r3]; exact tW) (by rw [o]; exact h₀)

/-- hB is a premise. **THE SPENT RUN, AT THE FIRST PART, READS W's OWN COINS**: at (0, 3882), eleven
of them. -/
theorem spent_W_held {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {p : Part V W X} {y : p.Coins} (k : Coins B)
    (hl : lendPart B (B.rowsOf 2) (k.look 2) ⟨placeW, 0⟩ p = .ok y)
    {c₀ : Cs (K1.dueR parWF rideWF)}
    (h₀ : (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c₀) :
    ∀ i, i < 11 → K1.ce c₀ (3882 + i) = (stretches p.spends y.2.1 0).e i := by
  obtain ⟨-, dW, -, -, sW, tW, -, -, -, -, st, bd⟩ := written_W
  obtain ⟨r1, r2, r3⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  obtain ⟨B₀, hB₀, he⟩ := bookWhole_returns_written_ahead
  obtain rfl : B = B₀ := Except.ok.inj (hB.symm.trans hB₀)
  obtain ⟨s0, -⟩ := spent_W_written
  have e0 : spentE B ⟨placeW, 0⟩ =
      (rawAheadW.filter fun e => e.spender == ⟨placeW, 0⟩).filter (·.once) := by
    unfold spentE
    rw [he]
  rw [← e0] at s0
  cases hs : spentE B ⟨placeW, 0⟩ with
  | nil =>
    rw [hs] at s0
    simp at s0
  | cons e l =>
    rw [hs] at s0
    simp only [List.map_cons, List.cons.injEq] at s0
    obtain ⟨q, -⟩ := s0
    obtain ⟨o, s, c⟩ : e.owner = senderW ∧ e.start = ⟨0, 3882⟩ ∧ e.count = ⟨0, 11⟩ := by
      simpa [Prod.mk.injEq] using q
    have he' : (spentE B ⟨placeW, 0⟩)[0]? = some e := by
      rw [hs]
      rfl
    rw [st] at bd
    obtain ⟨-, f2⟩ := spent_held k hl he' (t := K1.dueR parWF rideWF)
      (by rw [o]; show dueAt B.first _ = _; rw [r1]; exact dW)
      (by rw [o, r2]; exact sW) (by rw [o, r3]; exact tW)
      (by rw [s, c]; exact Nat.zero_le _ |>.trans (Nat.zero_le _)) (by rw [s, c]; exact bd)
      (by rw [o]; exact h₀)
    intro i hi
    have := f2 i (by rw [c]; exact hi)
    rw [s] at this
    exact this

set_option maxRecDepth 1000000 in
/-- **The written list and rows at Omega's message.** -/
theorem written_O :
    rawRowsFirstW.any (fun r => r.1 == senderO) = false ∧
    rawRowsSecondW.any (fun r => r.1 == senderO) = false ∧
    (∀ j ∈ [0, 1], ((rawCarriesWW.filter fun e => e.spender == ⟨placeW, j⟩).map
      (fun e => (e.owner, e.start, e.count)))[2]? = some (senderO, ⟨0, 0⟩, rowOF.2.2)) ∧
    rowOF.2.2.f ≤ (dueAt rawRowsSharedW senderO).f ∧
    rowOF.2.2.e ≤ (dueAt rawRowsSharedW senderO).e := by decide +kernel

/-- hB is a premise. **AT OMEGA's MEMBER, AT EITHER PART, THE STRETCH THAT THE FRAME CARRIES GIVES
THE ROWS THAT THE SENDER's OWN COINS GIVE.** M: the member's sending; hq: its row is the written
row; hs: its sort. -/
theorem omega_held {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {p : Part V W X} {y : p.Coins} {j : Nat}
    (hj : j ∈ [0, 1]) (k : Coins B)
    (hl : lendPart B (B.rowsOf 2) (k.look 2) ⟨placeW, j⟩ p = .ok y)
    (M : ProofFile.Honest.K14.SendJob) (fs : Option Nat × Option Nat) (ask : W → ProofFile.Honest.K14.Ask)
    (hi : Bool) (hs : M.sort 0 = .plain hi) (hq : msgOf senderO M 0 = rowOF)
    {c₀ : Cs (dueAt rawRowsSharedW senderO)}
    (h₀ : (k.look 1 senderO).2.cut ⟨0, 0⟩ (dueAt rawRowsSharedW senderO) = some c₀) (w : W)
    (fr : Front X) :
    (ProofFile.Honest.K12.Light.memOfSending M senderO 0 fs ask none).rows w fr
        (stretches p.carries y.2.2 2) =
      (ProofFile.Honest.K12.Light.memOfSending M senderO 0 fs ask none).rows w fr (stretchOf c₀) := by
  obtain ⟨t1, t3, hAll, bf, be⟩ := written_O
  have hL := hAll j hj
  obtain ⟨r1, r2, r3⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  have ha : (⟨placeW, j⟩ : Addr) = ⟨placeW, 0⟩ ∨ (⟨placeW, j⟩ : Addr) = ⟨placeW, 1⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc := carryE_at_W hB ha
  rw [List.getElem?_map] at hL
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 hL
  obtain ⟨o, s, c⟩ : e.owner = senderO ∧ e.start = ⟨0, 0⟩ ∧ e.count = rowOF.2.2 := by
    simpa [Prod.mk.injEq] using q
  have he' : (carryE B ⟨placeW, j⟩)[2]? = some e := by
    rw [hc]
    exact he
  have key := member_held_shared k hl he' (t := dueAt rawRowsSharedW senderO)
    (by rw [o]; show dueAt B.shared _ = _; rw [r2]) (by rw [o, r1]; exact t1)
    (by rw [o, r3]; exact t3) s (by rw [c]; exact bf) (by rw [c]; exact be)
    (by rw [o]; exact h₀)
  refine ProofFile.Honest.K12.Light.mem_rows_below M senderO 0 fs ask none hi hs w fr _ _ fun i hi' => ?_
  refine key i ?_
  rw [c]
  have e₁ : (msgOf senderO M 0).2.2.e = rowOF.2.2.e :=
    congrArg (fun r : Addr × Nat × Due => r.2.2.e) hq
  have e₂ : (msgOf senderO M 0).2.2.e =
      ProofFile.Honest.K14.dueOf M.Q.codes (M.Q.sent.getD 0 default).shape (M.sort 0) := rfl
  rw [← e₁, e₂]
  exact hi'

end AtFullSide.K12

#print axioms AtFullSide.K12.rideGF
#print axioms AtFullSide.K12.rideWF
#print axioms AtFullSide.K12.written_W
#print axioms AtFullSide.K12.written_W_bite
#print axioms AtFullSide.K12.members_held
#print axioms AtFullSide.K12.fresh_held
#print axioms AtFullSide.K12.spent_W_held
#print axioms AtFullSide.K12.written_O
#print axioms AtFullSide.K12.omega_held
