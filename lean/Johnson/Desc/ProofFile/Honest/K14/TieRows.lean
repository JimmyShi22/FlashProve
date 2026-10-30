-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieRows.lean: kind K14: THE ROWS THAT THIS KIND's TEXT OF A
SENDING LAYS ARE, READ, THE ROWS THAT THE SHARED SENDING's TEXT LAYS, AT THE SAME COINS, NUMBER BY
NUMBER: for every job whose shapes fit, at every state and every value of the coins. Statements with
their proofs. An equation at each value of the coins: no distribution occurs.

  ride_plain, ride_fresh, vec_plain, sendRows_at   rideBySort, vecData and SendJob.rows at a
                  message, by its sort
  offset_mono, room_tie   each message's coins lie within the part's count
  tieCoin_val, tieCoin_word   a coin of this kind's text, by its number in the message, is the coin
                  of the shared text with the same number: read; and as the program's element
  rows_tie        **RowsAgree** (Honest/K14/TieDefs.lean) between SendJob.rows and rowsR at vecData

How. Message by message, by the arm of the test on shapes that the message's sort picks: main_same,
mask_same (Honest/K14/SendingsViaRows.lean), tail_same, maskTail_same, ride_same, rideTail_same
(Honest/K14/SendingsViaHolds.lean), each of which asks that the message's coins in the two texts are
the same by number: that is start_tie (Honest/K14/TieCounts.lean) with recount_e
(Honest/K14/TieCoins.lean).
What is assumed. sendShapeFits J = true (Honest/K14/SendingsShapes.lean).
Limits. Nothing on columns, answers or what is shown. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.TieCoins
import Johnson.Desc.ProofFile.Honest.K14.TieDefs
import Johnson.Desc.ProofFile.Honest.K14.TieCounts
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleNotice)
open OnBytes.Slice (GE GF rdE ofE)
open Johnson.Prover.Send (Rows shapeAt)
open ProofFile.Honest.K1 (Ride rowsR startR dueR ce)

/-- On a message that is laid plainly no table rides. -/
theorem ride_plain (J : SendJob) (k : Nat) (high : Bool) (hs : J.sort k = .plain high) :
    rideBySort J k = none := by
  unfold rideBySort
  rw [hs]

/-- On a fold's fresh table the table of its two numbers rides. -/
theorem ride_fresh (J : SendJob) (k k' h : Nat) (hs : J.sort k = .fresh k' h) :
    rideBySort J k = some ⟨k', h⟩ := by
  unfold rideBySort
  rw [hs]

/-- The data of a message that is laid plainly: its vector, as vectorData lays it. -/
theorem vec_plain (J : SendJob) (t : State Ask Unit) (k : Nat) (high : Bool)
    (hs : J.sort k = .plain high) (r j : Nat) :
    vecData J t k r j = vectorData J.Q.codes (shapeAt J.Q k) high (J.data t k) r j := by
  unfold vecData
  rw [hs]

/-- A message's rows in this kind's text, at its sort. -/
theorem sendRows_at (J : SendJob) (t : State Ask Unit) (cs : Array E) (k : Nat) (s : MsgSort)
    (hs : J.sort k = s) :
    J.rows t cs k = laid J.Q.codes (shapeAt J.Q k) (J.data t k)
      (fun i => cs.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i) zeroE) s := by
  unfold SendJob.rows
  rw [hs]
  rfl

/-- Where messages' coins begin grows with the message's number. -/
theorem offset_mono (codes : Codes) (sent : Array OracleNotice) (sort : Nat → MsgSort) :
    ∀ n k, k ≤ n → n ≤ sent.size → offsetOf codes sent sort k ≤ offsetOf codes sent sort n := by
  intro n
  induction n with
  | zero =>
    intro k hk _
    have e : k = 0 := by omega
    subst e
    exact Nat.le_refl _
  | succ n ih =>
    intro k hk hn
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · have h1 := ih k (by omega) (by omega)
      rw [offset_succ codes sent sort n (by omega)]
      omega
    · have e : k = n + 1 := by omega
      subst e
      exact Nat.le_refl _

/-- **Each message's coins lie within the part's count.** -/
theorem room_tie (J : SendJob) (k : Nat) (hk : k < J.Q.sent.size) :
    offsetOf J.Q.codes J.Q.sent J.sort k + dueOf J.Q.codes (shapeAt J.Q k) (J.sort k) ≤
      (sendingPart J).takes.e := by
  have h := offset_mono J.Q.codes J.Q.sent J.sort J.Q.sent.size (k + 1) hk (Nat.le_refl _)
  rw [offset_succ _ _ _ k hk] at h
  exact h

section
variable (J : SendJob) (hfit : sendShapeFits J = true) (c : Cs (sendingPart J).takes)

/-- **A coin by its number in the message, read.** -/
theorem tieCoin_val (k : Nat) (hk : k ≤ J.Q.sent.size) (i : Nat) :
    rdE.val ((coinsE c).toArray.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i) zeroE) =
      ce (recount (due_tie J hfit) c) ((startR J.Q (rideBySort J) k).e + i) := by
  rw [val_coinsE, recount_e, start_tie J hfit k hk]

/-- **A coin by its number in the message, as the program's element**, within the count. -/
theorem tieCoin_word (k : Nat) (hk : k ≤ J.Q.sent.size) (i : Nat)
    (hi : offsetOf J.Q.codes J.Q.sent J.sort k + i < (sendingPart J).takes.e) :
    (coinsE c).toArray.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i) zeroE =
      E.ofTriple (ofE (ce (recount (due_tie J hfit) c)
        ((startR J.Q (rideBySort J) k).e + i))) := by
  rw [coded_coin c _ hi, recount_e, start_tie J hfit k hk]

/-- **The two texts' rows are the same, read, wherever they are read.** -/
theorem rows_tie (t : State Ask Unit) :
    RowsAgree J.Q (J.rows t (coinsE c).toArray)
      (rowsR J.Q (rideBySort J) (vecData J t) (recount (due_tie J hfit) c)) := by
  have hcs := fun k (hk : k < J.Q.sent.size) => tieCoin_val J hfit c k (Nat.le_of_lt hk)
  refine ⟨fun k hk hm => ?_, fun k hk r hr j hj => ?_, fun k hk r hr q hq => ?_,
    fun k hk r hr j hj => ?_, fun k hk r hr q hq => ?_⟩
  · have hf := msg_fits J hfit k hk
    cases hs : J.sort k with
    | plain high =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hf
      rcases hf.2 with ⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩ | ⟨h0, -⟩
      · exact h3
      · exact absurd h0 hm
    | fresh k' h =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
      exact absurd hf.1.1.1.1.2 hm
  · have hf := msg_fits J hfit k hk
    cases hs : J.sort k with
    | plain high =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hf
      rcases hf.2 with ⟨⟨⟨⟨hz, -⟩, h3⟩, hlen⟩, ha⟩ | ⟨h0, -⟩
      · rw [sendRows_at J t _ k _ hs]
        exact main_same J.Q (rideBySort J) (vecData J t) _ k high (J.data t k) _ h3 hz (by omega)
          hlen (vec_plain J t k high hs) (hcs k hk) r j hr hj
      · omega
    | fresh k' h =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
      have h0 := hf.1.1.1.1.2
      omega
  · have hf := msg_fits J hfit k hk
    cases hs : J.sort k with
    | plain high =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hf
      rcases hf.2 with ⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩ | ⟨h0, -⟩
      · rw [sendRows_at J t _ k _ hs]
        exact tail_same J.Q (rideBySort J) (vecData J t) _ k high (J.data t k) _ h3 (hcs k hk) r q
          hr hq
      · omega
    | fresh k' h =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
      have h0 := hf.1.1.1.1.2
      omega
  · have hf := msg_fits J hfit k hk
    cases hs : J.sort k with
    | plain high =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hf
      rcases hf.2 with ⟨⟨⟨⟨hz, -⟩, -⟩, -⟩, -⟩ | ⟨h0, hz⟩
      · omega
      · rw [sendRows_at J t _ k _ hs]
        exact mask_same J.Q (rideBySort J) (vecData J t) _ k high (J.data t k) _ h0 (by omega)
          (ride_plain J k high hs) (hcs k hk) r j hr hj
    | fresh k' h =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
      obtain ⟨⟨⟨⟨⟨⟨-, ha⟩, hm⟩, -⟩, hhk⟩, -⟩, -⟩ := hf
      have hroom := room_tie J k hk
      rw [hs] at hroom
      rw [sendRows_at J t _ k _ hs]
      refine ride_same J.Q (rideBySort J) (vecData J t) _ k k' h (J.data t k) _
        (ride_fresh J k k' h hs) hhk hm ha (fun i hi => ?_) r j hr hj
      refine tieCoin_word J hfit c k (Nat.le_of_lt hk) i ?_
      have e : dueOf J.Q.codes (shapeAt J.Q k) (.fresh k' h) = 2 * k' + 1 +
          (shapeAt J.Q k).maskRows *
            (J.Q.codes.mask.getD (shapeAt J.Q k).maskCode default).r := rfl
      rw [e] at hroom
      omega
  · have hf := msg_fits J hfit k hk
    cases hs : J.sort k with
    | plain high =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hf
      rcases hf.2 with ⟨⟨⟨⟨hz, -⟩, -⟩, -⟩, -⟩ | ⟨h0, hz⟩
      · omega
      · rw [sendRows_at J t _ k _ hs]
        exact maskTail_same J.Q (rideBySort J) (vecData J t) _ k high (J.data t k) _ h0 (by omega)
          (ride_plain J k high hs) (hcs k hk) r q hr hq
    | fresh k' h =>
      rw [hs] at hf
      simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
      obtain ⟨⟨⟨⟨⟨⟨-, ha⟩, hm⟩, -⟩, -⟩, -⟩, -⟩ := hf
      rw [sendRows_at J t _ k _ hs]
      exact rideTail_same J.Q (rideBySort J) (vecData J t) _ k k' h (J.data t k) _
        (ride_fresh J k k' h hs) hm ha (hcs k hk) r q hr hq

end

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.ride_plain
#print axioms ProofFile.Honest.K14.ride_fresh
#print axioms ProofFile.Honest.K14.vec_plain
#print axioms ProofFile.Honest.K14.sendRows_at
#print axioms ProofFile.Honest.K14.offset_mono
#print axioms ProofFile.Honest.K14.room_tie
#print axioms ProofFile.Honest.K14.tieCoin_val
#print axioms ProofFile.Honest.K14.tieCoin_word
#print axioms ProofFile.Honest.K14.rows_tie
