-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/SeatOnto.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: EVERY NUMBER BELOW THE PART's COUNT, IN EACH FIELD, IS A PLACE's. Statements and
proofs: arithmetic on the numbers of Honest/K1/Seat.lean.

  split_mul     a number below m * c is r * c + q with r < m and q < c
  off_onto      in one message: every number below the message's count in a field is Seat.off of a
                place inside the sizes, of that field
  find_msg_e, find_msg_f   a number below where message number m's coins begin lies in the stretch
                of one earlier message
  seat_onto     EVERY NUMBER BELOW THE PART's COUNT, IN EACH FIELD, IS Seat.no OF A PLACE INSIDE THE
                SIZES OF ONE OF THE SENDING's MESSAGES

Limits. At a riding table a mask coin's place is its NUMBER among the table's coefficients: that
rowsR lays it at one place of the table is ride_one's (Honest/K1/RideOne.lean), at one row alone: at
more rows such a number has no one place. THAT rowsR READS AT Seat.no IS NOT SAID HERE: it is
seat_reads' (Honest/K1/SeatReads.lean), under sendFits, at a message of the sending whose table does
not ride, at a place inside the sizes: so the title does not say that every coin is laid somewhere.
No test on the job is asked. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

theorem split_mul (m c n : Nat) (h : n < m * c) : ∃ r q, r < m ∧ q < c ∧ n = r * c + q := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.mul_zero] at h
      exact absurd h (Nat.not_lt_zero _)
    · exact h0
  refine ⟨n / c, n % c, ?_, Nat.mod_lt _ hc, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  · have := Nat.div_add_mod n c
    rw [Nat.mul_comm] at this
    exact this.symm

/-- **In one message.** -/
theorem off_onto (codes : Codes) (s : OracleShape) (R : Option Ride) (e : Bool) (n : Nat)
    (h : n < share codes s R e) :
    ∃ x : Seat, x.ok codes s R ∧ x.inE s = e ∧ x.off codes s R = n := by
  have hT : (stepsOf codes s R).tails = s.mainRows * (codes.base.getD s.code default).r := rfl
  have hK : (stepsOf codes s R).maskTails =
    s.maskRows * (codes.mask.getD s.maskCode default).r := rfl
  have hM : (stepsOf codes s R).main =
    (stepsOf codes s R).tails + (stepsOf codes s R).word + (stepsOf codes s R).pad := rfl
  -- a number below the main coins' count is a main place's
  have main : ∀ n, n < (stepsOf codes s R).main → ∃ x : Seat, x.ok codes s R ∧
      x.inE s = (s.mainDeg == 3) ∧ x.off codes s R = n := by
    intro n hn
    by_cases h1 : n < (stepsOf codes s R).tails
    · obtain ⟨r, q, hr, hq, rfl⟩ := split_mul _ _ n (hT ▸ h1)
      exact ⟨.tail r q, ⟨hr, hq⟩, rfl, rfl⟩
    · by_cases hw : (stepsOf codes s R).word = 0
      · exact ⟨.pad (n - (stepsOf codes s R).tails),
          (by show n - _ < (stepsOf codes s R).pad; omega), rfl,
          (by show (stepsOf codes s R).tails + (n - _) = n; omega)⟩
      · obtain ⟨e1, e2⟩ := word_eq codes s R hw
        obtain ⟨r, j, hr, hj, hn'⟩ := split_mul s.mainRows
          (codes.base.getD s.code default).ell (n - (stepsOf codes s R).tails) (by omega)
        exact ⟨.word r j, ⟨hw, hr, hj⟩, rfl,
          (by show (stepsOf codes s R).tails + r * _ + j = n; omega)⟩
  -- a number below the mask coins' and their tails' count, from the base b on
  have mask : ∀ n, n < (stepsOf codes s R).mask + (stepsOf codes s R).maskTails →
      ∃ x : Seat, x.ok codes s R ∧ x.inE s = true ∧
        x.off codes s R = (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) + n := by
    intro n hn
    by_cases h1 : n < (stepsOf codes s R).mask
    · exact ⟨.mask n, h1, rfl, rfl⟩
    · obtain ⟨r, q, hr, hq, hn'⟩ := split_mul s.maskRows
        (codes.mask.getD s.maskCode default).r (n - (stepsOf codes s R).mask) (by omega)
      exact ⟨.maskTail r q, ⟨hr, hq⟩, rfl, (by
        show (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) +
          (stepsOf codes s R).mask + r * _ + q = _
        omega)⟩
  by_cases h3 : (s.mainDeg == 3) = true
  · cases e with
    | true =>
      simp only [share, dueMsg, h3, if_true] at h
      by_cases hm : n < (stepsOf codes s R).main
      · obtain ⟨x, a, b, c⟩ := main n hm
        exact ⟨x, a, b.trans h3, c⟩
      · obtain ⟨x, a, b, c⟩ := mask (n - (stepsOf codes s R).main) (by omega)
        refine ⟨x, a, b, ?_⟩
        rw [c, h3, if_pos rfl]
        omega
    | false =>
      simp only [share, dueMsg, h3, if_true, Bool.false_eq_true, if_false] at h
      exact absurd h (Nat.not_lt_zero _)
  · have h3' : (s.mainDeg == 3) = false := by simpa using h3
    cases e with
    | true =>
      simp only [share, dueMsg, h3', Bool.false_eq_true, if_false, if_true] at h
      obtain ⟨x, a, b, c⟩ := mask n h
      refine ⟨x, a, b, ?_⟩
      rw [c, h3']
      simp
    | false =>
      simp only [share, dueMsg, h3', Bool.false_eq_true, if_false] at h
      obtain ⟨x, a, b, c⟩ := main n h
      exact ⟨x, a, b.trans h3', c⟩

/-! ## Through the messages -/

theorem find_msg_e (P : K1.Par) (ride : Nat → Option Ride) (n : Nat) : ∀ m,
    n < (startR P ride m).e → ∃ k, k < m ∧ (startR P ride k).e ≤ n ∧ n < (startR P ride (k + 1)).e
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    by_cases hm : n < (startR P ride m).e
    · obtain ⟨k, a, b, c⟩ := find_msg_e P ride n m hm
      exact ⟨k, by omega, b, c⟩
    · exact ⟨m, by omega, by omega, h⟩

theorem find_msg_f (P : K1.Par) (ride : Nat → Option Ride) (n : Nat) : ∀ m,
    n < (startR P ride m).f → ∃ k, k < m ∧ (startR P ride k).f ≤ n ∧ n < (startR P ride (k + 1)).f
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    by_cases hm : n < (startR P ride m).f
    · obtain ⟨k, a, b, c⟩ := find_msg_f P ride n m hm
      exact ⟨k, by omega, b, c⟩
    · exact ⟨m, by omega, by omega, h⟩

/-- **EVERY NUMBER BELOW THE PART's COUNT IS A PLACE's.** -/
theorem seat_onto (P : K1.Par) (ride : Nat → Option Ride) (e : Bool) (n : Nat)
    (h : n < if e then (dueR P ride).e else (dueR P ride).f) :
    ∃ k x, k < P.sent.size ∧ Seat.ok P.codes (shapeAt P k) (ride k) x ∧
      x.inE (shapeAt P k) = e ∧ x.no P ride k = n := by
  cases e with
  | true =>
    obtain ⟨k, hk, a, b⟩ := find_msg_e P ride n P.sent.size h
    rw [start_e] at b
    obtain ⟨x, ox, ex, fx⟩ := off_onto P.codes (shapeAt P k) (ride k) true
      (n - (startR P ride k).e) (by show _ < (dueMsg _ _ _).e; omega)
    refine ⟨k, x, hk, ox, ex, ?_⟩
    unfold Seat.no
    rw [ex, fx, if_pos rfl]
    omega
  | false =>
    obtain ⟨k, hk, a, b⟩ := find_msg_f P ride n P.sent.size h
    rw [start_f] at b
    obtain ⟨x, ox, ex, fx⟩ := off_onto P.codes (shapeAt P k) (ride k) false
      (n - (startR P ride k).f) (by show _ < (dueMsg _ _ _).f; omega)
    refine ⟨k, x, hk, ox, ex, ?_⟩
    unfold Seat.no
    rw [ex, fx, if_neg (by decide)]
    omega

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.split_mul
#print axioms ProofFile.Honest.K1.off_onto
#print axioms ProofFile.Honest.K1.find_msg_e
#print axioms ProofFile.Honest.K1.find_msg_f
#print axioms ProofFile.Honest.K1.seat_onto
