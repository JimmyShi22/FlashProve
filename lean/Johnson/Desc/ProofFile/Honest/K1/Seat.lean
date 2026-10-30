-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Seat.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR THE
HONEST SIDE: TWO PLACES INSIDE THE SIZES, OF ONE FIELD, BEAR TWO NUMBERS. Definitions, statements
and proofs: arithmetic on the numbers at which rowsR (Honest/K1/Coins.lean) reads the part's coins.

  Seat          a place at which a message holds a coin, by the five steps of the order in the head
                of Honest/K1/Coins.lean
  Seat.inE, Seat.ok, Seat.off, Seat.no   the coin's field · the place lies inside the message's
                sizes · the coin's number among the message's coins of its field · among the part's
  Seat.lo, Seat.hi, Seat.rng   the stretch of a step's numbers in a message; a place inside the
                sizes bears a number in its step's stretch
  share, hi_le  a message's count in a field; a stretch ends inside it
  word_eq, word_pad   a message has the message of a word with main rows and no answer, or a pad in
                a main row, not both
  mul_add_inj   r * c + q with q < c tells r and q
  Seat.kind, kind_eq, off_inj   in one message: two places of one field and one number are of one
                step; and are one
  start_e, start_f   where the next message's coins begin
  seat_next, seat_in   a place inside the sizes bears a number inside the part's count, in its field
  seat_lt       of two messages the earlier one's numbers lie below the later one's
  seat_inj      TWO PLACES INSIDE THE SIZES, OF ONE FIELD, BEAR TWO NUMBERS

Seat.off's five terms are the right-hand sides of tail_coin_e and _f, word_coin_e and _f, pad_coin_e
and _f, maskTail_coin (Honest/K1/CoinLaw.lean), mask_slot (MaskLaw.lean) and, at a riding table,
ride_coin (RideLaw.lean).

Limits. THAT rowsR READS AT Seat.no IS NOT SAID HERE: it is these laws', and, as one statement,
seat_reads' (Honest/K1/SeatReads.lean). No test on the job is asked: the count splits the fields by
"mainDeg == 3" at every mainDeg, as Seat.inE does. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.CoinsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- **A place at which a message holds a coin**, by the five steps of the order: a main row's tail's
entry · an entry of the message of a word with main rows and no answer · a pad's entry in a main
row, by its number in the pad · a mask coin, by its number (the format's number of the entry; at a
riding table the coefficient's number) · a mask row's tail's entry. -/
inductive Seat where
  | tail (r q : Nat)
  | word (r j : Nat)
  | pad (i : Nat)
  | mask (i : Nat)
  | maskTail (r q : Nat)
  deriving DecidableEq

/-- The field of the coin at a place: true: the extension field. -/
def Seat.inE (s : OracleShape) : Seat → Bool
  | .tail .. | .word .. | .pad _ => s.mainDeg == 3
  | .mask _ | .maskTail .. => true

/-- The place lies inside the message's sizes. -/
def Seat.ok (codes : Codes) (s : OracleShape) (R : Option Ride) : Seat → Prop
  | .tail r q => r < s.mainRows ∧ q < (codes.base.getD s.code default).r
  | .word r j => (stepsOf codes s R).word ≠ 0 ∧ r < s.mainRows ∧
      j < (codes.base.getD s.code default).ell
  | .pad i => i < (stepsOf codes s R).pad
  | .mask i => i < (stepsOf codes s R).mask
  | .maskTail r q => r < s.maskRows ∧ q < (codes.mask.getD s.maskCode default).r

/-- The coin's number among the message's coins of its field: rowsR's own terms. -/
def Seat.off (codes : Codes) (s : OracleShape) (R : Option Ride) : Seat → Nat
  | .tail r q => r * (codes.base.getD s.code default).r + q
  | .word r j => (stepsOf codes s R).tails + r * (codes.base.getD s.code default).ell + j
  | .pad i => (stepsOf codes s R).tails + i
  | .mask i => (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) + i
  | .maskTail r q => (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) +
      (stepsOf codes s R).mask + r * (codes.mask.getD s.maskCode default).r + q

/-- **The coin's number among the part's coins of its field.** -/
def Seat.no (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (x : Seat) : Nat :=
  (if x.inE (shapeAt P k) then (startR P ride k).e else (startR P ride k).f) +
    x.off P.codes (shapeAt P k) (ride k)

/-! ## In one message -/

/-- Where a step's numbers begin in a message, in the step's field. -/
def Seat.lo (codes : Codes) (s : OracleShape) (R : Option Ride) : Seat → Nat
  | .tail .. => 0
  | .word .. | .pad _ => (stepsOf codes s R).tails
  | .mask _ => if s.mainDeg == 3 then (stepsOf codes s R).main else 0
  | .maskTail .. => (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) +
      (stepsOf codes s R).mask

/-- Where they end. -/
def Seat.hi (codes : Codes) (s : OracleShape) (R : Option Ride) : Seat → Nat
  | .tail .. => (stepsOf codes s R).tails
  | .word .. => (stepsOf codes s R).tails + (stepsOf codes s R).word
  | .pad _ => (stepsOf codes s R).tails + (stepsOf codes s R).pad
  | .mask _ => (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) + (stepsOf codes s R).mask
  | .maskTail .. => (if s.mainDeg == 3 then (stepsOf codes s R).main else 0) +
      (stepsOf codes s R).mask + (stepsOf codes s R).maskTails

/-- A message's count in a field. -/
def share (codes : Codes) (s : OracleShape) (R : Option Ride) (e : Bool) : Nat :=
  if e then (dueMsg codes s R).e else (dueMsg codes s R).f

theorem word_eq (codes : Codes) (s : OracleShape) (R : Option Ride)
    (h : (stepsOf codes s R).word ≠ 0) :
    (stepsOf codes s R).word = s.mainRows * (codes.base.getD s.code default).ell ∧
      (stepsOf codes s R).pad = 0 := by
  by_cases hc : (s.mainRows != 0 && s.answers == 0) = true
  · have ha : (s.answers != 0) = false := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [hc.2]
      rfl
    constructor
    · simp only [stepsOf, hc, if_true]
    · simp only [stepsOf, ha, Bool.and_false, Bool.false_eq_true, if_false]
  · exact absurd (by simp only [stepsOf, hc, Bool.false_eq_true, if_false]) h

/-- The message of a word with main rows and no answer, or a pad in a main row, not both. -/
theorem word_pad (codes : Codes) (s : OracleShape) (R : Option Ride) :
    (stepsOf codes s R).word = 0 ∨ (stepsOf codes s R).pad = 0 := by
  by_cases h : (stepsOf codes s R).word = 0
  · exact .inl h
  · exact .inr (word_eq codes s R h).2

theorem Seat.rng (codes : Codes) (s : OracleShape) (R : Option Ride) (x : Seat)
    (h : x.ok codes s R) :
    x.lo codes s R ≤ x.off codes s R ∧ x.off codes s R < x.hi codes s R := by
  cases x with
  | tail r q => exact ⟨Nat.zero_le _, lt_mul r q _ _ h.1 h.2⟩
  | word r j =>
    have b := lt_mul r j _ _ h.2.1 h.2.2
    have e := (word_eq codes s R h.1).1
    simp only [Seat.lo, Seat.hi, Seat.off]
    omega
  | pad i =>
    have : i < (stepsOf codes s R).pad := h
    simp only [Seat.lo, Seat.hi, Seat.off]
    omega
  | mask i =>
    have : i < (stepsOf codes s R).mask := h
    simp only [Seat.lo, Seat.hi, Seat.off]
    omega
  | maskTail r q =>
    have b := lt_mul r q _ _ h.1 h.2
    have e : (stepsOf codes s R).maskTails =
      s.maskRows * (codes.mask.getD s.maskCode default).r := rfl
    simp only [Seat.lo, Seat.hi, Seat.off]
    omega

theorem hi_le (codes : Codes) (s : OracleShape) (R : Option Ride) (x : Seat) :
    x.hi codes s R ≤ share codes s R (x.inE s) := by
  by_cases h3 : (s.mainDeg == 3) = true
  · cases x <;>
      simp only [Seat.hi, Seat.inE, share, dueMsg, Steps.main, h3, if_true] <;> omega
  · cases x <;>
      simp only [Seat.hi, Seat.inE, share, dueMsg, Steps.main, h3, Bool.false_eq_true, if_false,
        if_true] <;> omega

theorem mul_add_inj (c r q r' q' : Nat) (hq : q < c) (hq' : q' < c)
    (h : r * c + q = r' * c + q') : r = r' ∧ q = q' := by
  have hc : 0 < c := by omega
  have e1 : (r * c + q) / c = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hq, Nat.zero_add]
  have e2 : (r' * c + q') / c = r' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hq', Nat.zero_add]
  have hr : r = r' := by rw [← e1, h, e2]
  subst hr
  exact ⟨rfl, by omega⟩

/-- The step's number. -/
def Seat.kind : Seat → Nat
  | .tail .. => 0
  | .word .. => 1
  | .pad _ => 2
  | .mask _ => 3
  | .maskTail .. => 4

/-- In one message two places of one field and one number are of one step. -/
theorem kind_eq (codes : Codes) (s : OracleShape) (R : Option Ride) (x x' : Seat)
    (hx : x.ok codes s R) (hx' : x'.ok codes s R) (he : x.inE s = x'.inE s)
    (ho : x.off codes s R = x'.off codes s R) : x.kind = x'.kind := by
  have a := Seat.rng codes s R x hx
  have b := Seat.rng codes s R x' hx'
  have hwp := word_pad codes s R
  have hM : (stepsOf codes s R).main =
    (stepsOf codes s R).tails + (stepsOf codes s R).word + (stepsOf codes s R).pad := rfl
  rw [ho] at a
  by_cases h3 : (s.mainDeg == 3) = true
  · cases x <;> cases x' <;>
      first
        | rfl
        | (exfalso
           simp only [Seat.lo, Seat.hi, Seat.ok, h3, if_true] at a b hx hx'
           omega)
  · have h3' : (s.mainDeg == 3) = false := by simpa using h3
    cases x <;> cases x' <;>
      first
        | rfl
        | (exfalso
           simp only [Seat.inE, h3'] at he
           exact absurd he (by decide))
        | (exfalso
           simp only [Seat.lo, Seat.hi, Seat.ok, h3', Bool.false_eq_true, if_false,
             Nat.zero_add] at a b hx hx'
           omega)

/-- **In one message.** -/
theorem off_inj (codes : Codes) (s : OracleShape) (R : Option Ride) (x x' : Seat)
    (hx : x.ok codes s R) (hx' : x'.ok codes s R) (he : x.inE s = x'.inE s)
    (ho : x.off codes s R = x'.off codes s R) : x = x' := by
  have hk := kind_eq codes s R x x' hx hx' he ho
  cases x with
  | tail r q =>
    cases x' with
    | tail r' q' =>
      obtain ⟨rfl, rfl⟩ := mul_add_inj _ r q r' q' hx.2 hx'.2 ho
      rfl
    | _ => simp [Seat.kind] at hk
  | word r j =>
    cases x' with
    | word r' j' =>
      simp only [Seat.off] at ho
      obtain ⟨rfl, rfl⟩ := mul_add_inj _ r j r' j' hx.2.2 hx'.2.2 (by omega)
      rfl
    | _ => simp [Seat.kind] at hk
  | pad i =>
    cases x' with
    | pad i' =>
      simp only [Seat.off] at ho
      obtain rfl : i = i' := by omega
      rfl
    | _ => simp [Seat.kind] at hk
  | mask i =>
    cases x' with
    | mask i' =>
      simp only [Seat.off] at ho
      obtain rfl : i = i' := by omega
      rfl
    | _ => simp [Seat.kind] at hk
  | maskTail r q =>
    cases x' with
    | maskTail r' q' =>
      simp only [Seat.off] at ho
      obtain ⟨rfl, rfl⟩ := mul_add_inj _ r q r' q' hx.2 hx'.2 (by omega)
      rfl
    | _ => simp [Seat.kind] at hk

/-! ## Through the messages -/

theorem start_e (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) :
    (startR P ride (k + 1)).e =
      (startR P ride k).e + (dueMsg P.codes (shapeAt P k) (ride k)).e := by
  rw [startR_succ]

theorem start_f (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) :
    (startR P ride (k + 1)).f =
      (startR P ride k).f + (dueMsg P.codes (shapeAt P k) (ride k)).f := by
  rw [startR_succ]

/-- A seat's number lies below the next message's start, in its field. -/
theorem seat_next (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (x : Seat)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) :
    x.no P ride k <
      if x.inE (shapeAt P k) then (startR P ride (k + 1)).e else (startR P ride (k + 1)).f := by
  have a := (Seat.rng _ _ _ x hx).2
  have b := hi_le P.codes (shapeAt P k) (ride k) x
  unfold Seat.no
  unfold share at b
  rw [start_e, start_f]
  split_ifs at b ⊢ <;> omega

/-- **Inside the part's count.** -/
theorem seat_in (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (x : Seat)
    (hk : k < P.sent.size) (hx : x.ok P.codes (shapeAt P k) (ride k)) :
    x.no P ride k < if x.inE (shapeAt P k) then (dueR P ride).e else (dueR P ride).f := by
  have a := seat_next P ride k x hx
  have e := startR_mono P ride (k + 1) P.sent.size hk
  have f := startR_mono_f P ride (k + 1) P.sent.size hk
  unfold dueR
  split_ifs at a ⊢ <;> omega

/-- Of two messages the earlier one's numbers lie below the later one's. -/
theorem seat_lt (P : K1.Par) (ride : Nat → Option Ride) (k k' : Nat) (x x' : Seat) (hkk : k < k')
    (hx : x.ok P.codes (shapeAt P k) (ride k))
    (he : x.inE (shapeAt P k) = x'.inE (shapeAt P k')) : x.no P ride k < x'.no P ride k' := by
  have a := seat_next P ride k x hx
  have e := startR_mono P ride (k + 1) k' hkk
  have f := startR_mono_f P ride (k + 1) k' hkk
  rw [he] at a
  unfold Seat.no at a ⊢
  rw [he] at a ⊢
  split_ifs at a ⊢ <;> omega

/-- **TWO PLACES INSIDE THE SIZES, OF ONE FIELD, BEAR TWO NUMBERS.** -/
theorem seat_inj (P : K1.Par) (ride : Nat → Option Ride) (k k' : Nat) (x x' : Seat)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) (hx' : x'.ok P.codes (shapeAt P k') (ride k'))
    (he : x.inE (shapeAt P k) = x'.inE (shapeAt P k'))
    (hn : x.no P ride k = x'.no P ride k') : k = k' ∧ x = x' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact absurd hn (Nat.ne_of_lt (seat_lt P ride k k' x x' h hx he))
  · subst h
    refine ⟨rfl, off_inj _ _ _ x x' hx hx' he ?_⟩
    unfold Seat.no at hn
    rw [he] at hn
    exact Nat.add_left_cancel hn
  · exact absurd hn.symm (Nat.ne_of_lt (seat_lt P ride k' k x' x h hx' he.symm))

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.word_eq
#print axioms ProofFile.Honest.K1.word_pad
#print axioms ProofFile.Honest.K1.Seat.rng
#print axioms ProofFile.Honest.K1.hi_le
#print axioms ProofFile.Honest.K1.mul_add_inj
#print axioms ProofFile.Honest.K1.kind_eq
#print axioms ProofFile.Honest.K1.off_inj
#print axioms ProofFile.Honest.K1.start_e
#print axioms ProofFile.Honest.K1.start_f
#print axioms ProofFile.Honest.K1.seat_next
#print axioms ProofFile.Honest.K1.seat_in
#print axioms ProofFile.Honest.K1.seat_lt
#print axioms ProofFile.Honest.K1.seat_inj
#print axioms ProofFile.Honest.K1.Seat
#print axioms ProofFile.Honest.K1.Seat.inE
#print axioms ProofFile.Honest.K1.Seat.ok
#print axioms ProofFile.Honest.K1.Seat.off
#print axioms ProofFile.Honest.K1.Seat.no
#print axioms ProofFile.Honest.K1.Seat.lo
#print axioms ProofFile.Honest.K1.Seat.hi
#print axioms ProofFile.Honest.K1.share
#print axioms ProofFile.Honest.K1.Seat.kind
