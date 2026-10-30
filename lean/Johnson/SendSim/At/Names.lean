-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Names.lean: every slot within the sizes that is not in a tail has a name in
CoinN; so the sender's coins, read by readC and placed again by put, are the same coins at every
such slot.
Terms: Johnson/SendSim/At/Sim.lean; put, slot, name, number: Johnson/SendSim/At/Bridge.lean, "Terms
of the instance". Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. No statement has a premise on P or ride. In each, x is a slot of oracle
message k that is within the sizes (Seat.ok) and not in a tail (inMsg), and t is a coordinate that
the slot's field has: t < 3, and t = 0 in the base field.
  exists_name      Some name n in CoinN has the oracle message k, the slot x and the coordinate t.
  coinAt_put_read  coinAt reads the same at (x, t) off put (readC c).1 as off c.
  coinNo_put_read  The same for the whole coin at the slot's number, read in the extension field
                   (coinNo).

How it fits. Johnson/SendSim/At/Split.lean uses coinNo_put_read for entry_split, which serves
rowsExact (Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean).
Johnson/SendSim/At/Cells.lean, Johnson/SendSim/At/PadsOf.lean, Johnson/SendSim/At/PadSeat.lean and
Johnson/SendSim/At/CutProof.lean use exists_name. The proofs rest on coinAt_put and coinAt_put_tail
(Johnson/SendSim/At/Put.lean), word_eq (Johnson/Desc/ProofFile/Honest/K1/Seat.lean) and lt_mul
(Johnson/Desc/ProofFile/Honest/K1/CoinsIn.lean). coinNo is defined in
Johnson/Desc/ProofFile/Honest/K1/SeatReads.lean.

The other names.
  inMsg            the slot is an entry of a main row, an entry of a pad or a mask coin: not in a
                   tail.
  lt_dg, co_fin    a coordinate that the field has is below dg P k; co of a coordinate's value is
                   that coordinate.
  coinNo_put_tail  at the slot of an entry of a tail, the coin of put s is 0 at the entry's
                   coordinate. It completes the account of put; no file uses it.
-/
import Johnson.Desc.ProofFile.Honest.K1.SeatReads
import Johnson.SendSim.At.Put

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- The slot is not in a tail: it is an entry of a main row, an entry of a pad or a mask coin. -/
def inMsg : Seat → Bool
  | .tail .. | .maskTail .. => false
  | .word .. | .pad _ | .mask _ => true

variable (P : K1.Par) (ride : Nat → Option Ride)

theorem lt_dg (k : ℕ) (x : Seat) (t : ℕ) (ht : t < 3)
    (hx : x.inE (shapeAt P k) = ((shapeAt P k).mainDeg == 3))
    (h0 : x.inE (shapeAt P k) = false → t = 0) : t < dg P k := by
  unfold dg
  cases h3 : ((shapeAt P k).mainDeg == 3)
  · rw [h0 (hx.trans h3)]
    simp
  · simpa using ht

/-- A slot x of oracle message k that is within the sizes and not in a tail, with a coordinate t < 3
that is 0 if the slot's coin is in the base field, is the slot and coordinate of some name in CoinN.
-/
theorem exists_name (k : Fin P.sent.size) (x : Seat) (t : ℕ)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg x = true) (ht : t < 3)
    (h0 : x.inE (shapeAt P k) = false → t = 0) :
    ∃ n : CoinN P ride, n.1 = k ∧ seatC P ride n = (x, t) := by
  cases x with
  | tail r q => cases hm
  | maskTail r q => cases hm
  | word r j =>
    obtain ⟨hw, hr, hj⟩ := hx
    have e := (word_eq P.codes (shapeAt P k) (ride k) hw).1
    have hl : 0 < (P.codes.base.getD (shapeAt P k).code default).ell := by omega
    have hi : r * (P.codes.base.getD (shapeAt P k).code default).ell + j < (stp P ride k).word := by
      unfold stp
      rw [e]
      exact lt_mul r j _ _ hr hj
    refine ⟨⟨k, .inl (.inl ⟨_, hi⟩, ⟨t, lt_dg P k _ t ht rfl h0⟩)⟩, rfl, ?_⟩
    have e1 : (r * (P.codes.base.getD (shapeAt P k).code default).ell + j) /
        (P.codes.base.getD (shapeAt P k).code default).ell = r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (r * (P.codes.base.getD (shapeAt P k).code default).ell + j) %
        (P.codes.base.getD (shapeAt P k).code default).ell = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [seatC, e1, e2]
  | pad i => exact ⟨⟨k, .inl (.inr ⟨i, hx⟩, ⟨t, lt_dg P k _ t ht rfl h0⟩)⟩, rfl, rfl⟩
  | mask i => exact ⟨⟨k, .inr (⟨i, hx⟩, ⟨t, ht⟩)⟩, rfl, rfl⟩

/-- At such a slot and coordinate, coinAt reads the same off put (readC c).1 as off the sender's
coins c. -/
theorem coinAt_put_read (c : Cs (dueR P ride)) (k : Fin P.sent.size) (x : Seat) (t : ℕ)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg x = true) (ht : t < 3)
    (h0 : x.inE (shapeAt P k) = false → t = 0) :
    coinAt P ride (put P ride (readC P ride c).1) k (x, t) = coinAt P ride c k (x, t) := by
  obtain ⟨n, hk, hs⟩ := exists_name P ride k x t hx hm ht h0
  have h := coinAt_put P ride (readC P ride c).1 n
  rw [hs, hk] at h
  rw [h]
  show coinAt P ride c n.1 (seatC P ride n) = _
  rw [hs, hk]

theorem co_fin (t : Fin 3) : co t.val = t := Fin.ext (co_val t.isLt)

/-- At a slot x that is within the sizes and not in a tail, put (readC c).1 and c have the same coin
at the slot's number. -/
theorem coinNo_put_read (c : Cs (dueR P ride)) (k : Fin P.sent.size) (x : Seat)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg x = true) :
    coinNo (put P ride (readC P ride c).1) (x.inE (shapeAt P k)) (x.no P ride k) =
      coinNo c (x.inE (shapeAt P k)) (x.no P ride k) := by
  unfold coinNo
  cases hE : x.inE (shapeAt P k)
  · have h := coinAt_put_read P ride c k x 0 hx hm (by norm_num) fun _ => rfl
    unfold coinAt at h
    simp only [hE, Bool.false_eq_true, if_false] at h ⊢
    rw [h]
  · simp only [if_true]
    refine ext_crd fun t => ?_
    have h := coinAt_put_read P ride c k x t.val hx hm t.isLt fun e => by rw [hE] at e; cases e
    unfold coinAt at h
    simp only [hE, if_true, co_fin] at h
    exact h

/-- At the slot of an entry of a row's tail, the coin of put s has 0 at the entry's coordinate. -/
theorem coinNo_put_tail (s : CoinN P ride → GF) (ρ : RowN P) (q : Fin (codeAt P ρ).r) :
    crd (co (seatT P ρ q.val).2)
      (coinNo (put P ride s) ((seatT P ρ q.val).1.inE (shapeAt P ρ.1))
        ((seatT P ρ q.val).1.no P ride ρ.1)) = 0 := by
  have h := coinAt_put_tail P ride s ρ q
  unfold coinAt at h
  unfold coinNo
  cases hE : (seatT P ρ q.val).1.inE (shapeAt P ρ.1)
  · simp only [hE, Bool.false_eq_true, if_false] at h ⊢
    rw [h, map_zero, crd_zero]
  · simp only [hE, if_true] at h ⊢
    exact h

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.exists_name
#print axioms OnBytes.SendSim.At.coinNo_put_read
#print axioms OnBytes.SendSim.At.coinNo_put_tail
