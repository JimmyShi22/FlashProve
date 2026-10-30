-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Hands/HandsCore.lean: WHICH MASK ENTRIES A LEDGER HANDS OUT: A CLOSED FORM,
LAID ON THE LAWS BELOW. Plain functions on numbers and on a bare ledger; statements and proofs.

A message's mask table has 2 ^ k places for rows, of which the first R are real; entry number n
stands in row n % 2 ^ k. A ledger hands out, from its count "next" on, the numbers whose row is
real, each once, in rising order.

WHAT IS TAKEN AS IT LIES. OnBytes/G4/Seat.lean: stepLedger, takesOf: one taking and n
takings on a bare ledger. OnBytes/G4/LedgerLaws.lean: realBelow R k n (how many real numbers lie
below n: THE RANK), realBelow_next (the search keeps the rank), next_real (it ends at a real
number), realBelow_at (the rank at place p, row r). OnBytes/Iop/LedgerPlaces.lean: takenNo_eq: the
t-th number given, begun at the count 0, is the number of the t-th free entry in the format page's
order (Fmt/Places.lean: freeAt, entryNo); by its own head that file names no ledger.
WHAT IS NEW HERE: the LIST that n takings give FROM ANY COUNT, and the rank behind them.

Main names:
  realAt R k t: the real number of rank t: t / R * 2 ^ k + t % R.
  real_eq: a real number is realAt of its rank.
  takes_eq: THE CLOSED FORM: under 0 < R ≤ 2 ^ k: n takings from a ledger with R rows and the
    logarithm k give realAt at the ranks r, r + 1, ..., r + n - 1, r the rank of its count; they
    leave R and k, and a count of the rank r + n.
  takes_left: n takings take n of the entries that are left.
  realAt_lt: INSIDE THE TABLE: a rank below R * c gives a number below 2 ^ k * c. free_lt: the free
    entries of R rows of ell entries with a answers, 1 ≤ a ≤ ell, are fewer than R * ell.
  realAt_places, realAt_takenNo: at k = logUp m it is the format page's free entry number t, and
    takenNo (OnBytes/Iop/LedgerPlaces.lean).
  fresh_bounds: m mask rows, 0 < m: max m 1 = m and 0 < max m 1 ≤ 2 ^ ceilLog2 m: what a sending
    lays (freshLedger, OnBytes/Slice/BlkCalls.lean) meets the premises.
  slotsOf: the number of hidden values of a lookup with P parts of v bits (a copy, on numbers, of
    Face.slots, Johnson/Desc/First/Look/K3LookupGeneral.lean: NOT TIED TO IT HERE).
  The evaluations at the end: at the numbers of a key file of full size as the library writes them
    (Cb/Pv/KeyLookup/FullPub.lean; Johnson/Top/H/KeyRows.lean: nine mask rows, so k = 4; one mask
    row, so k = 0).

Limits. That a description's takeMasksP is takesOf on the ledger that the record holds is
Johnson/Top/H/Hands/HandsLoop.lean's [not in this library], from a law on one taking.
Not shown: that a sending leaves the
count 0; that nothing else takes an entry between the sending and the first lookup or between the
lookups; that the two messages differ. The numbers of the evaluations are typed here: nothing ties
them to a plan.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.G4.LedgerLaws
import OnBytes.Iop.LedgerPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Hands
open OnBytes OnBytes.G4 Fmt.Places

/-- The real number of rank t. -/
def realAt (R k t : Nat) : Nat := t / R * 2 ^ k + t % R

theorem realAt_add (R k q r : Nat) (hr : r < R) : realAt R k (q * R + r) = q * 2 ^ k + r := by
  have h0 : 0 < R := by omega
  unfold realAt
  rw [Nat.add_comm (q * R) r, Nat.add_mul_div_right _ _ h0, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, Nat.zero_add]

/-- A real number is realAt of its rank. -/
theorem real_eq {R k x : Nat} (hR : R ≤ 2 ^ k) (hx : x % 2 ^ k < R) :
    x = realAt R k (realBelow R k x) := by
  have hd : 2 ^ k * (x / 2 ^ k) + x % 2 ^ k = x := Nat.div_add_mod x (2 ^ k)
  have e := realBelow_at R k hR (x / 2 ^ k) (x % 2 ^ k)
    (Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k)))
  rw [hd, Nat.min_eq_left (Nat.le_of_lt hx)] at e
  rw [e, realAt_add _ _ _ _ hx, Nat.mul_comm]
  exact hd.symm

/-- **THE CLOSED FORM.** -/
theorem takes_eq {R k : Nat} (h1 : 0 < R) (h2 : R ≤ 2 ^ k) : ∀ (n : Nat) (l : Ledger),
    l.rows = R → l.logRows = k →
    (takesOf l n).1 = (List.range n).map (fun t => realAt R k (realBelow R k l.next + t)) ∧
      (takesOf l n).2.rows = R ∧ (takesOf l n).2.logRows = k ∧
      realBelow R k (takesOf l n).2.next = realBelow R k l.next + n
  | 0, _, e1, e2 => ⟨rfl, e1, e2, rfl⟩
  | n + 1, l, e1, e2 => by
    subst e1 e2
    have hreal := next_real l.rows l.logRows h1 (2 ^ l.logRows) l.next (Or.inr (Nat.sub_le _ _))
    have hc := realBelow_next l.rows l.logRows (2 ^ l.logRows) l.next
    have e : realBelow l.rows l.logRows (stepLedger l).2.next =
        realBelow l.rows l.logRows l.next + 1 := by
      show realBelow l.rows l.logRows
        (Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1) = _
      rw [realBelow, if_pos hreal, hc]
    obtain ⟨a1, a2, a3, a4⟩ := takes_eq h1 h2 n (stepLedger l).2 rfl rfl
    refine ⟨?_, a2, a3, ?_⟩
    · show (stepLedger l).1 :: (takesOf (stepLedger l).2 n).1 = _
      rw [a1, e, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      congr 1
      · show Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next = _
        rw [← hc]
        exact real_eq h2 hreal
      · refine List.map_congr_left fun t _ => ?_
        show realAt l.rows l.logRows (realBelow l.rows l.logRows l.next + 1 + t) =
          realAt l.rows l.logRows (realBelow l.rows l.logRows l.next + (t + 1))
        rw [show realBelow l.rows l.logRows l.next + 1 + t =
          realBelow l.rows l.logRows l.next + (t + 1) by omega]
    · show realBelow l.rows l.logRows (takesOf (stepLedger l).2 n).2.next = _
      rw [a4, e]
      omega

/-- n takings take n of the entries that are left. -/
theorem takes_left : ∀ (n : Nat) (l : Ledger), (takesOf l n).2.left = l.left - n
  | 0, _ => rfl
  | n + 1, l => by
    show (takesOf (stepLedger l).2 n).2.left = _
    rw [takes_left n]
    show l.left - 1 - n = l.left - (n + 1)
    omega

/-- **Inside the table**: a real number whose rank is below R * c lies below 2 ^ k * c: in a table
of 2 ^ k places for rows and c entries a row. -/
theorem realAt_lt {R k t c : Nat} (h1 : 0 < R) (h2 : R ≤ 2 ^ k) (ht : t < R * c) :
    realAt R k t < 2 ^ k * c := by
  have hq : t / R < c := (Nat.div_lt_iff_lt_mul h1).2 (by rw [Nat.mul_comm]; exact ht)
  have hr : t % R < 2 ^ k := Nat.lt_of_lt_of_le (Nat.mod_lt _ h1) h2
  have hm : (t / R + 1) * 2 ^ k ≤ c * 2 ^ k := Nat.mul_le_mul_right _ hq
  unfold realAt
  rw [Nat.succ_mul] at hm
  rw [Nat.mul_comm (2 ^ k) c]
  omega

/-- The free entries of R mask rows of ell entries with a answers (Send.freeMaskEntries,
OnBytes/Iop/Send.lean) are fewer than R * ell. -/
theorem free_lt {R ell a : Nat} (h1 : 0 < R) (ha : 1 ≤ a) (hl : a ≤ ell) :
    Send.freeMaskEntries R ell a < R * ell := by
  rw [freeMask_eq R ell a (by omega) hl]
  have e : R * ell = R * (ell - a) + R * a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hl]
  have h : R ≤ R * a := Nat.le_mul_of_pos_right _ ha
  omega

/-! ## In the format page's words -/

theorem realAt_places (m t : Nat) :
    realAt m (logUp m) t = entryNo m (freeAt m t).1 (freeAt m t).2 := by
  show t / m * 2 ^ logUp m + t % m = t % m + 2 ^ logUp m * (t / m)
  rw [Nat.mul_comm, Nat.add_comm]

theorem realAt_takenNo {m : Nat} (hm : 0 < m) (t : Nat) : realAt m (logUp m) t = takenNo m t := by
  rw [takenNo_eq hm, realAt_places]

/-- A fresh ledger's numbers meet the closed form's premises. -/
theorem fresh_bounds {m : Nat} (hm : 0 < m) :
    max m 1 = m ∧ 0 < max m 1 ∧ max m 1 ≤ 2 ^ ceilLog2 m := by
  have e : max m 1 = m := Nat.max_eq_left hm
  rw [e]
  exact ⟨rfl, hm, le_pow_ceilLog2 m⟩

/-! ## A lookup's number of hidden values, on numbers -/

/-- A copy of Face.slots at P parts of v bits each. -/
def slotsOf (planes P v d mu : Nat) : Nat :=
  7 + 6 * (planes - 2) + 5 * (P - 1) +
    ((List.replicate P v).map fun v => ((List.range v).map fun k => 2 * k + 5).sum).sum +
    ((List.range d).map fun l => 2 * (mu + l) + 5).sum +
    (1 + mu + 2 * d) + (1 + 2 * (mu + d) + 2 + 1)

/-! ## Evaluations -/

-- a small ledger: three real rows of four
example :
    (takesOf { next := 0, left := 9, rows := 3, logRows := 2 } 7).1 = [0, 1, 2, 4, 5, 6, 8] := by
  decide
example : (List.range 7).map (realAt 3 2) = [0, 1, 2, 4, 5, 6, 8] := by decide
example : (takesOf { next := 3, left := 9, rows := 3, logRows := 2 } 3).1 = [4, 5, 6] := by decide
-- the premise bears load: with no real row the search runs out and hands back an unreal number
example : (takesOf { next := 0, left := 9, rows := 0, logRows := 1 } 2).1 = [2, 5] := by decide

/-- The two lookups of a key file of full size: 17,817 and 17,116 hidden values. -/
theorem slots_full : slotsOf 40 12 36 8 6 = 17817 ∧ slotsOf 39 12 35 13 6 = 17116 := by
  decide +kernel

/-- What the own message's ledger (nine real rows of sixteen) hands to lookup 0: 17,793 entries, the
first 0, the tenth 16, the last 31,624; to lookup 1: 17,092 entries, from 31,632 to 62,016. -/
theorem own_full :
    17817 - 2 * 12 = 17793 ∧ 17116 - 2 * 12 = 17092 ∧ realAt 9 4 0 = 0 ∧ realAt 9 4 9 = 16 ∧
      realAt 9 4 (17793 - 1) = 31624 ∧ realAt 9 4 17793 = 31632 ∧
      realAt 9 4 (17793 + 17092 - 1) = 62016 := by
  decide

/-- Both lookups' entries are fewer than the ledger's free entries at nine rows of 4,096 places and
one answer, and more than eight rows would give. (Not: that they are all that is taken of it.) -/
theorem own_room : 17793 + 17092 ≤ 9 * (4096 - 1) + (9 - 1) ∧
    8 * (4096 - 1) + (8 - 1) < 17793 + 17092 := by
  decide

/-- At one mask row the real number of rank t is t. -/
theorem realAt_one (t : Nat) : realAt 1 0 t = t := by
  simp [realAt, Nat.mod_one]

end Fo.Hands

#print axioms Fo.Hands.real_eq
#print axioms Fo.Hands.takes_eq
#print axioms Fo.Hands.takes_left
#print axioms Fo.Hands.realAt_lt
#print axioms Fo.Hands.free_lt
#print axioms Fo.Hands.realAt_takenNo
#print axioms Fo.Hands.fresh_bounds
#print axioms Fo.Hands.slots_full
#print axioms Fo.Hands.own_full
