-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Rates.lean: error counts of a written round, as probabilities.

The library's theory counts the bad verifier messages of a round among the typed values that the
round draws. In the protocol that a file holds, a verifier message is the round's hash blocks, with
test bits where the round asks for work. At most w written messages go to one typed value, so e
bad values become at most e * w bad written messages. This file shows that the share of bad
messages grows by no more than the bias of the format's sampler, a factor 1 + 2^-128
(`kapSl 128`, Iop/DrawOf.lean) for each of the round's hash blocks, and it counts the typed values.

Main definitions: `nVals`.
Main theorems.
 `card_vals_all`, `card_vals`   the number of typed values of a list of draws is `nVals`.
 `card_wRound`      the number of written verifier messages: all strings of blocks, times two to
                    the number of test bits.
 `below_round_work`  a share c of bad values gives a share of bad written messages of at most c
                    times the bias, divided by two to the number of test bits.
 `below_round_div`  the same statement, written with the division.
 `below_round`      the same without the gain from the test bits.
 `share_le`         a count of e among N values as a share n / D.

Not claimed here: any bound on an error count itself. Nothing on the hash function: a share is a
count among all strings of hash blocks and test bits.
-/
import OnBytes.Slice.Draws

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- The number of typed values of a list of draws. An element has three coordinates below the
size p of the base field, so there are p^3 elements, and p^3 - 1 other than 0. A position of k
bits has 2^k values, a matrix entry is a pair of bits, and a sealing has four words of 64 bits. -/
def nVals : List Fmt.Draw → ℕ
  | [] => 1
  | .elem :: ds => Fmt.Fld.two.p ^ 3 * nVals ds
  | .elemNZ :: ds => (Fmt.Fld.two.p ^ 3 - 1) * nVals ds
  | .pos k :: ds => 2 ^ k * nVals ds
  | .trits n :: ds => 4 ^ n * nVals ds
  | .sealed :: ds => (2 ^ 64) ^ 4 * nVals ds

/-- The number of triples of numbers below n. The size n is a variable, so that no step of the
proof is a computation with a number as large as the size of the base field. -/
theorem card_triples (n : ℕ) : Nat.card (Fin n × Fin n × Fin n) = n ^ 3 := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, pow_succ, pow_two,
    mul_assoc]

/-- The typed elements of the extension field. -/
theorem card_EV : Nat.card (EV .two) = Fmt.Fld.two.p ^ 3 := card_triples Fmt.Fld.two.p

/-- A finite type without one of its elements. -/
theorem card_without {α : Type} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq a

/-- The typed elements other than 0. -/
theorem card_NZ : Nat.card (NZ .two) = Fmt.Fld.two.p ^ 3 - 1 := by
  rw [← card_EV]
  exact card_without (zF .two, zF .two, zF .two)

/-- The number of typed values, for every list of draws. -/
theorem card_vals_all : ∀ ds : List Fmt.Draw, Nat.card (Vals .two ds) = nVals ds
  | [] => by
      show Nat.card Unit = 1
      exact Nat.card_unique
  | .elem :: ds => by
      show Nat.card (EV .two × Vals .two ds) = Fmt.Fld.two.p ^ 3 * nVals ds
      rw [Nat.card_prod, card_EV, card_vals_all ds]
  | .elemNZ :: ds => by
      show Nat.card (NZ .two × Vals .two ds) = (Fmt.Fld.two.p ^ 3 - 1) * nVals ds
      rw [Nat.card_prod, card_NZ, card_vals_all ds]
  | .pos k :: ds => by
      show Nat.card (Fin (2 ^ k) × Vals .two ds) = 2 ^ k * nVals ds
      rw [Nat.card_prod, card_vals_all ds, Nat.card_eq_fintype_card, Fintype.card_fin]
  | .trits n :: ds => by
      show Nat.card ((Fin n → Bool × Bool) × Vals .two ds) = 4 ^ n * nVals ds
      rw [Nat.card_prod, card_vals_all ds, Nat.card_eq_fintype_card, Fintype.card_fun,
        Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  | .sealed :: ds => by
      show Nat.card ((Fin 4 → UInt64) × Vals .two ds) = (2 ^ 64) ^ 4 * nVals ds
      rw [Nat.card_prod, card_vals_all ds, Nat.card_eq_fintype_card, Fintype.card_fun,
        card_u64, Fintype.card_fin]

/-- The number of typed values of a list of draws, stated under `PlainDraws` (elements, positions
and empty draws of matrix entries alone). The hypothesis is not used. -/
theorem card_vals : ∀ ds : List Fmt.Draw, PlainDraws ds → Nat.card (Vals .two ds) = nVals ds :=
  fun ds _ => card_vals_all ds

/-- The typed values of a run of n positions of k bits, and of what is drawn after them. -/
theorem nVals_rep (k n : ℕ) (rest : List Fmt.Draw) :
    nVals (List.replicate n (Fmt.Draw.pos k) ++ rest) = (2 ^ k) ^ n * nVals rest := by
  induction n with
  | zero => rw [pow_zero, one_mul]; rfl
  | succ n ih =>
      show 2 ^ k * nVals (List.replicate n (Fmt.Draw.pos k) ++ rest) = _
      rw [ih, pow_succ]
      ring

/-- A count as a share: if e * D is at most n * N, then e of N values are a share of at most
n / D. -/
theorem share_le (e n D N : ℕ) (hD : 0 < D) (h : e * D ≤ n * N) :
    (e : ℝ≥0∞) ≤ ((n : ℝ≥0∞) / (D : ℝ≥0∞)) * (N : ℝ≥0∞) := by
  have hD0 : (D : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  have hDt : (D : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top D
  have hc : (e : ℝ≥0∞) * (D : ℝ≥0∞) ≤ (n : ℝ≥0∞) * (N : ℝ≥0∞) := by exact_mod_cast h
  calc (e : ℝ≥0∞) = (e : ℝ≥0∞) * (D : ℝ≥0∞) / (D : ℝ≥0∞) :=
        (ENNReal.mul_div_cancel_right hD0 hDt).symm
    _ ≤ (n : ℝ≥0∞) * (N : ℝ≥0∞) / (D : ℝ≥0∞) := ENNReal.div_le_div_right hc _
    _ = (n : ℝ≥0∞) / (D : ℝ≥0∞) * (N : ℝ≥0∞) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- The number of written verifier messages of a round. -/
theorem card_wRound (d : PQ.RD) : Fintype.card (wRound d).Chal =
    Fintype.card (Fin (bsRound .two d.entry d.kind).b → Dig 256) * 2 ^ d.entry.work :=
  GChal.card_eq d.entry.work _

/-- From a share of bad typed values to a share of bad written verifier messages, with the gain
from the test bits: of the written messages over one string of blocks only one passes the test.
Asked: the round's entry has `logN` at most 64. -/
theorem below_round_work (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (e : ℕ) (c : ℝ≥0∞)
    (h : (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) * 2 ^ d.entry.work ≤
      (kapSl 128 ^ (bsRound .two d.entry d.kind).b * c) *
        (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have hr := (planDraws_law .two d.entry d.kind hlog).1.ratio
  rw [card_wRound, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc]
  refine mul_le_mul' ?_ le_rfl
  calc (e : ℝ≥0∞) * ((bsRound .two d.entry d.kind).w : ℝ≥0∞)
      ≤ (c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) *
          ((bsRound .two d.entry d.kind).w : ℝ≥0∞) := mul_le_mul' h le_rfl
    _ = c * (((bsRound .two d.entry d.kind).w : ℝ≥0∞) *
          (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) := by ring
    _ ≤ c * (kapSl 128 ^ (bsRound .two d.entry d.kind).b *
          (Fintype.card (Fin (bsRound .two d.entry d.kind).b → Dig 256) : ℝ≥0∞)) :=
        mul_le_mul' le_rfl hr
    _ = kapSl 128 ^ (bsRound .two d.entry d.kind).b * c *
          (Fintype.card (Fin (bsRound .two d.entry d.kind).b → Dig 256) : ℝ≥0∞) := by ring

/-- The same, with the gain from the test bits as a division of the share. -/
theorem below_round_div (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (e : ℕ) (c : ℝ≥0∞)
    (h : (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (kapSl 128 ^ (bsRound .two d.entry d.kind).b * (c / 2 ^ d.entry.work)) *
        (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have h0 : (2 : ℝ≥0∞) ^ d.entry.work ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ d.entry.work ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞)
      = ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) * 2 ^ d.entry.work /
          2 ^ d.entry.work := (ENNReal.mul_div_cancel_right h0 ht).symm
    _ ≤ (kapSl 128 ^ (bsRound .two d.entry d.kind).b * c) *
          (Fintype.card (wRound d).Chal : ℝ≥0∞) / 2 ^ d.entry.work :=
        ENNReal.div_le_div_right (below_round_work d hlog e c h) _
    _ = (kapSl 128 ^ (bsRound .two d.entry d.kind).b * (c / 2 ^ d.entry.work)) *
          (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- From a share of bad typed values to a share of bad written verifier messages. -/
theorem below_round (d : Run.PQ.RD) (hlog : d.entry.logN ≤ 64) (e : ℕ) (c : ℝ≥0∞)
    (h : (e : ℝ≥0∞) ≤ c * (Nat.card (Run.Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) :
    ((e * (Run.bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (Iop.kapSl 128 ^ (Run.bsRound .two d.entry d.kind).b * c) *
        (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  refine _root_.le_trans ?_ (below_round_work d hlog e c h)
  exact le_mul_of_one_le_right (_root_.zero_le _) (one_le_pow₀ (by norm_num))

end OnBytes.Slice

#print axioms OnBytes.Slice.card_vals_all
#print axioms OnBytes.Slice.card_vals
#print axioms OnBytes.Slice.below_round_work
#print axioms OnBytes.Slice.below_round_div
#print axioms OnBytes.Slice.share_le
#print axioms OnBytes.Slice.below_round
