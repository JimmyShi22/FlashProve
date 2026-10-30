-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CountRow.lean: the row on the number of keys of the course over
the field, read, is the description's.

The course over the field is our text of the program's lookup
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean; that the program's run, read in the field, is this
course is shown, under conditions on public data, in files that are not in this library yet). Its
last row of a lookup says that the counts add up to the number of keys that are no padding. The
row's vector on the table of bits has product form: the pair (1, 2^(2^t)) for bit t of a plane's
number, the pair (1, 1) for each bit of a row's number (`cntRowF`,
Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean). The description's row has the coefficient 2^p at
the entry of plane p (`Dat.numRow`, Cb/Pv/KeyLookup/Letters.lean).

Main names:
  `pairsAt_pows`: the product over the low n bits of a number N of 2^(2^(t0 + t)) at the bits that
  are set is 2^(2^t0 (N mod 2^n)).
  `numRow_eq`: `A.numRow = rdRow A sl (cntRowF D)`, if the course has the description's public
  record and there are at most 2^mu real planes.

Limits. One row, of our text: nothing on the program's own row.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

open OnBytes OnBytes.Slice Finset Cb.LdLkp

/-- The first pair. -/
theorem pairsAt_cons (p : GE × GE) (ps : List (GE × GE)) (n : ℕ) :
    pairsAt (p :: ps) n = (if n % 2 = 1 then p.2 else p.1) * pairsAt ps (n / 2) := rfl

/-- Pairs (1, 1) give 1. -/
theorem pairsAt_ones : ∀ (d N : ℕ), pairsAt (List.replicate d ((1 : GE), (1 : GE))) N = 1
  | 0, _ => rfl
  | d + 1, N => by
    rw [List.replicate_succ, pairsAt_cons, pairsAt_ones d, ite_self, mul_one]

/-- **The pairs (1, 2^(2^(t0 + t))), t < n, give 2^(2^t0 (N mod 2^n)).** -/
theorem pairsAt_pows : ∀ (n t0 N : ℕ) (tl : List (GE × GE)),
    pairsAt ((List.range n).map (fun t => ((1 : GE), (2 : GE) ^ 2 ^ (t0 + t))) ++ tl) N =
      2 ^ (2 ^ t0 * (N % 2 ^ n)) * pairsAt tl (N / 2 ^ n)
  | 0, t0, N, tl => by
    rw [List.range_zero, List.map_nil, List.nil_append, pow_zero, Nat.mod_one, Nat.mul_zero,
      pow_zero, _root_.one_mul, Nat.div_one]
  | n + 1, t0, N, tl => by
    have e : (List.range (n + 1)).map (fun t => ((1 : GE), (2 : GE) ^ 2 ^ (t0 + t))) =
        ((1 : GE), (2 : GE) ^ 2 ^ t0) ::
          (List.range n).map (fun t => ((1 : GE), (2 : GE) ^ 2 ^ (t0 + 1 + t))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      refine congrArg _ (List.map_congr_left fun t _ => ?_)
      show ((1 : GE), (2 : GE) ^ 2 ^ (t0 + (t + 1))) = _
      rw [Nat.add_comm t 1, Nat.add_assoc]
    have h1 : N / 2 / 2 ^ n = N / 2 ^ (n + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ']
    have h2 : N % 2 ^ (n + 1) = N % 2 + 2 * (N / 2 % 2 ^ n) := by rw [pow_succ', Nat.mod_mul]
    rw [e, List.cons_append, pairsAt_cons, pairsAt_pows n (t0 + 1) (N / 2) tl, h1, h2]
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · rw [h, if_neg (by decide), _root_.one_mul]
      have x : 2 ^ (t0 + 1) * (N / 2 % 2 ^ n) = 2 ^ t0 * (0 + 2 * (N / 2 % 2 ^ n)) := by ring
      rw [x]
    · rw [h, if_pos rfl, ← mul_assoc, ← pow_add]
      have x : 2 ^ t0 + 2 ^ (t0 + 1) * (N / 2 % 2 ^ n) = 2 ^ t0 * (1 + 2 * (N / 2 % 2 ^ n)) := by
        ring
      rw [x]

/-- The vector of the row on the number of keys, at the place of plane p and row u. -/
theorem cnt_at (mu d p u : ℕ) (hp : p < 2 ^ mu) :
    pairsAt (((List.range mu).map fun t => ((1 : GE), (2 : GE) ^ 2 ^ t)) ++
      List.replicate d (1, 1)) (p + 2 ^ mu * u) = 2 ^ p := by
  have h := pairsAt_pows mu 0 (p + 2 ^ mu * u) (List.replicate d ((1 : GE), (1 : GE)))
  simp only [Nat.zero_add, pow_zero, Nat.one_mul] at h
  rw [h, pairsAt_ones, mul_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]

variable (A : Dat GE) (sl : Slot → A.J)

/-- **The row on the number of keys.** -/
theorem numRow_eq (D : Dt) (hS : D.S = A.toPub) (hpl : A.pl ≤ 2 ^ A.mu) :
    A.numRow = rdRow A sl (cntRowF D) := by
  have hf : (fun i => ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range A.pl,
        if A.bAt u j = i then (2 : GE) ^ j else 0) =
      fun j => rdMF sl (cntRowF D).masks j +
        ((cntRowF D).maps.map fun a => a.1 * onCell A a.2 j).sum := by
    funext i
    show _ = rdMF sl [] i + ((1 : GE) * onCell A (((List.range D.S.mu).map fun t =>
      ((1 : GE), (2 : GE) ^ 2 ^ t)) ++ List.replicate D.S.d (1, 1)) i + 0)
    rw [rdMF_nil, zero_add, add_zero, _root_.one_mul, hS]
    unfold onCell
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p hp => ?_
    rw [cnt_at A.mu A.d p u (lt_of_lt_of_le (Finset.mem_range.1 hp) hpl)]
  have ht : (((A.allKeys - A.padCount : ℕ) : GE)) = (cntRowF D).target := by
    show _ = (((D.S.allKeys - D.S.padCount : ℕ) : GE))
    rw [hS]
  show (⟨_, _⟩ : Row GE A.J) = ⟨_, _⟩
  rw [hf, ht]

end Lk6.Mid

#print axioms Lk6.Mid.pairsAt_cons
#print axioms Lk6.Mid.pairsAt_ones
#print axioms Lk6.Mid.pairsAt_pows
#print axioms Lk6.Mid.cnt_at
#print axioms Lk6.Mid.numRow_eq
