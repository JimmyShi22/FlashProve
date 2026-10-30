-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvKey2.lean

Lane5KvKey.lean, the segments with products: fm, fd (the score) and wl (the accumulator; the
denominator times the output). As there: A.lean's segKey IS the library's key2 and key3W at the
cells that stand in the verifier's matrices, for every commutative ring, under "NumsA S".

Main theorems: "score_eq", "wt_M", "wt_D", "acc_eq" (the three functions of the cells that nobody
sends), "cover_fst", "cover_snd" (the verifier's cover is the library's rowBlk, colBlk), "gp_M",
"gp_D" (the extended gap), "segKey_fm", "segKey_fd", "segKey_wl".

At fm and fd the call's shift must be the first layer's (the library has one shift for a segment).
-/
import Johnson.Road.Lane5KvKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A Finset
open OnBytes.Attention (Seg)
open Inst.Model.AttSeg

variable {R : Type} [CommRing R] (S : Attention.Shape) (cell : NameA → R)

theorem score_eq (N : NumsA S) (b g ti tj : ℕ) :
    score S cell (b / S.HA) (g * S.HA + b % S.HA) g ti tj =
      scV (dimOf S) (tC S cell) b g ti tj := by
  unfold score scV
  rw [sumN_sum, N.dh]
  refine sum_congr rfl fun n _ => ?_
  rw [← N.dh, ten_qry S cell N, ten_key S cell N]
  rfl

theorem wt_M (b π : ℕ) :
    wt S cell (b / S.HA) (b % S.HA) false π = wtV (tC S cell) .M b π := by
  unfold wt wtV w0 w1
  rw [asC_M, asC_M]

theorem wt_D (b π : ℕ) :
    wt S cell (b / S.HA) (b % S.HA) true π = wtV (tC S cell) .D b π := by
  unfold wt wtV w0 w1
  rw [asC_D, asC_D]

theorem cover_fst (N : NumsA S) (P s : ℕ) : (S.cover P s).1 = (dimOf S).rowBlk P s := by
  unfold Attention.Shape.cover Dim.rowBlk
  rw [N.nT]
  split_ifs <;> rfl

theorem cover_snd (P s : ℕ) : (S.cover P s).2 = (dimOf S).colBlk P s := by
  unfold Attention.Shape.cover Dim.colBlk
  split_ifs <;> rfl

theorem codeM_eq (N : NumsA S) (g P s i j : ℕ) :
    A.codeM S g P s i j = (dimOf S).codeM g P s i j := by
  unfold A.codeM Dim.codeM
  rw [N.hP, N.nT, N.B]

theorem codeD_eq (N : NumsA S) (g I i j : ℕ) : A.codeD S g I i j = (dimOf S).codeD g I i j := by
  unfold A.codeD Dim.codeD
  rw [N.nT, N.B]

theorem acc_eq (N : NumsA S) (b g i n : ℕ) :
    acc S cell (b / S.HA) (b % S.HA) g i n = AC (dimOf S) (tC S cell) b g i n := by
  unfold acc AC rowSum
  simp only [sumN_sum, wt_M, wt_D, ten_val S cell N, cover_fst S N, cover_snd, codeM_eq S N,
    codeD_eq S N]
  rw [N.hP, N.nT, N.B]
  congr 1
  · refine sum_congr rfl fun P _ => sum_congr rfl fun s _ => ?_
    split_ifs
    · refine sum_congr rfl fun j _ => ?_
      rw [Nat.mul_comm ((dimOf S).colBlk P s)]
      rfl
    · rfl
  · refine sum_congr rfl fun j _ => ?_
    rw [Nat.mul_comm (i / (dimOf S).B)]
    rfl

/-! ## The extended gap -/

theorem gp_M (N : NumsA S) (b κ : ℕ) :
    gapAt S cell (S.cf.sh.getD 0 0) false (b / S.HA) (b % S.HA) κ -
        ssAt S cell false (b / S.HA) (b % S.HA) κ =
      gp (scl := sclOf S) (dimOf S) (tC S cell) .M b κ := by
  have eS : κ / (S.B * S.B) % S.nT = (dimOf S).mS κ := by
    unfold Dim.mS
    rw [N.B, N.nT, Nat.div_div_eq_div_mul]
  have eP : κ / (S.B * S.B * S.nT) % S.hP = (dimOf S).mP κ := by
    unfold Dim.mP
    rw [N.B, N.nT, N.hP, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    simp only [Nat.mul_assoc]
  have eG : κ / (S.B * S.B * S.nT * S.hP) = (dimOf S).mG κ := by
    unfold Dim.mG
    rw [N.B, N.nT, N.hP, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    simp only [Nat.mul_assoc]
  have eI : κ / S.B % S.B = (dimOf S).mI κ := by
    unfold Dim.mI
    rw [N.B]
  have eJ : κ % S.B = (dimOf S).mJ κ := by
    unfold Dim.mJ
    rw [N.B]
  simp only [gapAt, ssAt, Bool.false_eq_true, if_false, eS, eP, eG, eI, eJ, gp]
  by_cases hE : (dimOf S).mS κ = S.nT - 1
  · have hE' : (dimOf S).EmptyM κ := by
      unfold Dim.EmptyM
      rw [hE, N.nT]
    rw [if_pos hE, if_pos hE, if_pos hE', sub_zero]
    show (((S.u0 * 2 ^ S.cf.sh.getD 0 0 : ℕ)) : R) =
      (((2 ^ S.cf.sh.getD 0 0 * (S.u0 : ℤ) : ℤ)) : R)
    push_cast
    ring
  · have hE' : ¬(dimOf S).EmptyM κ := by
      unfold Dim.EmptyM
      rw [← N.nT]
      exact hE
    rw [if_neg hE, if_neg hE, if_neg hE', mx_eq, score_eq S cell N, cover_fst S N, cover_snd, N.B]
    unfold Dim.iM Dim.jM
    rw [Nat.mul_comm (Dim.rowBlk _ _ _), Nat.mul_comm (Dim.colBlk _ _ _)]

theorem gp_D (N : NumsA S) (b κ : ℕ) :
    gapAt S cell (S.cf.sh.getD 0 0) true (b / S.HA) (b % S.HA) κ -
        ssAt S cell true (b / S.HA) (b % S.HA) κ =
      gp (scl := sclOf S) (dimOf S) (tC S cell) .D b κ := by
  have eD : κ / (S.B * S.B) % S.nT = (dimOf S).dI κ := by
    unfold Dim.dI
    rw [N.B, N.nT, Nat.div_div_eq_div_mul]
  have eG : κ / (S.B * S.B * S.nT) = (dimOf S).dG κ := by
    unfold Dim.dG
    rw [N.B, N.nT, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    simp only [Nat.mul_assoc]
  have eI : κ / S.B % S.B = (dimOf S).mI κ := by
    unfold Dim.mI
    rw [N.B]
  have eJ : κ % S.B = (dimOf S).mJ κ := by
    unfold Dim.mJ
    rw [N.B]
  simp only [gapAt, ssAt, if_true, eD, eG, eI, eJ, gp]
  rw [mx_eq, score_eq S cell N, N.B]
  unfold Dim.iD Dim.jD Dim.MaskedD
  rw [Nat.mul_comm (Dim.dI _ _)]
  have hOm : (((S.shd (S.cf.sh.getD 0 0)).Om : ℕ) : R) =
      ((Om (scl := sclOf S) (dimOf S) : ℤ) : R) := by
    have h1 : (((S.shd (S.cf.sh.getD 0 0)).Om : ℕ) : ℤ) = Om (scl := sclOf S) (dimOf S) := by
      show (((2 * S.Smax + S.u0 * 2 ^ S.cf.sh.getD 0 0 : ℕ)) : ℤ) =
        2 * Inst.Model.Smax + 2 ^ S.cf.sh.getD 0 0 * (S.u0 : ℤ)
      rw [← N.Sm]
      push_cast
      ring
    rw [← h1]
    push_cast
    rfl
  rw [hOm]
  ring

/-! ## The segments -/

theorem segKey_fm (N : NumsA S) (b κ : ℕ) :
    segKey S cell (S.cf.sh.getD 0 0) .fm (b / S.HA) (b % S.HA) κ =
      key2 (scl := sclOf S) (dimOf S) (tC S cell) .M b κ := by
  show gapAt S cell (S.cf.sh.getD 0 0) false (b / S.HA) (b % S.HA) κ -
      ssAt S cell false (b / S.HA) (b % S.HA) κ -
      (asC S cell 0 (b / S.HA) (b % S.HA) false κ + 128) -
      256 * (asC S cell 1 (b / S.HA) (b % S.HA) false κ + 128) +
      ((2 ^ 32 : ℕ) : R) * asC S cell 2 (b / S.HA) (b % S.HA) false κ +
      ((2 ^ 33 : ℕ) : R) * wt S cell (b / S.HA) (b % S.HA) false κ = _
  rw [gp_M S cell N, asC_M, asC_M, asC_M, wt_M]
  unfold key2 rm r0 r1 flV
  push_cast
  ring

theorem segKey_fd (N : NumsA S) (b κ : ℕ) :
    segKey S cell (S.cf.sh.getD 0 0) .fd (b / S.HA) (b % S.HA) κ =
      key2 (scl := sclOf S) (dimOf S) (tC S cell) .D b κ := by
  show gapAt S cell (S.cf.sh.getD 0 0) true (b / S.HA) (b % S.HA) κ -
      ssAt S cell true (b / S.HA) (b % S.HA) κ -
      (asC S cell 0 (b / S.HA) (b % S.HA) true κ + 128) -
      256 * (asC S cell 1 (b / S.HA) (b % S.HA) true κ + 128) +
      ((2 ^ 32 : ℕ) : R) * asC S cell 2 (b / S.HA) (b % S.HA) true κ +
      ((2 ^ 33 : ℕ) : R) * wt S cell (b / S.HA) (b % S.HA) true κ = _
  rw [gp_D S cell N, asC_D, asC_D, asC_D, wt_D]
  unfold key2 rm r0 r1 flV
  push_cast
  ring

theorem segKey_wl (N : NumsA S) (sh b κ : ℕ) :
    segKey S cell sh .wl (b / S.HA) (b % S.HA) κ =
      key3W (dimOf S) (tC S cell) (κ / (dimOf S).ch / (dimOf S).T / (dimOf S).nG) b
        (κ / (dimOf S).ch / (dimOf S).T % (dimOf S).nG) (κ / (dimOf S).ch % (dimOf S).T)
        (κ % (dimOf S).ch) := by
  simp only [segKey]
  rw [den_eq, acc_eq S cell N, ten_out S cell N, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  unfold key3W RE
  rw [← rh_eq, ← rhp_eq, N.dh, N.T, N.G]
  split_ifs <;> ring

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.acc_eq
#print axioms OnBytes.Road.L5.segKey_fm
#print axioms OnBytes.Road.L5.segKey_fd
#print axioms OnBytes.Road.L5.segKey_wl
