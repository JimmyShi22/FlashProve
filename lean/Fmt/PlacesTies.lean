-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Fmt/PlacesTies.lean: functions of Fmt/Places.lean proved equal to like texts elsewhere in Fmt/.

1. What the file contains.
    Against another text's function:
    `logUp_eq_M2`: `logUp` is `Fmt.M2.clog` (Fmt/M2Types.lean).
    `cubeOf_eq`: `Fmt.M2.cubeOf` is `cubeBits`, for a message with a main row.
    `nCoord_eq`: `Fmt.M1.nCoord` of the two tables' bits is `cubeBits`, for a message with both.
    `padAt_eq`: `Fmt.M2.padAt` is `entryNo` at `padRow` without mask rows.
    `hiAt_high`, `hiAt_low`: `Fmt.M3.hiAt` is `entryNo` of `vecAt`, in both ways of laying a vector.
    `ledger_eq`: `Fmt.M1.ledger` lists the numbers of the free entries of one mask row, at one
      answer.
    `endNo_takes`: with K + 1 variables of two scalars each, `endNo` at 2 is `Fmt.M1.pscTakes`.
    Closed forms, typed after the comment at the head of Fmt/M1Psc.lean (rows (U), (E_1), (E_2)),
    with K + 1 variables of two scalars each: `sk_replicate`; `hidPos_replicate`: 2 l + deg - 1;
    `hidPos_replicate_last`: 2 K + deg; `endNo_replicate`: 2 K + 3 + i.
2. What is checked when the file compiles. The proofs.
3. Theorems. As listed. No Mathlib is below this file.
4. What is not claimed. No tie to `Fmt.M1.maskU`'s text, which is written by cases on the entry's
   number, nor to `loAt`, `seedLen`, `layBlocks`. The ties to the verifier program's texts lie in
   OnBytes/Iop/SendPlaces.lean and OnBytes/Iop/LedgerPlaces.lean, because Fmt/ may not import
   OnBytes/.

Terms: lean/GLOSSARY.md.
-/
import Fmt.PlacesLaws
import Fmt.M2Send
import Fmt.M3Types
import Fmt.M1Psc

namespace Fmt.Places

theorem logUp_eq_M2 (n : Nat) : logUp n = Fmt.M2.clog n := rfl

theorem cubeOf_eq (lgl lgz : Nat) (m : Fmt.M2.Mem) (h : m.rows ≠ 0) :
    Fmt.M2.cubeOf lgl lgz m = cubeBits m.rows lgl m.masks lgz := by
  by_cases hz : m.masks = 0 <;>
    simp [Fmt.M2.cubeOf, cubeBits, tableBits, h, hz, ← logUp_eq_M2]

theorem nCoord_eq {M Z : Nat} (a z : Nat) (hM : M ≠ 0) (hZ : Z ≠ 0) :
    Fmt.M1.nCoord (tableBits M a) (tableBits Z z) = cubeBits M a Z z := by
  simp [Fmt.M1.nCoord, cubeBits, hM, hZ]

theorem padAt_eq (m : Fmt.M2.Mem) (p : Nat) :
    Fmt.M2.padAt m p = entryNo m.rows (padRow m.rows 0) p := by
  simp [Fmt.M2.padAt, entryNo, padRow, ← logUp_eq_M2]

theorem hiAt_high (R aP e : Nat) :
    Fmt.M3.hiAt true (logUp R) aP e =
      entryNo R (vecAt true (2 ^ aP) R e).1 (vecAt true (2 ^ aP) R e).2 := by
  simp [Fmt.M3.hiAt, entryNo, vecAt]

theorem hiAt_low (aR aP l e : Nat) :
    Fmt.M3.hiAt false aR aP e =
      entryNo (2 ^ aR) (vecAt false l (2 ^ aR) e).1 (vecAt false l (2 ^ aR) e).2 := by
  simp only [Fmt.M3.hiAt, entryNo, vecAt, logUp_two_pow]
  simp only [Bool.false_eq_true, if_false]
  exact (Nat.mod_add_div e (2 ^ aR)).symm

theorem ledger_eq (Az : Nat) :
    Fmt.M1.ledger Az =
      (List.range (freeCount 1 (2 ^ Az) 1)).map
        fun k => entryNo 1 (freeAt 1 k).1 (freeAt 1 k).2 := by
  have h : ¬ (2 ^ Az < 1) := by have := Nat.two_pow_pos Az; omega
  simp [Fmt.M1.ledger, freeCount, entryNo, freeAt, logUp, h, Nat.mod_one]

theorem sk_replicate {n l : Nat} (k : Nat) (h : l ≤ n) : sk (List.replicate n k) l = l * k := by
  unfold sk
  rw [List.take_replicate, Nat.min_eq_left h, List.sum_replicate_nat]

/-- A variable but the last: degree deg has the entry 2 l + deg - 1. -/
theorem hidPos_replicate {K l : Nat} (deg : Nat) (h : l < K) :
    hidPos (List.replicate (K + 1) 2) l deg = 2 * l + deg - 1 := by
  unfold hidPos
  rw [List.length_replicate, if_pos (by omega), sk_replicate 2 (by omega)]
  omega

/-- The last variable: degree deg has the entry 2 K + deg. -/
theorem hidPos_replicate_last (K deg : Nat) :
    hidPos (List.replicate (K + 1) 2) K deg = 2 * K + deg := by
  unfold hidPos
  rw [List.length_replicate, if_neg (by omega), sk_replicate 2 (by omega)]
  omega

/-- End value i has the number 2 K + 3 + i. -/
theorem endNo_replicate (K i : Nat) : endNo (List.replicate (K + 1) 2) i = 2 * K + 3 + i := by
  unfold endNo
  rw [List.sum_replicate_nat]
  omega

theorem endNo_takes (K : Nat) : endNo (List.replicate (K + 1) 2) 2 = Fmt.M1.pscTakes K := by
  rw [endNo_replicate]
  unfold Fmt.M1.pscTakes
  omega

end Fmt.Places
