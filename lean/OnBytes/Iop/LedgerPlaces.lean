-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Iop/LedgerPlaces.lean: the search Blk.nextRealRow of OnBytes/Iop/Ground.lean walks through
the free entries in the order of Fmt/Places.lean, and VectorLay.index of OnBytes/Iop/Tensor.lean is
the number of the entry that Fmt/Places.lean gives a vector's entry.

The format page says the order of an oracle message's free entries outright: entry 0 of row 0, entry
0 of row 1, and so on to the last row, then entry 1 of row 0 (Fmt.Places.freeAt). The program finds
the next free entry by a search: from the number after the last one taken it goes on to the next
number whose low bits name a real row (Blk.nextRealRow).

Main definition: takenNo m k: the k-th number that the search gives, begun at 0 and begun again each
time at the number after the last one given, with m rows, logUp m row bits and the fuel 2 ^ logUp m.
Main theorems: nextRealRow_skip (if the d numbers from n on name no real row, the next one does and
the fuel is above d, the search ends at n + d); nextRealRow_first, nextRealRow_row,
nextRealRow_entry, nextRealRow_freeAt (the start, and the step after a free entry); takenNo_eq (the
k-th number given is the number of the k-th free entry); VectorLay.index_high, VectorLay.index_low
(on a record written out); vectorLay_index_high, vectorLay_index_low (on the record that the program
makes of a shape).

What is not claimed. NO THEOREM HERE NAMES Ledger, Blk.takeMask OR Send.admit. That takenNo is what
a ledger hands out rests on four readings of the program's text: Send.admit fills a ledger with
next := 0, rows := max maskRows 1, logRows := ceilLog2 maskRows (OnBytes/Iop/Send.lean); it does so
only where there is a mask row, so rows is maskRows; Blk.takeMask calls nextRealRow l.rows l.logRows
(2 ^ l.logRows) l.next and stores the number given + 1 as next (OnBytes/Iop/Ground.lean); no other
text of the program writes a ledger. Nothing on the ledger's count left, or on who takes which
entry. For a vector: 2 ^ placeBits is the number of a row's entries only where that number is a
power of two (Codes.lengthsOk); the program lays a vector's weights by VectorLay.onTable and calls
index at single entries: nothing on onTable. The program does not import this file.
-/
import OnBytes.Iop.Foldeq
import Fmt.PlacesLaws

namespace OnBytes
open Fmt.Places

theorem nextRealRow_skip (rows q : Nat) : ∀ (d fuel n : Nat), d < fuel →
    (∀ i, i < d → ¬ (n + i) % 2 ^ q < rows) → (n + d) % 2 ^ q < rows →
    Blk.nextRealRow rows q fuel n = n + d
  | _, 0, _, hf, _, _ => absurd hf (Nat.not_lt_zero _)
  | 0, _ + 1, n, _, _, h => by
    have h' : n % 2 ^ q < rows := h
    rw [Blk.nextRealRow, if_pos h']
    rfl
  | d + 1, fuel + 1, n, hf, hs, h => by
    have h0 : ¬ n % 2 ^ q < rows := hs 0 (Nat.succ_pos d)
    rw [Blk.nextRealRow, if_neg h0]
    have e : ∀ i, n + 1 + i = n + (i + 1) := fun i => by omega
    rw [nextRealRow_skip rows q d fuel (n + 1) (by omega)
      (fun i hi => by rw [e]; exact hs (i + 1) (by omega)) (by rw [e]; exact h)]
    omega

/-- From 0 the search ends at free entry number 0. -/
theorem nextRealRow_first {m : Nat} (hm : 0 < m) :
    Blk.nextRealRow m (logUp m) (2 ^ logUp m) 0 = entryNo m (freeAt m 0).1 (freeAt m 0).2 := by
  rw [nextRealRow_skip m (logUp m) 0 _ 0 (two_pow_logUp_pos m)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by simpa using hm)]
  simp [entryNo, freeAt]

/-- After entry c of a row that is not the last, the search ends at entry c of the next row. -/
theorem nextRealRow_row {m r : Nat} (c : Nat) (h : r + 1 < m) :
    Blk.nextRealRow m (logUp m) (2 ^ logUp m) (entryNo m r c + 1) = entryNo m (r + 1) c := by
  have hQ := le_two_pow_logUp m
  have e : entryNo m r c + 1 = r + 1 + 2 ^ logUp m * c := by
    unfold entryNo
    omega
  rw [nextRealRow_skip m (logUp m) 0 _ _ (two_pow_logUp_pos m)
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (by rw [Nat.add_zero, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; exact h)]
  rw [Nat.add_zero, e]
  rfl

/-- After entry c of the last row, the search ends at entry c + 1 of row 0. -/
theorem nextRealRow_entry {m : Nat} (c : Nat) (hm : 0 < m) :
    Blk.nextRealRow m (logUp m) (2 ^ logUp m) (entryNo m (m - 1) c + 1) = entryNo m 0 (c + 1) := by
  have hQ := le_two_pow_logUp m
  have e : entryNo m (m - 1) c + 1 = m + 2 ^ logUp m * c := by
    unfold entryNo
    omega
  rw [e, nextRealRow_skip m (logUp m) (2 ^ logUp m - m) _ _ (by omega)]
  · unfold entryNo
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · intro i hi
    have e2 : m + 2 ^ logUp m * c + i = m + i + 2 ^ logUp m * c := by omega
    rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · have e3 : m + 2 ^ logUp m * c + (2 ^ logUp m - m) = 0 + 2 ^ logUp m * (c + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [e3, Nat.add_mul_mod_self_left, Nat.zero_mod]
    exact hm

/-- After the k-th free entry the search ends at the free entry number k + 1. -/
theorem nextRealRow_freeAt {m : Nat} (hm : 0 < m) (k : Nat) :
    Blk.nextRealRow m (logUp m) (2 ^ logUp m) (entryNo m (freeAt m k).1 (freeAt m k).2 + 1) =
      entryNo m (freeAt m (k + 1)).1 (freeAt m (k + 1)).2 := by
  have hr : k % m < m := Nat.mod_lt k hm
  have hk : m * (k / m) + k % m = k := Nat.div_add_mod k m
  show Blk.nextRealRow m (logUp m) (2 ^ logUp m) (entryNo m (k % m) (k / m) + 1) = _
  by_cases h : k % m + 1 < m
  · have e : k + 1 = m * (k / m) + (k % m + 1) := by omega
    rw [nextRealRow_row (k / m) h, e, freeAt_mul_add (k / m) h]
  · have e1 : k % m = m - 1 := by omega
    have e : k + 1 = m * (k / m + 1) + 0 := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [e1, nextRealRow_entry (k / m) hm, e, freeAt_mul_add (k / m + 1) hm]

/-- The k-th number that the search gives: begun at 0, and begun again each time at the number after
the last one given. -/
def takenNo (m : Nat) : Nat → Nat
  | 0 => Blk.nextRealRow m (logUp m) (2 ^ logUp m) 0
  | k + 1 => Blk.nextRealRow m (logUp m) (2 ^ logUp m) (takenNo m k + 1)

/-- The k-th number given is the number of the k-th free entry. -/
theorem takenNo_eq {m : Nat} (hm : 0 < m) : ∀ k,
    takenNo m k = entryNo m (freeAt m k).1 (freeAt m k).2
  | 0 => nextRealRow_first hm
  | k + 1 => by rw [takenNo, takenNo_eq hm k, nextRealRow_freeAt hm k]

namespace VectorLay

/-- The rows' index in the high bits: for every number of rows R with logUp R row bits. -/
theorem index_high (R pb j : Nat) :
    index { rowBits := logUp R, placeBits := pb, rowsHigh := true } j =
      entryNo R (vecAt true (2 ^ pb) R j).1 (vecAt true (2 ^ pb) R j).2 := by
  simp [index, entryNo, vecAt, Nat.mul_comm]

/-- The rows' index in the low bits: the number of rows is a power of two. -/
theorem index_low (rb pb l j : Nat) :
    index { rowBits := rb, placeBits := pb, rowsHigh := false } j =
      entryNo (2 ^ rb) (vecAt false l (2 ^ rb) j).1 (vecAt false l (2 ^ rb) j).2 := by
  simp only [index, entryNo, vecAt, logUp_two_pow]
  simp only [Bool.false_eq_true, if_false]
  exact (Nat.mod_add_div j (2 ^ rb)).symm

end VectorLay

/-- On the record that the program makes of a shape, the rows' index in the high bits. -/
theorem vectorLay_index_high (codes : Codes) (s : OracleShape) (j : Nat) :
    (vectorLay codes s true).index j =
      entryNo s.mainRows
        (vecAt true (2 ^ (codes.base.getD s.code default).logEll) s.mainRows j).1
        (vecAt true (2 ^ (codes.base.getD s.code default).logEll) s.mainRows j).2 :=
  VectorLay.index_high s.mainRows _ j

/-- The same with the rows' index in the low bits, where the number of main rows is a power of
two. -/
theorem vectorLay_index_low (codes : Codes) (s : OracleShape) (l j : Nat)
    (h : s.mainRows = 2 ^ ceilLog2 s.mainRows) :
    (vectorLay codes s false).index j =
      entryNo s.mainRows (vecAt false l s.mainRows j).1 (vecAt false l s.mainRows j).2 := by
  have e := VectorLay.index_low (ceilLog2 s.mainRows) (codes.base.getD s.code default).logEll l j
  rw [← h] at e
  exact e

end OnBytes
