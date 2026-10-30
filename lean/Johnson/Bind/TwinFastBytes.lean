-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastBytes.lean: words kept as bytes, for the fast encoder
(Johnson/Bind/TwinFast.lean).

The fast encoder keeps coefficients and symbols as bytes, 8 a word, lowest first (`pushWord`,
`packFrom`), and reads them back with `Fmt.wordAt` (`unpack`, `fastColumn`). This file proves that
what is read is what was laid:
   `pushWord_eq`: a word's 8 bytes behind a string are `Fmt.u64` of the word, appended;
   `foldl_pushWord`, `packFrom_eq`: a list of words laid so is `Fmt.colBytes` of the list, appended;
   `wordAt_colBytes`: word i of such bytes is entry i of the list;
   `wordAt_beyond`: beyond a string's end a word reads as 0;
   `wordAt_packFrom`: word j of `packFrom f n 0 ByteArray.empty` is f j below n, and 0 from n on;
   `wordAt_foldl`: word i of an array's words laid as bytes is the array's entry i.
No Mathlib.
Limits. Bookkeeping on bytes.

-/
import Johnson.Bind.TwinFast
import Fmt.Rules1Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

theorem pushWord_eq (B : ByteArray) (w : UInt64) : pushWord B w = B ++ Fmt.u64 w := by
  apply ByteArray.ext
  unfold pushWord Fmt.u64
  simp only [ByteArray.data_push, ByteArray.data_append]
  apply Array.toList_inj.mp
  simp

theorem colBytes_nil : Fmt.colBytes [] = ByteArray.empty := rfl

theorem colBytes_cons (x : UInt64) (l : List UInt64) :
    Fmt.colBytes (x :: l) = Fmt.u64 x ++ Fmt.colBytes l := by
  unfold Fmt.colBytes
  rw [List.map_cons, Fmt.cat_cons]

theorem size_colBytes : ∀ l : List UInt64, (Fmt.colBytes l).size = 8 * l.length
  | [] => rfl
  | x :: l => by
    rw [colBytes_cons, ByteArray.size_append, Fmt.size_u64, size_colBytes l, List.length_cons]
    omega

theorem foldl_pushWord : ∀ (l : List UInt64) (acc : ByteArray),
    l.foldl pushWord acc = acc ++ Fmt.colBytes l
  | [], acc => by
    rw [List.foldl_nil, colBytes_nil, ByteArray.append_empty]
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_pushWord l, pushWord_eq, colBytes_cons, ByteArray.append_assoc]

theorem packFrom_eq (f : Nat → UInt64) : ∀ (n j : Nat) (acc : ByteArray),
    packFrom f n j acc = acc ++ Fmt.colBytes ((List.range' j n).map f)
  | 0, _, acc => by
    show acc = acc ++ Fmt.colBytes []
    rw [colBytes_nil, ByteArray.append_empty]
  | n + 1, j, acc => by
    show packFrom f n (j + 1) (pushWord acc (f j)) = _
    rw [packFrom_eq f n (j + 1), pushWord_eq, List.range'_succ, List.map_cons, colBytes_cons,
      ByteArray.append_assoc]

/-- Word i of a list's bytes, behind any string. -/
theorem wordAt_colBytes : ∀ (l : List UInt64) (pre : ByteArray) (i : Nat), i < l.length →
    Fmt.wordAt (pre ++ Fmt.colBytes l) (pre.size + 8 * i) = l.getD i 0
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: l, pre, 0, _ => by
    have h := Fmt.wordAt_mid pre (Fmt.u64 x) (Fmt.colBytes l) 0 (by rw [Fmt.size_u64]; omega)
    rw [colBytes_cons, ← ByteArray.append_assoc, Nat.mul_zero, h, Fmt.wordAt_u64]
    rfl
  | x :: l, pre, i + 1, h => by
    have ih := wordAt_colBytes l (pre ++ Fmt.u64 x) i (Nat.lt_of_succ_lt_succ h)
    rw [ByteArray.size_append, Fmt.size_u64] at ih
    have e : pre.size + 8 * (i + 1) = pre.size + 8 + 8 * i := by omega
    rw [colBytes_cons, ← ByteArray.append_assoc, e, ih]
    rfl

theorem byteAt_beyond (b : ByteArray) (q : Nat) (h : b.size ≤ q) : Fmt.byteAt b q = 0 :=
  dif_neg (Nat.not_lt.2 h)

/-- Beyond a string's end a word reads as 0. -/
theorem wordAt_beyond (b : ByteArray) (q : Nat) (h : b.size ≤ q) : Fmt.wordAt b q = 0 := by
  unfold Fmt.wordAt
  rw [byteAt_beyond b q h, byteAt_beyond b (q + 1) (by omega), byteAt_beyond b (q + 2) (by omega),
    byteAt_beyond b (q + 3) (by omega), byteAt_beyond b (q + 4) (by omega),
    byteAt_beyond b (q + 5) (by omega), byteAt_beyond b (q + 6) (by omega),
    byteAt_beyond b (q + 7) (by omega)]
  rfl

theorem wordAt_colBytes_zero (l : List UInt64) (i : Nat) (h : i < l.length) :
    Fmt.wordAt (Fmt.colBytes l) (8 * i) = l.getD i 0 := by
  have h1 := wordAt_colBytes l ByteArray.empty i h
  rw [ByteArray.empty_append] at h1
  have e : ByteArray.empty.size + 8 * i = 8 * i := Nat.zero_add _
  rw [e] at h1
  exact h1

/-- Word j of the packed words f 0, .., f (n - 1). -/
theorem wordAt_packFrom (f : Nat → UInt64) (n j : Nat) :
    Fmt.wordAt (packFrom f n 0 ByteArray.empty) (8 * j) = if j < n then f j else 0 := by
  rw [packFrom_eq, ByteArray.empty_append]
  by_cases h : j < n
  · have hl : j < ((List.range' 0 n).map f).length := by
      rw [List.length_map, List.length_range']
      exact h
    rw [if_pos h, wordAt_colBytes_zero _ _ hl, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some, List.getElem_map, List.getElem_range',
      Nat.zero_add, Nat.one_mul]
  · rw [if_neg h]
    refine wordAt_beyond _ _ ?_
    rw [size_colBytes, List.length_map, List.length_range']
    omega

/-- Word i of an array's words laid as bytes. -/
theorem wordAt_foldl (A : Array UInt64) (i : Nat) (h : i < A.size) :
    Fmt.wordAt (A.foldl pushWord ByteArray.empty) (8 * i) = A.getD i 0 := by
  have hl : i < A.toList.length := by
    rw [Array.length_toList]
    exact h
  rw [← Array.foldl_toList, foldl_pushWord, ByteArray.empty_append, wordAt_colBytes_zero _ _ hl,
    Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

end Bind.Twin

#print axioms Bind.Twin.pushWord_eq
#print axioms Bind.Twin.colBytes_nil
#print axioms Bind.Twin.colBytes_cons
#print axioms Bind.Twin.size_colBytes
#print axioms Bind.Twin.foldl_pushWord
#print axioms Bind.Twin.packFrom_eq
#print axioms Bind.Twin.wordAt_colBytes
#print axioms Bind.Twin.byteAt_beyond
#print axioms Bind.Twin.wordAt_beyond
#print axioms Bind.Twin.wordAt_colBytes_zero
#print axioms Bind.Twin.wordAt_packFrom
#print axioms Bind.Twin.wordAt_foldl
