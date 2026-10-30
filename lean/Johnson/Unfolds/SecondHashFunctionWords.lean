-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SecondHashFunctionWords.lean: two laws more for the second hash function off the head of a list
(Johnson/Unfolds/SecondHashFunctionList.lean): the bytes of a table of words as a flat list, and pieces of the
chain.
Why. A public table's digest is asked of `table.foldl (fun b x => b ++ word32 x) ByteArray.empty`
(`tableHeld`, OnBytes/Model/Config.lean; `tableHeldO`, Johnson/Desc/Ok/PlanWritten/PublicAt.lean):
one append of four bytes a word. In our trials the kernel's cost of that fold
grew with the square of the number of words (256 and 1,024 words; at 4,096 its stack ended).
  `w4 x`: the four bytes of `word32 x`, as a list; `word32_list`.
  **`tableBytes_list`**: the fold's bytes are `table.toList.flatMap w4`.
  `tableBytes_size`: four a word.
  `tableDigest_list`: so `secondHashFunction num` of the fold is `olderKL num (4 * table.size)` of that list.
  `word8_take`, `blkL_take`; **`goL_take`**: the state behind k blocks hangs on the first 128 k
    bytes alone: so a piece's own bytes can stand in a statement in the place of the whole tail.
  `goL_piece`: `goL_cut` with that: a blocks, then b blocks of the 128 b bytes behind them.
Source. It reasons about `word8`, `blkL` and `goL` of Johnson/Unfolds/SecondHashFunctionList.lean, which follow
`load64Plain` and `MessageBlock.ofBytes` of Run/Blake2b/Hash.lean. `w4` follows `Fmt.u64` (Fmt/Rules1.lean).
That file's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
Limits. Equations between functions. Nothing on what the kernel bears.

-/
import Johnson.Unfolds.SecondHashFunctionList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Run.Blake2b

/-! ## A table's bytes -/

/-- The four bytes of `word32 x`, lowest first. -/
def w4 (x : Nat) : List UInt8 :=
  [(UInt64.ofNat x).toUInt8, (UInt64.ofNat x >>> 8).toUInt8, (UInt64.ofNat x >>> 16).toUInt8,
    (UInt64.ofNat x >>> 24).toUInt8]

theorem word32_list (x : Nat) : (OnBytes.word32 x).data.toList = w4 x := by
  unfold OnBytes.word32 Fmt.u64n Fmt.u64 w4
  rw [ByteArray.data_extract]
  rfl

theorem foldBytes_list (l : List Nat) : ∀ acc : ByteArray,
    (l.foldl (fun b x => b ++ OnBytes.word32 x) acc).data.toList =
      acc.data.toList ++ l.flatMap w4 := by
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    rw [List.foldl_cons, ih, ByteArray.data_append, Array.toList_append, word32_list,
      List.flatMap_cons, List.append_assoc]

/-- **The bytes of a table of words, as `tableHeld` makes them, are the flat list.** -/
theorem tableBytes_list (table : Array Nat) :
    (table.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty).data.toList =
      table.toList.flatMap w4 := by
  rw [← Array.foldl_toList, foldBytes_list]
  rfl

theorem length_flatMap_w4 (l : List Nat) : (l.flatMap w4).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    show 4 + 4 * l.length = 4 * (l.length + 1)
    omega

theorem tableBytes_size (table : Array Nat) :
    (table.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty).size = 4 * table.size := by
  rw [← ByteArray.size_data, ← Array.length_toList, tableBytes_list, length_flatMap_w4,
    Array.length_toList]

/-- **A table's digest over the flat list.** -/
theorem tableDigest_list (num : Nat) (table : Array Nat) :
    OnBytes.secondHashFunction num (table.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) =
      olderKL num (4 * table.size) (table.toList.flatMap w4) := by
  rw [olderK_eq_list, tableBytes_size, tableBytes_list]

/-! ## Pieces -/

theorem b64_take (l : List UInt8) (m j : Nat) (h : j < m) : b64 (l.take m) j = b64 l j := by
  unfold b64
  simp [List.getD_eq_getElem?_getD, h]

theorem word8_take (l : List UInt8) (m : Nat) (h : 8 ≤ m) : word8 (l.take m) = word8 l := by
  unfold word8
  rw [b64_take l m 0 (by omega), b64_take l m 1 (by omega), b64_take l m 2 (by omega),
    b64_take l m 3 (by omega), b64_take l m 4 (by omega), b64_take l m 5 (by omega),
    b64_take l m 6 (by omega), b64_take l m 7 (by omega)]

theorem word8_take_drop (l : List UInt8) (m d : Nat) (h : d + 8 ≤ m) :
    word8 ((l.take m).drop d) = word8 (l.drop d) := by
  rw [List.drop_take, word8_take _ _ (by omega)]

/-- A block hangs on 128 bytes alone. -/
theorem blkL_take (l : List UInt8) (m : Nat) (h : 128 ≤ m) : (blkL (l.take m)).1 = (blkL l).1 := by
  rw [blkL_eq, blkL_eq]
  simp only
  rw [word8_take l m (by omega), word8_take_drop l m 8 (by omega),
    word8_take_drop l m 16 (by omega), word8_take_drop l m 24 (by omega),
    word8_take_drop l m 32 (by omega), word8_take_drop l m 40 (by omega),
    word8_take_drop l m 48 (by omega), word8_take_drop l m 56 (by omega),
    word8_take_drop l m 64 (by omega), word8_take_drop l m 72 (by omega),
    word8_take_drop l m 80 (by omega), word8_take_drop l m 88 (by omega),
    word8_take_drop l m 96 (by omega), word8_take_drop l m 104 (by omega),
    word8_take_drop l m 112 (by omega), word8_take_drop l m 120 (by omega)]

/-- **The state behind k blocks hangs on the first 128 k bytes alone.** -/
theorem goL_take (t1 : UInt64) : ∀ (k i : Nat) (S : State) (l : List UInt8),
    (goL t1 k i S (l.take (128 * k))).1 = (goL t1 k i S l).1 := by
  intro k
  induction k with
  | zero => intro i S l; simp [goL]
  | succ k ih =>
    intro i S l
    simp only [goL]
    rw [blkL_take l _ (by omega), blkL_snd, blkL_snd, List.drop_take,
      show 128 * (k + 1) - 128 = 128 * k by omega, ih]

/-- **A piece**: a blocks, then b blocks of the 128 b bytes behind them. -/
theorem goL_piece (t1 : UInt64) (a b i : Nat) (S : State) (l : List UInt8) :
    (goL t1 (a + b) i S l).1 =
      (goL t1 b (i + a) (goL t1 a i S l).1 ((l.drop (128 * a)).take (128 * b))).1 := by
  rw [goL_cut, goL_take]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.word32_list
#print axioms Johnson.Unfolds.foldBytes_list
#print axioms Johnson.Unfolds.tableBytes_list
#print axioms Johnson.Unfolds.length_flatMap_w4
#print axioms Johnson.Unfolds.tableBytes_size
#print axioms Johnson.Unfolds.tableDigest_list
#print axioms Johnson.Unfolds.b64_take
#print axioms Johnson.Unfolds.word8_take
#print axioms Johnson.Unfolds.word8_take_drop
#print axioms Johnson.Unfolds.blkL_take
#print axioms Johnson.Unfolds.goL_take
#print axioms Johnson.Unfolds.goL_piece
