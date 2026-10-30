-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/Windows.lean: words of a string that is made of pieces: general laws on
`Verify.wordsAt` and `Fmt.cat`.

The item "request" (OnBytes/Proof/RequestItem.lean) is seventeen pieces, one behind the other. The
comparison of that item with the public part (`Verify.statementHeld`,
OnBytes/Model/VerifyStatement.lean) reads words at fixed places. These laws say which piece stands
at a place.

Main names.
* `wordsAt_cat`: behind pieces of `a` words together, the n words from place `a + i` of the whole
  are the n words from place i of the next piece, where they lie inside it.
* `wordsAt_whole`: all words of a string of n words are the string.
* `wordsAt_words`: in a string that is written of a list of numbers, word k is number k.
* `namesHeld_cat`: the comparison of a list of names accepts, where the piece at its place is
  written of the scan's values of these names.

Limits. General laws on strings. Nothing on any file. No soundness is claimed.
-/
import OnBytes.K.ServedFreeItem
import Fmt.M3ParOfLawsProofs
import Fmt.ParsedReadFileLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify

/-- The piece from 0 to a string's length is the string. -/
theorem extract_all (x : ByteArray) : x.extract 0 x.size = x := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_size

/-- Words behind a string of `a` words. -/
theorem wordsAt_skip (A B : ByteArray) (a i n : Nat) (h : A.size = 4 * a) :
    wordsAt (A ++ B) (a + i) n = wordsAt B i n := by
  unfold wordsAt
  rw [OnBytes.K.extract_append_right A _ _ _ (by omega)]
  congr 1 <;> omega

/-- Words that end inside the first of two strings. -/
theorem wordsAt_in (x Q : ByteArray) (i n : Nat) (h : 4 * (i + n) ≤ x.size) :
    wordsAt (x ++ Q) i n = wordsAt x i n := by
  unfold wordsAt
  exact OnBytes.K.extract_append_left _ _ _ _ h

/-- All words of a string of n words. -/
theorem wordsAt_whole (x : ByteArray) (n : Nat) (h : x.size = 4 * n) : wordsAt x 0 n = x := by
  unfold wordsAt
  rw [Nat.mul_zero, Nat.zero_add, ← h]
  exact extract_all x

/-- **Which piece stands at a place.** -/
theorem wordsAt_cat (pre : List ByteArray) (x : ByteArray) (post : List ByteArray) (a i n : Nat)
    (hp : (Fmt.cat pre).size = 4 * a) (hx : 4 * (i + n) ≤ x.size) :
    wordsAt (Fmt.cat (pre ++ x :: post)) (a + i) n = wordsAt x i n := by
  rw [Fmt.M3.cat_append, Fmt.cat_cons, wordsAt_skip _ _ a i n hp, wordsAt_in _ _ _ _ hx]

/-- A whole piece at its place. -/
theorem wordsAt_piece (pre : List ByteArray) (x : ByteArray) (post : List ByteArray) (a n : Nat)
    (hp : (Fmt.cat pre).size = 4 * a) (hx : x.size = 4 * n) :
    wordsAt (Fmt.cat (pre ++ x :: post)) a n = x := by
  have h := wordsAt_cat pre x post a 0 n hp (by omega)
  rw [Nat.add_zero] at h
  rw [h, wordsAt_whole x n hx]

/-- A string that is written of a list of numbers has four bytes a number. -/
theorem size_words (l : List Nat) : (Fmt.cat (l.map word32)).size = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, Fmt.cat_cons, ByteArray.size_append, OnBytes.K.size_word32, ih,
      List.length_cons]
    omega

/-- In a string that is written of a list of numbers, word k is number k. -/
theorem wordsAt_words (l : List Nat) (k : Nat) (hk : k < l.length) :
    wordsAt (Fmt.cat (l.map word32)) k 1 = word32 l[k] := by
  have e : l.map word32 = (l.take k).map word32 ++ word32 l[k] :: (l.drop (k + 1)).map word32 := by
    rw [← List.map_cons, ← List.map_append, List.getElem_cons_drop, List.take_append_drop]
  rw [e]
  refine wordsAt_piece _ _ _ k 1 ?_ (OnBytes.K.size_word32 _)
  rw [size_words, List.length_take]
  omega

/-- **The comparison of a list of names accepts**, where the piece at its place is written of the
scan's values of these names. -/
theorem namesHeld_cat (P : PolScan) (pre post : List ByteArray) (first : Nat) (names : String)
    (hp : (Fmt.cat pre).size = 4 * first) :
    namesHeld P
      (Fmt.cat (pre ++ Fmt.cat (((names.splitOn " ").map P.value).map word32) :: post)) first
      names = true := by
  unfold namesHeld
  rw [List.all_eq_true]
  intro x hx
  have hk : x.2 < (names.splitOn " ").length := by
    simpa using List.snd_lt_of_mem_zipIdx hx
  have hk' : x.2 < ((names.splitOn " ").map P.value).length := by
    rw [List.length_map]
    exact hk
  have hx1 : x.1 = (names.splitOn " ")[x.2] := by
    have := List.mem_zipIdx hx
    simpa using this.2.2
  rw [wordsAt_cat pre _ post first x.2 1 hp (by rw [size_words]; omega), wordsAt_words _ _ hk',
    List.getElem_map, ← hx1]
  exact Fmt.bytes_beq_self _

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.extract_all
#print axioms Johnson.AtFull.Item.wordsAt_skip
#print axioms Johnson.AtFull.Item.wordsAt_in
#print axioms Johnson.AtFull.Item.wordsAt_whole
#print axioms Johnson.AtFull.Item.wordsAt_cat
#print axioms Johnson.AtFull.Item.wordsAt_piece
#print axioms Johnson.AtFull.Item.size_words
#print axioms Johnson.AtFull.Item.wordsAt_words
#print axioms Johnson.AtFull.Item.namesHeld_cat
