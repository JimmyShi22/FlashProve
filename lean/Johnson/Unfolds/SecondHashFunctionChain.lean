-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SecondHashFunctionChain.lean: a table of words given by a function, its bytes in pieces, and the
second hash function's chain over pieces that are laid one behind the other.
For the digests of the public tables (Johnson/Unfolds/SecondHashFunctionWords.lean: `tableDigest_list`): the
kernel bears some 256 blocks in one term, by our trials, and not 2,048.
  `fromTo f s n`: the words f s, f (s + 1), …, n of them; `fromTo_append`, `fromTo_eq_map`.
  `bytesOf f s n`: their bytes, four a word; `bytesOf_append`, `length_bytesOf`.
  **`goL_append`**: over `l₁ ++ l₂`, where l₁ has 128 a bytes: a blocks of l₁, then b blocks of l₂.
  `goL_step`: that with a piece's closed fact laid in.
  `goL_exact`: a list of just 128 a bytes is spent. `olderStateL_eq`: its text at three letters.
  `toList_of_range_map`: an array `(Array.range n).map g` whose entries are f's is `fromTo f 0 n`.
Source. It reasons about `goL` and `olderStateL` of Johnson/Unfolds/SecondHashFunctionList.lean, whose `blkL`
follows `MessageBlock.ofBytes` of Run/Blake2b/Hash.lean.
That file's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
Limits. Equations between functions. Nothing on what the kernel bears.

-/
import Johnson.Unfolds.SecondHashFunctionWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Run.Blake2b

/-- The words f s, f (s + 1), …: n of them. -/
def fromTo (f : Nat → Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | s, n + 1 => f s :: fromTo f (s + 1) n

theorem length_fromTo (f : Nat → Nat) : ∀ (n s : Nat), (fromTo f s n).length = n
  | 0, _ => rfl
  | n + 1, s => by rw [fromTo, List.length_cons, length_fromTo f n]

theorem fromTo_append (f : Nat → Nat) : ∀ (a s b : Nat),
    fromTo f s (a + b) = fromTo f s a ++ fromTo f (s + a) b
  | 0, s, b => by simp [fromTo]
  | a + 1, s, b => by
    rw [Nat.succ_add, fromTo, fromTo, fromTo_append f a (s + 1) b, List.cons_append]
    congr 3
    omega

theorem fromTo_eq_map (f : Nat → Nat) : ∀ (n s : Nat), fromTo f s n = (List.range' s n).map f
  | 0, _ => rfl
  | n + 1, s => by rw [fromTo, List.range'_succ, List.map_cons, fromTo_eq_map f n]

/-- Their bytes, four a word, lowest first. -/
def bytesOf (f : Nat → Nat) (s n : Nat) : List UInt8 := (fromTo f s n).flatMap w4

theorem bytesOf_append (f : Nat → Nat) (a s b : Nat) :
    bytesOf f s (a + b) = bytesOf f s a ++ bytesOf f (s + a) b := by
  unfold bytesOf
  rw [fromTo_append, List.flatMap_append]

theorem length_bytesOf (f : Nat → Nat) (s n : Nat) : (bytesOf f s n).length = 4 * n := by
  unfold bytesOf
  rw [length_flatMap_w4, length_fromTo]

/-- **The chain over two lists laid one behind the other.** -/
theorem goL_append (t1 : UInt64) (a b i : Nat) (S : State) (l₁ l₂ : List UInt8)
    (h : l₁.length = 128 * a) :
    goL t1 (a + b) i S (l₁ ++ l₂) = goL t1 b (i + a) (goL t1 a i S l₁).1 l₂ := by
  rw [goL_cut, ← goL_take t1 a i S (l₁ ++ l₂), ← h, List.take_left', List.drop_left'] <;> rfl

/-- **A step of the chain**: a piece's closed fact `hp` carries the state over the piece. -/
theorem goL_step (f : Nat → Nat) (t1 : UInt64) (a b i s n : Nat) (S T : State) (R : List UInt8)
    (hn : 4 * n = 128 * a) (hp : (goL t1 a i S (bytesOf f s n)).1 = T) :
    goL t1 (a + b) i S (bytesOf f s n ++ R) = goL t1 b (i + a) T R := by
  rw [goL_append t1 a b i S _ R (by rw [length_bytesOf, hn]), hp]

theorem goL_zero (t1 : UInt64) (i : Nat) (S : State) (l : List UInt8) :
    goL t1 0 i S l = (S, l) := rfl

/-- `olderStateL`'s text with its three numbers as letters: no term is unfolded to see them. -/
theorem olderStateL_eq (num sz : Nat) (l : List UInt8) (n full : Nat) (t1 : UInt64)
    (hn : sz / 4 = n) (hf : (sz + 127) / 128 - 1 = full)
    (ht : UInt64.ofNat (num + 4294967296 * n) = t1) :
    olderStateL num sz l =
      (compress (setLastblock { (goL t1 full 0 (firstState 0 64) l).1 with
        t0 := UInt64.ofNat (4 * n), t1 := t1 })
        (blkL (goL t1 full 0 (firstState 0 64) l).2).1).h := by
  subst hn hf ht
  rfl

/-- Where the list has just 128 a bytes, nothing is left. -/
theorem goL_exact (t1 : UInt64) (a i : Nat) (S : State) (l : List UInt8)
    (h : l.length = 128 * a) : (goL t1 a i S l).2 = [] := by
  rw [goL_rest, ← h, List.drop_length]

/-- An array `(Array.range n).map g` whose entries are f's, as a list. -/
theorem toList_of_range_map (g f : Nat → Nat) (n : Nat) (h : ∀ t, t < n → g t = f t) :
    ((Array.range n).map g).toList = fromTo f 0 n := by
  rw [fromTo_eq_map, Array.toList_map, Array.toList_range, List.range_eq_range']
  apply List.map_congr_left
  intro t ht
  exact h t (by simpa using ht)

end Johnson.Unfolds

#print axioms Johnson.Unfolds.length_fromTo
#print axioms Johnson.Unfolds.fromTo_append
#print axioms Johnson.Unfolds.fromTo_eq_map
#print axioms Johnson.Unfolds.bytesOf_append
#print axioms Johnson.Unfolds.length_bytesOf
#print axioms Johnson.Unfolds.goL_append
#print axioms Johnson.Unfolds.goL_step
#print axioms Johnson.Unfolds.goL_zero
#print axioms Johnson.Unfolds.olderStateL_eq
#print axioms Johnson.Unfolds.goL_exact
#print axioms Johnson.Unfolds.toList_of_range_map
