-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SecondHashFunctionList.lean: the second hash function (OnBytes/Hash/SecondHashFunction.lean) read OFF THE HEAD
OF A LIST OF BYTES, and the law that ties that form to `OnBytes.secondHashFunctionState`.
Why. Lean's kernel does not reduce `OnBytes.secondHashFunctionState`: `Run.Blake2b.load64` first asks
`a.size.toUSize.toNat = a.size`, and the kernel has no value for the platform's word size. Over
`load64Plain` it reduces, but in our trials (512 to 8,192 bytes) the cost grew
with the square of the length; why was not measured apart. The form here reads eight bytes a word,
sixteen words a block, off the head of a list, and asks no index and no size: in those trials
(2,048 to 32,768 bytes) its cost was linear.
  `word8 l`: the little-endian word of the first eight bytes of l; beyond its end: zeros.
  `take8 l`: that word and the rest; `take8_eq`: it is (`word8 l`, `l.drop 8`).
  `blkL l`: a block of sixteen words and the rest; `blkL_snd`, `blkL_fst`: the rest is `l.drop 128`;
    the block of `L.drop off` is `MessageBlock.ofBytes ⟨⟨L⟩⟩ off`.
  `goL t1 k i S l`: k blocks compressed into S, the first with the number i, and the rest.
  `goL_split`, `goL_cut`: k = a + b blocks are a blocks and then b, from the list behind the first
    128 a bytes: THE CHAIN CAN BE CUT AT ANY BLOCK.
  `olderStateL num sz l`: `secondHashFunctionState`'s text over these; sz stands for the size.
  **`olderState_eq_list`**: `OnBytes.secondHashFunctionState num w = olderStateL num w.size w.data.toList`, for
    every number and every array, the short last block and the empty array among them.
  `olderKL`, `olderK_eq_list`: the digest.
Whose text. `olderStateL` and `goL` follow `OnBytes.secondHashFunctionState` (OnBytes/Hash/SecondHashFunction.lean), `word8`,
`take8` and `blkL` follow `load64Plain` and `MessageBlock.ofBytes` (Run/Blake2b/Hash.lean): this tree's own
files; `compress`, `firstState`, `setLastblock`, `ChainingValue.bytes` are called as they stand there.
Source. `word8`, `take8` and `blkL` follow `load64Plain` and `MessageBlock.ofBytes` of Run/Blake2b/Hash.lean
(its section 2), at one remove from what that file names as its source.
That file's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
Limits. Equations between functions: nothing on what the hash is good for. sz is an argument of its
own: whoever calls `olderStateL` at another number than the list's length has another function.
That the kernel bears a given length is a matter of trial, not of these laws.

-/
import OnBytes.Hash.SecondHashFunction
import Run.Blake2b.WordsThm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Run.Blake2b

/-- Byte j of a list as a 64-bit word; beyond the end: 0. -/
def b64 (l : List UInt8) (j : Nat) : UInt64 := (l.getD j 0).toUInt64

/-- The little-endian word of the first eight bytes; beyond the end: zeros. -/
def word8 (l : List UInt8) : UInt64 :=
  (b64 l 0 <<< 0) ||| (b64 l 1 <<< 8) ||| (b64 l 2 <<< 16) ||| (b64 l 3 <<< 24) |||
    (b64 l 4 <<< 32) ||| (b64 l 5 <<< 40) ||| (b64 l 6 <<< 48) ||| (b64 l 7 <<< 56)

/-- That word and the rest of the list: where eight bytes lie, they are taken off the head. -/
def take8 : List UInt8 → UInt64 × List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =>
    ((b0.toUInt64 <<< 0) ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
      (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
      (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56), r)
  | l => (word8 l, [])

theorem take8_eq (l : List UInt8) : take8 l = (word8 l, l.drop 8) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ |
    ⟨b7, r⟩⟩⟩⟩⟩⟩⟩⟩ <;> rfl

/-- A block of sixteen words off the head, and the rest. -/
def blkL (l : List UInt8) : MessageBlock × List UInt8 :=
  let (m0, l) := take8 l; let (m1, l) := take8 l; let (m2, l) := take8 l; let (m3, l) := take8 l
  let (m4, l) := take8 l; let (m5, l) := take8 l; let (m6, l) := take8 l; let (m7, l) := take8 l
  let (m8, l) := take8 l; let (m9, l) := take8 l; let (m10, l) := take8 l
  let (m11, l) := take8 l; let (m12, l) := take8 l; let (m13, l) := take8 l
  let (m14, l) := take8 l; let (m15, l) := take8 l
  (⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15⟩, l)

theorem blkL_eq (l : List UInt8) : blkL l =
    (⟨word8 l, word8 (l.drop 8), word8 (l.drop 16), word8 (l.drop 24), word8 (l.drop 32),
      word8 (l.drop 40), word8 (l.drop 48), word8 (l.drop 56), word8 (l.drop 64),
      word8 (l.drop 72), word8 (l.drop 80), word8 (l.drop 88), word8 (l.drop 96),
      word8 (l.drop 104), word8 (l.drop 112), word8 (l.drop 120)⟩, l.drop 128) := by
  simp only [blkL, take8_eq, List.drop_drop]

theorem blkL_snd (l : List UInt8) : (blkL l).2 = l.drop 128 := by rw [blkL_eq]

theorem getD_drop (L : List UInt8) (k j : Nat) : (L.drop k).getD j 0 = L.getD (k + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem arr_getD (L : List UInt8) (i : Nat) : (Array.mk L).getD i 0 = L.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The plain read at the index k is the word off the head of the list behind k bytes. -/
theorem load64Plain_list (L : List UInt8) (k : Nat) :
    load64Plain ⟨⟨L⟩⟩ k = word8 (L.drop k) := by
  unfold load64Plain word8 b64
  simp only [byteOrZero_mk, arr_getD, getD_drop]

/-- **The block at an offset is the block off the head of the list behind that many bytes.** -/
theorem blkL_fst (L : List UInt8) (off : Nat) :
    (blkL (L.drop off)).1 = MessageBlock.ofBytes ⟨⟨L⟩⟩ off := by
  rw [blkL_eq]
  unfold MessageBlock.ofBytes
  simp only [load64_eq_plain, load64Plain_list, List.drop_drop, Nat.reduceMul, Nat.add_zero]

/-- k blocks compressed into S, the first with the number i; and the rest of the list. -/
def goL (t1 : UInt64) : Nat → Nat → State → List UInt8 → State × List UInt8
  | 0, _, S, l => (S, l)
  | k + 1, i, S, l =>
    let (b, r) := blkL l
    goL t1 k (i + 1) (compress { S with t0 := UInt64.ofNat (128 * (i + 1)), t1 := t1 } b) r

/-- **The chain can be cut at any block.** -/
theorem goL_split (t1 : UInt64) (a b : Nat) : ∀ (i : Nat) (S : State) (l : List UInt8),
    goL t1 (a + b) i S l = goL t1 b (i + a) (goL t1 a i S l).1 (goL t1 a i S l).2 := by
  induction a with
  | zero => intro i S l; simp [goL]
  | succ a ih =>
    intro i S l
    rw [Nat.succ_add]
    simp only [goL]
    rw [ih]
    congr 1
    omega

/-- What is left behind k blocks. -/
theorem goL_rest (t1 : UInt64) : ∀ (k i : Nat) (S : State) (l : List UInt8),
    (goL t1 k i S l).2 = l.drop (128 * k) := by
  intro k
  induction k with
  | zero => intro i S l; simp [goL]
  | succ k ih =>
    intro i S l
    simp only [goL]
    rw [ih, blkL_snd, List.drop_drop]
    congr 1
    omega

/-- **The form that a cut uses**: a blocks, then b blocks from the list behind them. -/
theorem goL_cut (t1 : UInt64) (a b i : Nat) (S : State) (l : List UInt8) :
    goL t1 (a + b) i S l = goL t1 b (i + a) (goL t1 a i S l).1 (l.drop (128 * a)) := by
  rw [goL_split, goL_rest]

/-- `goL` from the first block is `secondHashFunctionState`'s fold, and what is left is the list behind. -/
theorem goL_fold (t1 : UInt64) (S0 : State) (L : List UInt8) : ∀ k : Nat,
    goL t1 k 0 S0 L =
      (Nat.fold k (fun i _ S =>
        compress { S with t0 := UInt64.ofNat (128 * (i + 1)), t1 := t1 }
          (MessageBlock.ofBytes ⟨⟨L⟩⟩ (128 * i))) S0, L.drop (128 * k)) := by
  intro k
  induction k with
  | zero => simp [goL]
  | succ k ih =>
    rw [goL_split t1 k 1 0 S0 L, ih]
    simp only [goL, Nat.fold_succ, Nat.zero_add, blkL_snd, blkL_fst, List.drop_drop]
    congr 2

/-- `OnBytes.secondHashFunctionState`'s text over the list form; sz stands for the size. -/
def olderStateL (num sz : Nat) (l : List UInt8) : ChainingValue :=
  let n := sz / 4
  let full := (sz + 127) / 128 - 1
  let t1 := UInt64.ofNat (num + 4294967296 * n)
  let r := goL t1 full 0 (firstState 0 64) l
  (compress (setLastblock { r.1 with t0 := UInt64.ofNat (4 * n), t1 := t1 }) (blkL r.2).1).h

/-- **THE LAW: the second hash function's last state is the list form's**, at every num and w. -/
theorem olderState_eq_list (num : Nat) (w : ByteArray) :
    OnBytes.secondHashFunctionState num w = olderStateL num w.size w.data.toList := by
  obtain ⟨⟨L⟩⟩ := w
  unfold OnBytes.secondHashFunctionState olderStateL
  simp only [goL_fold, blkL_fst]

/-- The digest over the list form. -/
def olderKL (num sz : Nat) (l : List UInt8) : ByteArray := (olderStateL num sz l).bytes 32

theorem olderK_eq_list (num : Nat) (w : ByteArray) :
    OnBytes.secondHashFunction num w = olderKL num w.size w.data.toList := by
  unfold OnBytes.secondHashFunction olderKL
  rw [olderState_eq_list]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.take8_eq
#print axioms Johnson.Unfolds.blkL_eq
#print axioms Johnson.Unfolds.blkL_snd
#print axioms Johnson.Unfolds.getD_drop
#print axioms Johnson.Unfolds.arr_getD
#print axioms Johnson.Unfolds.load64Plain_list
#print axioms Johnson.Unfolds.blkL_fst
#print axioms Johnson.Unfolds.goL_split
#print axioms Johnson.Unfolds.goL_rest
#print axioms Johnson.Unfolds.goL_cut
#print axioms Johnson.Unfolds.goL_fold
#print axioms Johnson.Unfolds.olderState_eq_list
#print axioms Johnson.Unfolds.olderK_eq_list
