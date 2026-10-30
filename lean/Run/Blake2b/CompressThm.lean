-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.SpecFast
import Run.Blake2b.HashThm
/-!
# The fast compression function computes that of the plain definition

The main statements:

* compress_h: if a state S of Spec.lean and a state T of Compress.lean have the same chaining value,
  counter and flags, then the h of Spec.blake2b_compress S block is the h of compress on T and the
  block's sixteen long words. It is stated for a block that is read from bytes.
* compress_t0 to compress_last_node: Spec.blake2b_compress changes no other field of the state.
* compress_eq: the two together, as one equation between states.

The method: lemmas that read and write an entry of an explicit array of sixteen words, with them the
eight applications of G in a round, then a round, then each of the twelve rounds, where Lean
evaluates the round's row of blake2b_sigma. The loops before and after the rounds are unrolled.

What "#print axioms" reports for compress_h and compress_eq: propext and Quot.sound. There is no
sorry and no axiom of ours.
Source. All are theorems about the definitions of Spec.lean, Compress.lean and Hash.lean, with WorkVector.arr
to state them. Some statements write out again what these definitions have from their source, among
them: G_0 to G_7 and round_arr the eight quadruples of ROUND, round_0 to round_11 the twelve rows of
blake2b_sigma, msg_arr, start_arr and last_arr the loops before and after the rounds. These follow,
at one remove, what the three files name as their source (Hash.lean: lines 10 to 15).
Compress.lean's head says (its lines 8 to 11, copied here):
`IV`, `rotr64`, `G`, `ROUND`, `State` and `compress` are adapted from blake2b-ref.c, blake2.h and
blake2-impl.h of the BLAKE2 reference source code package (reference C implementations), Copyright
2012, Samuel Neves. Their head offers "the CC0, the OpenSSL Licence, or the Apache Public License
2.0, at your option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
Spec.lean's head says (its lines 7 and 8, copied here):
Adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the BLAKE2 reference source code package,
Copyright 2012 Samuel Neves, taken under CC0 1.0 Universal.
-/
namespace Run.Blake2b

/-! ## A long word of the block -/

/-- A read with a default, as Spec.lean writes it, made a 64-bit word, is byteOrZero of
Hash.lean. -/
theorem read_eq_byteOrZero (x : Array UInt8) (i : Nat) : (x[i]!).toUInt64 = byteOrZero ⟨x⟩ i :=
  (byteOrZero_mk x i).symm

/-- Spec.load64 is the fast read of a long word. -/
theorem load64_fast (src : Array UInt8) (off : Nat) :
    Spec.load64 src off = load64 ⟨src⟩ off := by
  rw [load64_eq_plain]
  unfold Spec.load64 load64Plain
  simp only [read_eq_byteOrZero]

/-- Spec.lean and Compress.lean have the same rotation. -/
theorem rotr_eq (w c : UInt64) : Spec.rotr64 w c = rotr64 w c := rfl

/-! ## Reading and writing an entry of an explicit array of sixteen or of eight words -/

theorem get_0 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[0]! =
      v0 := rfl
theorem get_1 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[1]! =
      v1 := rfl
theorem get_2 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[2]! =
      v2 := rfl
theorem get_3 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[3]! =
      v3 := rfl
theorem get_4 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[4]! =
      v4 := rfl
theorem get_5 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[5]! =
      v5 := rfl
theorem get_6 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[6]! =
      v6 := rfl
theorem get_7 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[7]! =
      v7 := rfl
theorem get_8 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[8]! =
      v8 := rfl
theorem get_9 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[9]! =
      v9 := rfl
theorem get_10 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[10]! =
      v10 := rfl
theorem get_11 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[11]! =
      v11 := rfl
theorem get_12 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[12]! =
      v12 := rfl
theorem get_13 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[13]! =
      v13 := rfl
theorem get_14 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[14]! =
      v14 := rfl
theorem get_15 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64} :
    (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : Array UInt64)[15]! =
      v15 := rfl

theorem set_0 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 x =
      #[x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_1 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 x =
      #[v0, x, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_2 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 x =
      #[v0, v1, x, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_3 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 x =
      #[v0, v1, v2, x, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_4 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 4 x =
      #[v0, v1, v2, v3, x, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_5 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 5 x =
      #[v0, v1, v2, v3, v4, x, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_6 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 6 x =
      #[v0, v1, v2, v3, v4, v5, x, v7, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_7 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 7 x =
      #[v0, v1, v2, v3, v4, v5, v6, x, v8, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_8 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 8 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, x, v9, v10, v11, v12, v13, v14, v15] := rfl
theorem set_9 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 9 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, x, v10, v11, v12, v13, v14, v15] := rfl
theorem set_10 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 10 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, x, v11, v12, v13, v14, v15] := rfl
theorem set_11 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 11 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, x, v12, v13, v14, v15] := rfl
theorem set_12 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 12 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, x, v13, v14, v15] := rfl
theorem set_13 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 13 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, x, v14, v15] := rfl
theorem set_14 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 14 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, x, v15] := rfl
theorem set_15 {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x : UInt64} :
    Array.set! #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 15 x =
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, x] := rfl

theorem get8_0 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[0]! = a0 := rfl
theorem get8_1 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[1]! = a1 := rfl
theorem get8_2 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[2]! = a2 := rfl
theorem get8_3 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[3]! = a3 := rfl
theorem get8_4 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[4]! = a4 := rfl
theorem get8_5 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[5]! = a5 := rfl
theorem get8_6 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[6]! = a6 := rfl
theorem get8_7 {a0 a1 a2 a3 a4 a5 a6 a7 : UInt64} :
    (#[a0, a1, a2, a3, a4, a5, a6, a7] : Array UInt64)[7]! = a7 := rfl

theorem set8_0 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 0 x =
      #[x, a1, a2, a3, a4, a5, a6, a7] := rfl
theorem set8_1 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 1 x =
      #[a0, x, a2, a3, a4, a5, a6, a7] := rfl
theorem set8_2 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 2 x =
      #[a0, a1, x, a3, a4, a5, a6, a7] := rfl
theorem set8_3 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 3 x =
      #[a0, a1, a2, x, a4, a5, a6, a7] := rfl
theorem set8_4 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 4 x =
      #[a0, a1, a2, a3, x, a5, a6, a7] := rfl
theorem set8_5 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 5 x =
      #[a0, a1, a2, a3, a4, x, a6, a7] := rfl
theorem set8_6 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 6 x =
      #[a0, a1, a2, a3, a4, a5, x, a7] := rfl
theorem set8_7 {a0 a1 a2 a3 a4 a5 a6 a7 x : UInt64} :
    Array.set! #[a0, a1, a2, a3, a4, a5, a6, a7] 7 x =
      #[a0, a1, a2, a3, a4, a5, a6, x] := rfl

/-! ## The eight applications of G in a round, each on an explicit array of sixteen words

s0 and s1 stand for the two message words that Spec.G finds through the round r and the position
i. -/

theorem G_0 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        0 4 8 12 =
      #[(G s0 s1 v0 v4 v8 v12).a, v1, v2, v3, (G s0 s1 v0 v4 v8 v12).b, v5, v6, v7,
        (G s0 s1 v0 v4 v8 v12).c, v9, v10, v11, (G s0 s1 v0 v4 v8 v12).d, v13, v14, v15] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_0, set_0, get_4, set_4, get_8, set_8, get_12, set_12]

theorem G_1 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        1 5 9 13 =
      #[v0, (G s0 s1 v1 v5 v9 v13).a, v2, v3, v4, (G s0 s1 v1 v5 v9 v13).b, v6, v7, v8,
        (G s0 s1 v1 v5 v9 v13).c, v10, v11, v12, (G s0 s1 v1 v5 v9 v13).d, v14, v15] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_1, set_1, get_5, set_5, get_9, set_9, get_13, set_13]

theorem G_2 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        2 6 10 14 =
      #[v0, v1, (G s0 s1 v2 v6 v10 v14).a, v3, v4, v5, (G s0 s1 v2 v6 v10 v14).b, v7, v8, v9,
        (G s0 s1 v2 v6 v10 v14).c, v11, v12, v13, (G s0 s1 v2 v6 v10 v14).d, v15] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_2, set_2, get_6, set_6, get_10, set_10, get_14, set_14]

theorem G_3 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        3 7 11 15 =
      #[v0, v1, v2, (G s0 s1 v3 v7 v11 v15).a, v4, v5, v6, (G s0 s1 v3 v7 v11 v15).b, v8, v9, v10,
        (G s0 s1 v3 v7 v11 v15).c, v12, v13, v14, (G s0 s1 v3 v7 v11 v15).d] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_3, set_3, get_7, set_7, get_11, set_11, get_15, set_15]

theorem G_4 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        0 5 10 15 =
      #[(G s0 s1 v0 v5 v10 v15).a, v1, v2, v3, v4, (G s0 s1 v0 v5 v10 v15).b, v6, v7, v8, v9,
        (G s0 s1 v0 v5 v10 v15).c, v11, v12, v13, v14, (G s0 s1 v0 v5 v10 v15).d] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_0, set_0, get_5, set_5, get_10, set_10, get_15, set_15]

theorem G_5 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        1 6 11 12 =
      #[v0, (G s0 s1 v1 v6 v11 v12).a, v2, v3, v4, v5, (G s0 s1 v1 v6 v11 v12).b, v7, v8, v9, v10,
        (G s0 s1 v1 v6 v11 v12).c, (G s0 s1 v1 v6 v11 v12).d, v13, v14, v15] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_1, set_1, get_6, set_6, get_11, set_11, get_12, set_12]

theorem G_6 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        2 7 8 13 =
      #[v0, v1, (G s0 s1 v2 v7 v8 v13).a, v3, v4, v5, v6, (G s0 s1 v2 v7 v8 v13).b,
        (G s0 s1 v2 v7 v8 v13).c, v9, v10, v11, v12, (G s0 s1 v2 v7 v8 v13).d, v14, v15] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_2, set_2, get_7, set_7, get_8, set_8, get_13, set_13]

theorem G_7 (m : Array UInt64) (r i : Nat)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 s0 s1 : UInt64}
    (hs0 : m[Spec.blake2b_sigma[r]![2 * i + 0]!]! = s0)
    (hs1 : m[Spec.blake2b_sigma[r]![2 * i + 1]!]! = s1) :
    Spec.G m #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] r i
        3 4 9 14 =
      #[v0, v1, v2, (G s0 s1 v3 v4 v9 v14).a, (G s0 s1 v3 v4 v9 v14).b, v5, v6, v7, v8,
        (G s0 s1 v3 v4 v9 v14).c, v10, v11, v12, v13, (G s0 s1 v3 v4 v9 v14).d, v15] := by
  subst hs0 hs1
  simp only [Spec.G, G, rotr_eq, get_3, set_3, get_4, set_4, get_9, set_9, get_14, set_14]

/-! ## A round -/

/-- The work vector as the array v of sixteen long words in Spec.blake2b_compress. -/
def WorkVector.arr (v : WorkVector) : Array UInt64 :=
  #[v.v0, v.v1, v.v2, v.v3, v.v4, v.v5, v.v6, v.v7, v.v8, v.v9, v.v10, v.v11, v.v12, v.v13, v.v14,
    v.v15]

/-- A round, for any round number r; s k stands for the message word at place k of the round's row
of blake2b_sigma. -/
theorem round_arr (m : Array UInt64) (r : Nat) (v : WorkVector) (s : Nat → UInt64)
    (hs : ∀ k, m[Spec.blake2b_sigma[r]![k]!]! = s k) :
    Spec.ROUND m v.arr r =
      (ROUND (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) (s 8) (s 9) (s 10) (s 11) (s 12) (s 13)
        (s 14) (s 15) v).arr := by
  show Spec.G m (Spec.G m (Spec.G m (Spec.G m (Spec.G m (Spec.G m (Spec.G m (Spec.G m
    #[v.v0, v.v1, v.v2, v.v3, v.v4, v.v5, v.v6, v.v7, v.v8, v.v9, v.v10, v.v11, v.v12, v.v13, v.v14,
      v.v15]
    r 0 0 4 8 12) r 1 1 5 9 13) r 2 2 6 10 14) r 3 3 7 11 15) r 4 0 5 10 15) r 5 1 6 11 12)
    r 6 2 7 8 13) r 7 3 4 9 14 = _
  rw [G_0 m r 0 (hs 0) (hs 1), G_1 m r 1 (hs 2) (hs 3), G_2 m r 2 (hs 4) (hs 5),
    G_3 m r 3 (hs 6) (hs 7), G_4 m r 4 (hs 8) (hs 9), G_5 m r 5 (hs 10) (hs 11),
    G_6 m r 6 (hs 12) (hs 13), G_7 m r 7 (hs 14) (hs 15)]
  rfl

theorem round_0 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 0 =
      (ROUND m[0]! m[1]! m[2]! m[3]! m[4]! m[5]! m[6]! m[7]! m[8]! m[9]! m[10]! m[11]! m[12]! m[13]!
        m[14]! m[15]! v).arr :=
  round_arr m 0 v (fun k => m[Spec.blake2b_sigma[0]![k]!]!) (fun _ => rfl)

theorem round_1 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 1 =
      (ROUND m[14]! m[10]! m[4]! m[8]! m[9]! m[15]! m[13]! m[6]! m[1]! m[12]! m[0]! m[2]! m[11]!
        m[7]! m[5]! m[3]! v).arr :=
  round_arr m 1 v (fun k => m[Spec.blake2b_sigma[1]![k]!]!) (fun _ => rfl)

theorem round_2 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 2 =
      (ROUND m[11]! m[8]! m[12]! m[0]! m[5]! m[2]! m[15]! m[13]! m[10]! m[14]! m[3]! m[6]! m[7]!
        m[1]! m[9]! m[4]! v).arr :=
  round_arr m 2 v (fun k => m[Spec.blake2b_sigma[2]![k]!]!) (fun _ => rfl)

theorem round_3 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 3 =
      (ROUND m[7]! m[9]! m[3]! m[1]! m[13]! m[12]! m[11]! m[14]! m[2]! m[6]! m[5]! m[10]! m[4]!
        m[0]! m[15]! m[8]! v).arr :=
  round_arr m 3 v (fun k => m[Spec.blake2b_sigma[3]![k]!]!) (fun _ => rfl)

theorem round_4 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 4 =
      (ROUND m[9]! m[0]! m[5]! m[7]! m[2]! m[4]! m[10]! m[15]! m[14]! m[1]! m[11]! m[12]! m[6]!
        m[8]! m[3]! m[13]! v).arr :=
  round_arr m 4 v (fun k => m[Spec.blake2b_sigma[4]![k]!]!) (fun _ => rfl)

theorem round_5 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 5 =
      (ROUND m[2]! m[12]! m[6]! m[10]! m[0]! m[11]! m[8]! m[3]! m[4]! m[13]! m[7]! m[5]! m[15]!
        m[14]! m[1]! m[9]! v).arr :=
  round_arr m 5 v (fun k => m[Spec.blake2b_sigma[5]![k]!]!) (fun _ => rfl)

theorem round_6 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 6 =
      (ROUND m[12]! m[5]! m[1]! m[15]! m[14]! m[13]! m[4]! m[10]! m[0]! m[7]! m[6]! m[3]! m[9]!
        m[2]! m[8]! m[11]! v).arr :=
  round_arr m 6 v (fun k => m[Spec.blake2b_sigma[6]![k]!]!) (fun _ => rfl)

theorem round_7 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 7 =
      (ROUND m[13]! m[11]! m[7]! m[14]! m[12]! m[1]! m[3]! m[9]! m[5]! m[0]! m[15]! m[4]! m[8]!
        m[6]! m[2]! m[10]! v).arr :=
  round_arr m 7 v (fun k => m[Spec.blake2b_sigma[7]![k]!]!) (fun _ => rfl)

theorem round_8 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 8 =
      (ROUND m[6]! m[15]! m[14]! m[9]! m[11]! m[3]! m[0]! m[8]! m[12]! m[2]! m[13]! m[7]! m[1]!
        m[4]! m[10]! m[5]! v).arr :=
  round_arr m 8 v (fun k => m[Spec.blake2b_sigma[8]![k]!]!) (fun _ => rfl)

theorem round_9 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 9 =
      (ROUND m[10]! m[2]! m[8]! m[4]! m[7]! m[6]! m[1]! m[5]! m[15]! m[11]! m[9]! m[14]! m[3]!
        m[12]! m[13]! m[0]! v).arr :=
  round_arr m 9 v (fun k => m[Spec.blake2b_sigma[9]![k]!]!) (fun _ => rfl)

theorem round_10 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 10 =
      (ROUND m[0]! m[1]! m[2]! m[3]! m[4]! m[5]! m[6]! m[7]! m[8]! m[9]! m[10]! m[11]! m[12]! m[13]!
        m[14]! m[15]! v).arr :=
  round_arr m 10 v (fun k => m[Spec.blake2b_sigma[10]![k]!]!) (fun _ => rfl)

theorem round_11 (m : Array UInt64) (v : WorkVector) :
    Spec.ROUND m v.arr 11 =
      (ROUND m[14]! m[10]! m[4]! m[8]! m[9]! m[15]! m[13]! m[6]! m[1]! m[12]! m[0]! m[2]! m[11]!
        m[7]! m[5]! m[3]! v).arr :=
  round_arr m 11 v (fun k => m[Spec.blake2b_sigma[11]![k]!]!) (fun _ => rfl)

/-! ## The steps before and after the rounds -/

theorem blk_0 (b : MessageBlock) : b.arr[0]! = b.m0 := rfl
theorem blk_1 (b : MessageBlock) : b.arr[1]! = b.m1 := rfl
theorem blk_2 (b : MessageBlock) : b.arr[2]! = b.m2 := rfl
theorem blk_3 (b : MessageBlock) : b.arr[3]! = b.m3 := rfl
theorem blk_4 (b : MessageBlock) : b.arr[4]! = b.m4 := rfl
theorem blk_5 (b : MessageBlock) : b.arr[5]! = b.m5 := rfl
theorem blk_6 (b : MessageBlock) : b.arr[6]! = b.m6 := rfl
theorem blk_7 (b : MessageBlock) : b.arr[7]! = b.m7 := rfl
theorem blk_8 (b : MessageBlock) : b.arr[8]! = b.m8 := rfl
theorem blk_9 (b : MessageBlock) : b.arr[9]! = b.m9 := rfl
theorem blk_10 (b : MessageBlock) : b.arr[10]! = b.m10 := rfl
theorem blk_11 (b : MessageBlock) : b.arr[11]! = b.m11 := rfl
theorem blk_12 (b : MessageBlock) : b.arr[12]! = b.m12 := rfl
theorem blk_13 (b : MessageBlock) : b.arr[13]! = b.m13 := rfl
theorem blk_14 (b : MessageBlock) : b.arr[14]! = b.m14 := rfl
theorem blk_15 (b : MessageBlock) : b.arr[15]! = b.m15 := rfl

theorem range16 : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl

theorem rep16 :
    Array.replicate 16 (0 : UInt64) =
      (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array UInt64) := rfl

/-- The loop that loads the block's sixteen long words. -/
theorem msg_arr (block : Array UInt8) :
    (List.range 16).foldl (fun (m : Array UInt64) i => m.set! i (Spec.load64 block (i * 8)))
      (Array.replicate 16 0) = (MessageBlock.ofBytes ⟨block⟩ 0).arr := by
  simp only [range16, rep16, List.foldl_cons, List.foldl_nil, set_0, set_1, set_2, set_3, set_4,
    set_5, set_6, set_7, set_8, set_9, set_10, set_11, set_12, set_13, set_14, set_15,
    load64_fast]
  rfl

/-- The first work vector. -/
theorem start_arr (h : ChainingValue) (t0 t1 f0 f1 : UInt64) :
    ((((((((((List.range 8).foldl (fun (v : Array UInt64) i => v.set! i h.arr[i]!)
      (Array.replicate 16 0)).set! 8 Spec.blake2b_IV[0]!).set! 9 Spec.blake2b_IV[1]!).set! 10
      Spec.blake2b_IV[2]!).set! 11 Spec.blake2b_IV[3]!).set! 12 (Spec.blake2b_IV[4]! ^^^ t0)).set!
      13 (Spec.blake2b_IV[5]! ^^^ t1)).set! 14 (Spec.blake2b_IV[6]! ^^^ f0)).set! 15
      (Spec.blake2b_IV[7]! ^^^ f1)) =
      (⟨h.h0, h.h1, h.h2, h.h3, h.h4, h.h5, h.h6, h.h7, IV.h0, IV.h1, IV.h2, IV.h3, IV.h4 ^^^ t0,
        IV.h5 ^^^ t1, IV.h6 ^^^ f0, IV.h7 ^^^ f1⟩ : WorkVector).arr := by
  simp only [range8, rep16, List.foldl_cons, List.foldl_nil, set_0, set_1, set_2, set_3, set_4,
    set_5, set_6, set_7, set_8, set_9, set_10, set_11, set_12, set_13, set_14, set_15]
  rfl

/-- The loop that makes the new chaining value. -/
theorem last_arr (h : ChainingValue) (w : WorkVector) :
    (List.range 8).foldl
      (fun (a : Array UInt64) i => a.set! i (a[i]! ^^^ w.arr[i]! ^^^ w.arr[i + 8]!)) h.arr =
      (⟨h.h0 ^^^ w.v0 ^^^ w.v8, h.h1 ^^^ w.v1 ^^^ w.v9, h.h2 ^^^ w.v2 ^^^ w.v10,
        h.h3 ^^^ w.v3 ^^^ w.v11, h.h4 ^^^ w.v4 ^^^ w.v12, h.h5 ^^^ w.v5 ^^^ w.v13,
        h.h6 ^^^ w.v6 ^^^ w.v14, h.h7 ^^^ w.v7 ^^^ w.v15⟩ : ChainingValue).arr := by
  simp only [ChainingValue.arr, WorkVector.arr, range8, List.foldl_cons, List.foldl_nil, Nat.reduceAdd, get8_0,
    get8_1, get8_2, get8_3, get8_4, get8_5, get8_6, get8_7, set8_0, set8_1, set8_2, set8_3, set8_4,
    set8_5, set8_6, set8_7, get_0, get_1, get_2, get_3, get_4, get_5, get_6, get_7, get_8, get_9,
    get_10, get_11, get_12, get_13, get_14, get_15] <;> rfl

/-! ## The compression function -/

/-- The fast compress computes the new chaining value of Spec.blake2b_compress. -/
theorem compress_h (S : Spec.blake2b_state) (block : Array UInt8) (T : State)
    (hh : S.h = T.h.arr) (h0 : S.t0 = T.t0) (h1 : S.t1 = T.t1) (hf0 : S.f0 = T.f0)
    (hf1 : S.f1 = T.f1) :
    (Spec.blake2b_compress S block).h = (compress T (MessageBlock.ofBytes ⟨block⟩ 0)).h.arr := by
  unfold Spec.blake2b_compress compress
  simp only [hh, h0, h1, hf0, hf1, msg_arr, start_arr, round_0, round_1, round_2, round_3, round_4,
    round_5, round_6, round_7, round_8, round_9, round_10, round_11, blk_0, blk_1, blk_2, blk_3,
    blk_4, blk_5, blk_6, blk_7, blk_8, blk_9, blk_10, blk_11, blk_12, blk_13, blk_14, blk_15,
    last_arr]

theorem compress_t0 (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).t0 = S.t0 := by
  simp only [Spec.blake2b_compress]

theorem compress_t1 (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).t1 = S.t1 := by
  simp only [Spec.blake2b_compress]

theorem compress_f0 (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).f0 = S.f0 := by
  simp only [Spec.blake2b_compress]

theorem compress_f1 (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).f1 = S.f1 := by
  simp only [Spec.blake2b_compress]

theorem compress_buf (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).buf = S.buf := by
  simp only [Spec.blake2b_compress]

theorem compress_buflen (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).buflen = S.buflen := by
  simp only [Spec.blake2b_compress]

theorem compress_outlen (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).outlen = S.outlen := by
  simp only [Spec.blake2b_compress]

theorem compress_last_node (S : Spec.blake2b_state) (block : Array UInt8) :
    (Spec.blake2b_compress S block).last_node = S.last_node := by
  simp only [Spec.blake2b_compress]

/-- Spec.blake2b_compress changes the field h only. -/
theorem compress_self (S : Spec.blake2b_state) (block : Array UInt8) :
    Spec.blake2b_compress S block = { S with h := (Spec.blake2b_compress S block).h } := by
  simp only [Spec.blake2b_compress]

/-- The state after Spec.blake2b_compress: the fast compress makes the new h, the rest stays. -/
theorem compress_eq (S : Spec.blake2b_state) (block : Array UInt8) (T : State)
    (hh : S.h = T.h.arr) (h0 : S.t0 = T.t0) (h1 : S.t1 = T.t1) (hf0 : S.f0 = T.f0)
    (hf1 : S.f1 = T.f1) :
    Spec.blake2b_compress S block =
      { S with h := (compress T (MessageBlock.ofBytes ⟨block⟩ 0)).h.arr } := by
  rw [← compress_h S block T hh h0 h1 hf0 hf1]
  exact compress_self S block

/-! ## Chaining values and blocks against arrays -/

theorem ofArr_arr (m : MessageBlock) : MessageBlock.ofArr m.arr = m := rfl

/-- An array of eight long words is the array of its chaining value. -/
theorem arr_ofArr (h : Array UInt64) (hs : h.size = 8) : (ChainingValue.ofArr h).arr = h := by
  obtain ⟨l⟩ := h
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
    ⟨a8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | rfl
    | (exfalso; simp only [List.size_toArray, List.length_cons, List.length_nil] at hs; omega)

end Run.Blake2b
