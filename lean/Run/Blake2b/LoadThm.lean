-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.SpecFast
import Run.Blake2b.HashThm
/-!
# Loads, stores, the counter and the first state

Small ties between the plain definition of Spec.lean and the functions of Hash.lean:

* load64_eq: Spec.load64 reads the long word of load64Plain.
* ofBytes_congr: a block depends on its 128 bytes only.
* size_memcpy, getD_memcpy_in, getD_memcpy_before and the like for memset: what the two copies of
  string.h leave in an array.
* increment_at: Spec.blake2b_increment_counter and incrementCounter move a counter in the same way.
* init_eq, init_key_eq: the states of Spec.blake2b_init and Spec.blake2b_init_key, with firstState.
* store_eq: the eight calls of Spec.store64 write the 64 bytes of ChainingValue.bytes64.
Source. All are theorems about the definitions of Spec.lean and Hash.lean, with firstSpec and the
notation pblock to state them. Some write out again what these definitions have from their source,
among them: pblock and the statements of param_block and init_param_first (the parameter block and
the writes of Spec.blake2b_init), load_first and load_zeros (the eight bytes of a word of that
block, as Spec.load64 reads them), key_block (the block that Spec.blake2b_init_key fills with the
key), increment_eq and incrementCounter_eq (the counter's step), store64_eq and store_eq (the eight
bytes of Spec.store64, and its eight calls in Spec.blake2b_final). These follow, at one remove, what
the two files name as their source.
Spec.lean's head says (its lines 7 and 8, copied here):
Adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the BLAKE2 reference source code package,
Copyright 2012 Samuel Neves, taken under CC0 1.0 Universal.
Hash.lean's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
-/
namespace Run.Blake2b

/-! ## 1. Loads and blocks -/

theorem get!_eq_getD (x : Array UInt8) (i : Nat) : x[i]! = x.getD i 0 := rfl

/-- Spec.load64 reads the long word that load64Plain reads, with zeros after the end. -/
theorem load64_eq (src : Array UInt8) (off : Nat) :
    Spec.load64 src off = load64Plain ⟨src⟩ off := by
  unfold Spec.load64 load64Plain
  simp only [byteOrZero_mk, get!_eq_getD]

/-- A long word depends on eight bytes only. -/
theorem load64Plain_congr {x y : Array UInt8} {k l : Nat}
    (h : ∀ j, j < 8 → x.getD (k + j) 0 = y.getD (l + j) 0) :
    load64Plain ⟨x⟩ k = load64Plain ⟨y⟩ l := by
  unfold load64Plain
  simp only [byteOrZero_mk]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-- A block depends on 128 bytes only. -/
theorem ofBytes_congr {x y : Array UInt8} {a b : Nat}
    (h : ∀ j, j < 128 → x.getD (a + j) 0 = y.getD (b + j) 0) :
    MessageBlock.ofBytes ⟨x⟩ a = MessageBlock.ofBytes ⟨y⟩ b := by
  have key : ∀ q, q + 8 ≤ 128 → load64 ⟨x⟩ (a + q) = load64 ⟨y⟩ (b + q) := by
    intro q hq
    rw [load64_eq_plain, load64_eq_plain]
    apply load64Plain_congr
    intro j hj
    have := h (q + j) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at this
    exact this
  unfold MessageBlock.ofBytes
  rw [key (8 * 0) (by omega), key (8 * 1) (by omega), key (8 * 2) (by omega),
    key (8 * 3) (by omega), key (8 * 4) (by omega), key (8 * 5) (by omega),
    key (8 * 6) (by omega), key (8 * 7) (by omega), key (8 * 8) (by omega),
    key (8 * 9) (by omega), key (8 * 10) (by omega), key (8 * 11) (by omega),
    key (8 * 12) (by omega), key (8 * 13) (by omega), key (8 * 14) (by omega),
    key (8 * 15) (by omega)]

/-! ## 2. memcpy and memset -/

theorem size_memcpy (dst : Array UInt8) (doff : Nat) (src : Array UInt8) (soff n : Nat)
    (h1 : doff + n ≤ dst.size) (h2 : soff + n ≤ src.size) :
    (Spec.memcpy dst doff src soff n).size = dst.size := by
  unfold Spec.memcpy
  simp only [Array.size_append, Array.size_extract]
  omega

/-- Inside the copied range memcpy leaves the bytes of src. -/
theorem getD_memcpy_in (dst : Array UInt8) (doff : Nat) (src : Array UInt8) (soff n j : Nat)
    (h1 : doff + n ≤ dst.size) (h2 : soff + n ≤ src.size) (hj : j < n) :
    (Spec.memcpy dst doff src soff n).getD (doff + j) 0 = src.getD (soff + j) 0 := by
  have s1 : (dst.extract 0 doff).size = doff := by rw [Array.size_extract]; omega
  have s2 : (dst.extract 0 doff ++ src.extract soff (soff + n)).size = doff + n := by
    rw [Array.size_append, Array.size_extract, Array.size_extract]; omega
  unfold Spec.memcpy
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left (by omega), Array.getElem?_append_right (by omega), s1,
    Array.getElem?_extract, if_pos (by omega), show doff + j - doff = j from by omega]

/-- Before the copied range memcpy leaves the bytes of dst. -/
theorem getD_memcpy_before (dst : Array UInt8) (doff : Nat) (src : Array UInt8) (soff n j : Nat)
    (h1 : doff + n ≤ dst.size) (h2 : soff + n ≤ src.size) (hj : j < doff) :
    (Spec.memcpy dst doff src soff n).getD j 0 = dst.getD j 0 := by
  have s1 : (dst.extract 0 doff).size = doff := by rw [Array.size_extract]; omega
  have s2 : (dst.extract 0 doff ++ src.extract soff (soff + n)).size = doff + n := by
    rw [Array.size_append, Array.size_extract, Array.size_extract]; omega
  unfold Spec.memcpy
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left (by omega), Array.getElem?_append_left (by omega),
    Array.getElem?_extract, if_pos (by omega), Nat.zero_add]

theorem size_memset (dst : Array UInt8) (doff : Nat) (c : UInt8) (n : Nat)
    (h1 : doff + n ≤ dst.size) : (Spec.memset dst doff c n).size = dst.size := by
  unfold Spec.memset
  simp only [Array.size_append, Array.size_extract, Array.size_replicate]
  omega

/-- Inside the filled range memset leaves the byte c. -/
theorem getD_memset_in (dst : Array UInt8) (doff : Nat) (c : UInt8) (n j : Nat)
    (h1 : doff + n ≤ dst.size) (hj : j < n) : (Spec.memset dst doff c n).getD (doff + j) 0 = c := by
  have s1 : (dst.extract 0 doff).size = doff := by rw [Array.size_extract]; omega
  have s2 : (dst.extract 0 doff ++ Array.replicate n c).size = doff + n := by
    rw [Array.size_append, Array.size_extract, Array.size_replicate]; omega
  unfold Spec.memset
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by omega),
    Array.getElem?_append_right (by omega), s1, Array.getElem?_replicate, if_pos (by omega),
    Option.getD_some]

/-- Before the filled range memset leaves the bytes of dst. -/
theorem getD_memset_before (dst : Array UInt8) (doff : Nat) (c : UInt8) (n j : Nat)
    (h1 : doff + n ≤ dst.size) (hj : j < doff) :
    (Spec.memset dst doff c n).getD j 0 = dst.getD j 0 := by
  have s1 : (dst.extract 0 doff).size = doff := by rw [Array.size_extract]; omega
  have s2 : (dst.extract 0 doff ++ Array.replicate n c).size = doff + n := by
    rw [Array.size_append, Array.size_extract, Array.size_replicate]; omega
  unfold Spec.memset
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left (by omega), Array.getElem?_append_left (by omega),
    Array.getElem?_extract, if_pos (by omega), Nat.zero_add]

/-! ## 3. The counter -/

/-- Spec.blake2b_increment_counter changes the two words of the counter only. -/
theorem increment_eq (S : Spec.blake2b_state) (inc : UInt64) :
    Spec.blake2b_increment_counter S inc =
      { S with t0 := S.t0 + inc, t1 := S.t1 + (if S.t0 + inc < inc then 1 else 0) } := rfl

/-- incrementCounter of Hash.lean, written out: it changes the two words of the counter only. -/
theorem incrementCounter_eq (T : State) (inc : UInt64) :
    incrementCounter T inc =
      { T with t0 := T.t0 + inc, t1 := T.t1 + (if T.t0 + inc < inc then 1 else 0) } := rfl

/-- From the same counter the two functions come to the same counter. -/
theorem increment_at (S : Spec.blake2b_state) (T : State) (inc : UInt64) (h0 : S.t0 = T.t0)
    (h1 : S.t1 = T.t1) :
    (Spec.blake2b_increment_counter S inc).t0 = (incrementCounter T inc).t0 ∧
      (Spec.blake2b_increment_counter S inc).t1 = (incrementCounter T inc).t1 := by
  rw [increment_eq, incrementCounter_eq]
  show S.t0 + inc = T.t0 + inc ∧
    S.t1 + (if S.t0 + inc < inc then 1 else 0) = T.t1 + (if T.t0 + inc < inc then 1 else 0)
  rw [h0, h1]
  exact ⟨rfl, rfl⟩

/-! ## 4. The first state -/

/-- The state of Spec.blake2b_init_param for a key of keylen bytes and a digest of outlen bytes. -/
def firstSpec (keylen outlen : Nat) : Spec.blake2b_state :=
  { h := (firstState keylen outlen).h.arr, t0 := 0, t1 := 0, f0 := 0, f1 := 0,
    buf := Array.replicate 128 0, buflen := 0, outlen := outlen, last_node := 0 }

/-- The parameter block with a and b in its first two bytes. -/
local notation:max "pblock(" a ", " b ")" => (#[a, b, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array UInt8)

/-- A write into the first four bytes of an array that is given in two parts. -/
theorem set_head (H H' R : Array UInt8) (i : Nat) (v : UInt8) (hs : H.size = 4) (hi : i < 4)
    (hm : H.setIfInBounds i v = H') : (H ++ R).set! i v = H' ++ R := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_append_left (by omega), hm]

/-- A zero written behind the first four bytes, where zeros stand, changes nothing. -/
theorem set_tail (H : Array UInt8) (i : Nat) (hs : H.size = 4) (h1 : 4 ≤ i) (h2 : i < 64) :
    (H ++ Array.replicate 60 0).set! i 0 = H ++ Array.replicate 60 0 := by
  have t : ∀ k, k < 60 →
      (Array.replicate 60 (0 : UInt8)).setIfInBounds k 0 = Array.replicate 60 0 := by
    decide +kernel
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_append_right (by omega), t _ (by omega)]

/-- Spec.store32 of zero behind the first four bytes, where zeros stand, changes nothing. -/
theorem store32_tail (H : Array UInt8) (off : Nat) (hs : H.size = 4) (h1 : 4 ≤ off)
    (h2 : off + 3 < 64) :
    Spec.store32 (H ++ Array.replicate 60 0) off 0 = H ++ Array.replicate 60 0 := by
  have v0 : ((0 : UInt32) >>> 0).toUInt8 = 0 := by decide
  have v1 : ((0 : UInt32) >>> 8).toUInt8 = 0 := by decide
  have v2 : ((0 : UInt32) >>> 16).toUInt8 = 0 := by decide
  have v3 : ((0 : UInt32) >>> 24).toUInt8 = 0 := by decide
  simp only [Spec.store32, v0, v1, v2, v3]
  rw [set_tail H _ hs (by omega) (by omega), set_tail H _ hs (by omega) (by omega),
    set_tail H _ hs (by omega) (by omega), set_tail H _ hs (by omega) (by omega)]

/-- Spec.memset behind the first part of an array that is given in two parts. -/
theorem memset_tail (H R : Array UInt8) (doff d n : Nat) (c : UInt8) (hd : doff = H.size + d) :
    Spec.memset (H ++ R) doff c n = H ++ Spec.memset R d c n := by
  subst hd
  have a1 : 0 - H.size = 0 := by omega
  have a2 : H.size + d - H.size = d := by omega
  have a3 : H.size + d + n - H.size = d + n := by omega
  have a4 : H.size + R.size - H.size = R.size := by omega
  unfold Spec.memset
  rw [Array.extract_append, Array.extract_append, Array.size_append, a1, a2, a3, a4,
    Array.extract_eq_self_of_le (Nat.le_add_right _ _),
    Array.extract_empty_of_size_le_start (xs := H) (start := H.size + d + n) (by omega),
    Array.empty_append]
  simp only [Array.append_assoc]

theorem block_parts (a b : UInt8) : #[a, b, 1, 1] ++ Array.replicate 60 0 = pblock(a, b) := by
  have r : Array.replicate 60 (0 : UInt8) =
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [r]
  exact List.append_toArray _ _

/-- The parameter block that Spec.blake2b_init and Spec.blake2b_init_key fill in, written out. -/
theorem param_block (a b : UInt8) :
    Spec.memset (Spec.memset (Spec.memset
      (((Spec.store32 (Spec.store32 (Spec.store32
        (((((Array.replicate 64 (0 : UInt8)).set! 0 a).set! 1 b).set! 2 1).set! 3 1)
        4 0) 8 0) 12 0).set! 16 0).set! 17 0) 18 0 14) 32 0 16) 48 0 16 = pblock(a, b) := by
  have n0 : Array.replicate 64 (0 : UInt8) = #[0, 0, 0, 0] ++ Array.replicate 60 0 := by
    decide +kernel
  have m1 : Spec.memset (Array.replicate 60 0) 14 0 14 = Array.replicate 60 0 := by decide +kernel
  have m2 : Spec.memset (Array.replicate 60 0) 28 0 16 = Array.replicate 60 0 := by decide +kernel
  have m3 : Spec.memset (Array.replicate 60 0) 44 0 16 = Array.replicate 60 0 := by decide +kernel
  rw [n0, set_head #[0, 0, 0, 0] #[a, 0, 0, 0] _ 0 a rfl (by decide) rfl,
    set_head #[a, 0, 0, 0] #[a, b, 0, 0] _ 1 b rfl (by decide) rfl,
    set_head #[a, b, 0, 0] #[a, b, 1, 0] _ 2 1 rfl (by decide) rfl,
    set_head #[a, b, 1, 0] #[a, b, 1, 1] _ 3 1 rfl (by decide) rfl,
    store32_tail #[a, b, 1, 1] 4 rfl (by decide) (by decide),
    store32_tail #[a, b, 1, 1] 8 rfl (by decide) (by decide),
    store32_tail #[a, b, 1, 1] 12 rfl (by decide) (by decide),
    set_tail #[a, b, 1, 1] 16 rfl (by decide) (by decide),
    set_tail #[a, b, 1, 1] 17 rfl (by decide) (by decide),
    memset_tail #[a, b, 1, 1] _ 18 14 14 0 rfl, m1, memset_tail #[a, b, 1, 1] _ 32 28 16 0 rfl, m2,
    memset_tail #[a, b, 1, 1] _ 48 44 16 0 rfl, m3]
  exact block_parts a b

/-- The state of Spec.blake2b_init_param by the eight long words of the parameter block. -/
theorem init_param_eq (P : Array UInt8) :
    Spec.blake2b_init_param P =
      { h := #[IV.h0 ^^^ Spec.load64 P 0, IV.h1 ^^^ Spec.load64 P 8, IV.h2 ^^^ Spec.load64 P 16,
          IV.h3 ^^^ Spec.load64 P 24, IV.h4 ^^^ Spec.load64 P 32, IV.h5 ^^^ Spec.load64 P 40,
          IV.h6 ^^^ Spec.load64 P 48, IV.h7 ^^^ Spec.load64 P 56],
        t0 := 0, t1 := 0, f0 := 0, f1 := 0, buf := Array.replicate 128 0, buflen := 0,
        outlen := (P[0]!).toNat, last_node := 0 } := by
  have g0 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[0]! = v0 := fun _ _ _ _ _ _ _ _ => rfl
  have g1 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[1]! = v1 := fun _ _ _ _ _ _ _ _ => rfl
  have g2 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[2]! = v2 := fun _ _ _ _ _ _ _ _ => rfl
  have g3 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[3]! = v3 := fun _ _ _ _ _ _ _ _ => rfl
  have g4 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[4]! = v4 := fun _ _ _ _ _ _ _ _ => rfl
  have g5 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[5]! = v5 := fun _ _ _ _ _ _ _ _ => rfl
  have g6 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[6]! = v6 := fun _ _ _ _ _ _ _ _ => rfl
  have g7 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64)[7]! = v7 := fun _ _ _ _ _ _ _ _ => rfl
  have s0 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 0 x =
        #[x, v1, v2, v3, v4, v5, v6, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s1 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 1 x =
        #[v0, x, v2, v3, v4, v5, v6, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s2 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 2 x =
        #[v0, v1, x, v3, v4, v5, v6, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s3 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 3 x =
        #[v0, v1, v2, x, v4, v5, v6, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s4 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 4 x =
        #[v0, v1, v2, v3, x, v5, v6, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s5 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 5 x =
        #[v0, v1, v2, v3, v4, x, v6, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s6 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 6 x =
        #[v0, v1, v2, v3, v4, v5, x, v7] := fun _ _ _ _ _ _ _ _ _ => rfl
  have s7 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 x : UInt64,
      (#[v0, v1, v2, v3, v4, v5, v6, v7] : Array UInt64).set! 7 x =
        #[v0, v1, v2, v3, v4, v5, v6, x] := fun _ _ _ _ _ _ _ _ _ => rfl
  have ih : Spec.blake2b_init0.h = #[IV.h0, IV.h1, IV.h2, IV.h3, IV.h4, IV.h5, IV.h6, IV.h7] := by
    decide +kernel
  have i0 : Spec.blake2b_init0.t0 = 0 := by decide +kernel
  have i1 : Spec.blake2b_init0.t1 = 0 := by decide +kernel
  have i2 : Spec.blake2b_init0.f0 = 0 := by decide +kernel
  have i3 : Spec.blake2b_init0.f1 = 0 := by decide +kernel
  have i4 : Spec.blake2b_init0.buf = Array.replicate 128 0 := by decide +kernel
  have i5 : Spec.blake2b_init0.buflen = 0 := by decide +kernel
  have i6 : Spec.blake2b_init0.last_node = 0 := by decide +kernel
  simp only [Spec.blake2b_init_param, Spec.blake2b_param.digest_length, ih, i0, i1, i2, i3, i4, i5,
    i6, range8, List.foldl, g0, g1, g2, g3, g4, g5, g6, g7, s0, s1, s2, s3, s4, s5, s6, s7,
    Nat.reduceMul]

theorem load_first (a b : UInt8) :
    (a.toUInt64 <<< 0) ||| (b.toUInt64 <<< 8) ||| ((1 : UInt8).toUInt64 <<< 16) |||
      ((1 : UInt8).toUInt64 <<< 24) ||| ((0 : UInt8).toUInt64 <<< 32) |||
      ((0 : UInt8).toUInt64 <<< 40) ||| ((0 : UInt8).toUInt64 <<< 48) |||
      ((0 : UInt8).toUInt64 <<< 56) =
      a.toUInt64 ||| (b.toUInt64 <<< 8) ||| ((1 : UInt64) <<< 16) ||| ((1 : UInt64) <<< 24) := by
  have e1 : (1 : UInt8).toUInt64 = 1 := rfl
  have e0 : (0 : UInt8).toUInt64 = 0 := rfl
  simp only [e1, e0, UInt64.shiftLeft_zero, UInt64.zero_shiftLeft, UInt64.or_zero]

theorem load_zeros :
    ((0 : UInt8).toUInt64 <<< 0) ||| ((0 : UInt8).toUInt64 <<< 8) |||
      ((0 : UInt8).toUInt64 <<< 16) ||| ((0 : UInt8).toUInt64 <<< 24) |||
      ((0 : UInt8).toUInt64 <<< 32) ||| ((0 : UInt8).toUInt64 <<< 40) |||
      ((0 : UInt8).toUInt64 <<< 48) ||| ((0 : UInt8).toUInt64 <<< 56) = (0 : UInt64) := by decide

/-- Spec.blake2b_init_param on the written-out parameter block. -/
theorem init_param_block (a b : UInt8) :
    Spec.blake2b_init_param pblock(a, b) =
      { h := #[IV.h0 ^^^
            (a.toUInt64 ||| (b.toUInt64 <<< 8) ||| ((1 : UInt64) <<< 16) ||| ((1 : UInt64) <<< 24)),
          IV.h1, IV.h2, IV.h3, IV.h4, IV.h5, IV.h6, IV.h7],
        t0 := 0, t1 := 0, f0 := 0, f1 := 0, buf := Array.replicate 128 0, buflen := 0,
        outlen := a.toNat, last_node := 0 } := by
  have w0 : Spec.load64 pblock(a, b) 0 =
      a.toUInt64 ||| (b.toUInt64 <<< 8) ||| ((1 : UInt64) <<< 16) ||| ((1 : UInt64) <<< 24) :=
    load_first a b
  have w1 : Spec.load64 pblock(a, b) 8 = 0 := load_zeros
  have w2 : Spec.load64 pblock(a, b) 16 = 0 := load_zeros
  have w3 : Spec.load64 pblock(a, b) 24 = 0 := load_zeros
  have w4 : Spec.load64 pblock(a, b) 32 = 0 := load_zeros
  have w5 : Spec.load64 pblock(a, b) 40 = 0 := load_zeros
  have w6 : Spec.load64 pblock(a, b) 48 = 0 := load_zeros
  have w7 : Spec.load64 pblock(a, b) 56 = 0 := load_zeros
  have o : (pblock(a, b))[0]! = a := rfl
  rw [init_param_eq, w0, w1, w2, w3, w4, w5, w6, w7, o]
  simp only [UInt64.xor_zero]

/-- The chaining value of firstState, word by word. -/
theorem firstState_arr (keylen outlen : Nat) :
    (firstState keylen outlen).h.arr =
      #[IV.h0 ^^^
          (outlen.toUInt64 ||| (keylen.toUInt64 <<< 8) ||| ((1 : UInt64) <<< 16) |||
            ((1 : UInt64) <<< 24)),
        IV.h1, IV.h2, IV.h3, IV.h4, IV.h5, IV.h6, IV.h7] := by
  simp only [firstState, initParam, init0, parameterBlockFirstWord, ChainingValue.arr, UInt64.xor_zero,
    UInt64.shiftLeft_zero]

/-- Spec.blake2b_init_param on the filled-in parameter block gives firstSpec. -/
theorem init_param_first (keylen outlen : Nat) (hk : keylen ≤ 64) (hn : outlen ≤ 64) :
    Spec.blake2b_init_param (Spec.memset (Spec.memset (Spec.memset
      (((Spec.store32 (Spec.store32 (Spec.store32
        (((((Array.replicate 64 (0 : UInt8)).set! 0 outlen.toUInt8).set! 1 keylen.toUInt8).set! 2
          1).set! 3 1) 4 0) 8 0) 12 0).set! 16 0).set! 17 0) 18 0 14) 32 0 16) 48 0 16) =
      firstSpec keylen outlen := by
  have ek : keylen.toUInt8.toUInt64 = keylen.toUInt64 :=
    UInt8.toUInt64_ofNat' (Nat.lt_of_le_of_lt hk (by decide))
  have en : outlen.toUInt8.toUInt64 = outlen.toUInt64 :=
    UInt8.toUInt64_ofNat' (Nat.lt_of_le_of_lt hn (by decide))
  have eo : outlen.toUInt8.toNat = outlen :=
    UInt8.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hn (by decide))
  rw [param_block, init_param_block, ek, en, eo]
  -- No single rfl here: to compare the two states a kernel may unfold the operations on the free
  -- variables keylen and outlen, at great cost in memory.
  unfold firstSpec
  rw [firstState_arr]

/-- The state of Spec.blake2b_init. -/
theorem init_eq (outlen : Nat) (h1 : 1 ≤ outlen) (h64 : outlen ≤ 64) :
    Spec.blake2b_init outlen = some (firstSpec 0 outlen) := by
  have hc : ¬ (outlen = 0 ∨ outlen > 64) := by omega
  refine (if_neg hc).trans (congrArg some ?_)
  exact init_param_first 0 outlen (Nat.zero_le _) h64

/-- The block that Spec.blake2b_init_key hands to Spec.blake2b_update: the key, then zeros. -/
theorem key_block (key : Array UInt8) :
    Spec.memcpy (Spec.memset (Array.replicate 128 0) 0 0 128) 0 key 0 key.size =
      key ++ Array.replicate (128 - key.size) 0 := by
  have m : Spec.memset (Array.replicate 128 0) 0 0 128 = Array.replicate 128 0 := by decide +kernel
  rw [m]
  unfold Spec.memcpy
  rw [Array.extract_zero, Array.empty_append, Nat.zero_add, Array.extract_size,
    Array.size_replicate, Array.extract_replicate, Nat.min_self]

/-- The state of Spec.blake2b_init_key: the key's block goes through Spec.blake2b_update. -/
theorem init_key_eq (outlen : Nat) (key : Array UInt8) (h1 : 1 ≤ outlen) (h64 : outlen ≤ 64)
    (k1 : 1 ≤ key.size) (k64 : key.size ≤ 64) :
    Spec.blake2b_init_key outlen key =
      some (Spec.blake2b_update (firstSpec key.size outlen)
        (key ++ Array.replicate (128 - key.size) 0)) := by
  have hc : ¬ (outlen = 0 ∨ outlen > 64) := by omega
  have hk : ¬ (key.size = 0 ∨ key.size > 64) := by omega
  refine (if_neg hc).trans ((if_neg hk).trans (congrArg some ?_))
  exact congr (congrArg Spec.blake2b_update (init_param_first key.size outlen k64 h64))
    (key_block key)

/-! ## 5. The digest's bytes -/

/-- Spec.store64 as eight writes, with the first shift worked out. -/
theorem store64_eq (dst : Array UInt8) (off : Nat) (w : UInt64) :
    Spec.store64 dst off w =
      (((((((dst.set! (off + 0) w.toUInt8).set! (off + 1) (w >>> 8).toUInt8).set! (off + 2)
        (w >>> 16).toUInt8).set! (off + 3) (w >>> 24).toUInt8).set! (off + 4)
        (w >>> 32).toUInt8).set! (off + 5) (w >>> 40).toUInt8).set! (off + 6)
        (w >>> 48).toUInt8).set! (off + 7) (w >>> 56).toUInt8 := by
  simp only [Spec.store64, UInt64.shiftRight_zero]

/-- A write into the middle part, of eight bytes, of an array that is given in three parts. -/
theorem set_mid (pre mid mid' R : Array UInt8) (i : Nat) (x : UInt8) (hs : mid.size = 8)
    (hi : i < 8) (hm : mid.setIfInBounds i x = mid') :
    (pre ++ (mid ++ R)).set! (pre.size + i) x = pre ++ (mid' ++ R) := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, Array.setIfInBounds_append_left (by omega), hm]

/-- Eight writes fill the middle part. -/
theorem write8 (pre R : Array UInt8) (a b c d e f g h : UInt8) :
    ((((((((pre ++ (#[0, 0, 0, 0, 0, 0, 0, 0] ++ R)).set! (pre.size + 0) a).set! (pre.size + 1)
      b).set! (pre.size + 2) c).set! (pre.size + 3) d).set! (pre.size + 4) e).set!
      (pre.size + 5) f).set! (pre.size + 6) g).set! (pre.size + 7) h =
      pre ++ (#[a, b, c, d, e, f, g, h] ++ R) := by
  rw [set_mid pre #[0, 0, 0, 0, 0, 0, 0, 0] #[a, 0, 0, 0, 0, 0, 0, 0] R 0 a rfl (by decide) rfl,
    set_mid pre #[a, 0, 0, 0, 0, 0, 0, 0] #[a, b, 0, 0, 0, 0, 0, 0] R 1 b rfl (by decide) rfl,
    set_mid pre #[a, b, 0, 0, 0, 0, 0, 0] #[a, b, c, 0, 0, 0, 0, 0] R 2 c rfl (by decide) rfl,
    set_mid pre #[a, b, c, 0, 0, 0, 0, 0] #[a, b, c, d, 0, 0, 0, 0] R 3 d rfl (by decide) rfl,
    set_mid pre #[a, b, c, d, 0, 0, 0, 0] #[a, b, c, d, e, 0, 0, 0] R 4 e rfl (by decide) rfl,
    set_mid pre #[a, b, c, d, e, 0, 0, 0] #[a, b, c, d, e, f, 0, 0] R 5 f rfl (by decide) rfl,
    set_mid pre #[a, b, c, d, e, f, 0, 0] #[a, b, c, d, e, f, g, 0] R 6 g rfl (by decide) rfl,
    set_mid pre #[a, b, c, d, e, f, g, 0] #[a, b, c, d, e, f, g, h] R 7 h rfl (by decide) rfl]

/-- One long word written behind pre, where zeros stood. -/
theorem store64_append (pre : Array UInt8) (k off : Nat) (w : UInt64) (h : pre.size = off) :
    Spec.store64 (pre ++ Array.replicate (k + 8) 0) off w =
      pre ++ long8 w ++ Array.replicate k 0 := by
  subst h
  have r : Array.replicate (k + 8) (0 : UInt8) =
      #[0, 0, 0, 0, 0, 0, 0, 0] ++ Array.replicate k 0 := by
    rw [Nat.add_comm]
    exact Array.replicate_append_replicate.symm
  rw [store64_eq, r, write8]
  exact Array.append_assoc.symm

/-- The eight calls of Spec.store64 in Spec.blake2b_final write the 64 bytes of the chaining value
(ChainingValue.bytes64). -/
theorem store_eq (s : ChainingValue) :
    (List.range 8).foldl (fun (buffer : Array UInt8) i => Spec.store64 buffer (8 * i) s.arr[i]!)
      (Array.replicate 64 0) = s.bytes64.data := by
  have g0 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[0]! = s.h0 := rfl
  have g1 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[1]! = s.h1 := rfl
  have g2 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[2]! = s.h2 := rfl
  have g3 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[3]! = s.h3 := rfl
  have g4 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[4]! = s.h4 := rfl
  have g5 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[5]! = s.h5 := rfl
  have g6 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[6]! = s.h6 := rfl
  have g7 : (#[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7] : Array UInt64)[7]! = s.h7 := rfl
  have e : (ByteArray.emptyWithCapacity 64).data = #[] := rfl
  have z : Array.replicate 64 (0 : UInt8) = #[] ++ Array.replicate (56 + 8) 0 :=
    Array.empty_append.symm
  have n8 : ∀ x : UInt64, (long8 x).size = 8 := fun _ => rfl
  have q0 : (#[] : Array UInt8).size = 0 := rfl
  have q1 : (#[] ++ long8 s.h0 : Array UInt8).size = 8 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  have q2 : (#[] ++ long8 s.h0 ++ long8 s.h1 : Array UInt8).size = 16 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  have q3 : (#[] ++ long8 s.h0 ++ long8 s.h1 ++ long8 s.h2 : Array UInt8).size = 24 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  have q4 : (#[] ++ long8 s.h0 ++ long8 s.h1 ++ long8 s.h2 ++
      long8 s.h3 : Array UInt8).size = 32 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  have q5 : (#[] ++ long8 s.h0 ++ long8 s.h1 ++ long8 s.h2 ++ long8 s.h3 ++
      long8 s.h4 : Array UInt8).size = 40 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  have q6 : (#[] ++ long8 s.h0 ++ long8 s.h1 ++ long8 s.h2 ++ long8 s.h3 ++
      long8 s.h4 ++ long8 s.h5 : Array UInt8).size = 48 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  have q7 : (#[] ++ long8 s.h0 ++ long8 s.h1 ++ long8 s.h2 ++ long8 s.h3 ++
      long8 s.h4 ++ long8 s.h5 ++ long8 s.h6 : Array UInt8).size = 56 := by
    simp only [Array.size_append, Array.size_empty, n8, Nat.reduceAdd]
  unfold ChainingValue.bytes64 ChainingValue.arr
  simp only [data_store64, range8, List.foldl, g0, g1, g2, g3, g4, g5, g6, g7, Nat.reduceMul]
  rw [e, z, store64_append _ 56 _ _ q0, store64_append _ 48 _ _ q1, store64_append _ 40 _ _ q2,
    store64_append _ 32 _ _ q3, store64_append _ 24 _ _ q4, store64_append _ 16 _ _ q5,
    store64_append _ 8 _ _ q6, store64_append _ 0 _ _ q7]
  exact Array.append_empty

end Run.Blake2b
