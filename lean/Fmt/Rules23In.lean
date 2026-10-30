-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules23In.lean: the realised oracle as one call of BLAKE2b on every string; and: the map from
the oracle's strings to BLAKE2b's inputs is one to one on all strings, but for the two halves of one
call under the number 162.

Definitions that compute, theorems, proofs, tests (#guard). No Mathlib.
Sections 2 and 3 of the format page (docs/format/FORMAT.md, which comes with the programs): written
in an edition that is not the one that ships, not held against the page that ships; no definition,
statement or proof of this file differs between that edition and a second one, also not the one that
ships, which Fmt/Rules23.lean renders;
the ruling on the reserved number 177 is this library's own.

From Fmt/Rules23.lean: a call of the format's hash `formatHash` (BLAKE2b at a parameter block `pblock`, of a
`label` and then the bytes) is encoded as one string (`oStr`), a query to a single oracle with
answers of 32 bytes; its first byte, the half, says which 32 bytes of the digest are asked for. The
image (`inImage`) is the set of the strings that a hash of the format asks.

Why: the format has one oracle on all byte strings, taken for a random function. Fmt/Rules23.lean
realises it: in the format's image by the hash of the format, outside by the hash under the reserved
number 177 of the whole string. If two different strings led to the same call of BLAKE2b, their
answers would be tied, which no random function's are. Here: they do not, with the one exception
that the page itself rules (R2.4): a hash of 64 bytes counts as two queries, its two halves.

Main names:
  `bIn x`: (parameter block, message): in the image: the block and "label, bytes" of the hash;
    outside: the block of the number 177 without a start, and "the label of 177, then all of x".
  `bOf p`: BLAKE2b at a block and a message (digest length, salt, personalization read off the
    block).
  `hOf x`, `oracle_bIn`, `bIn_hOf_inj`, `bIn_inj`.
  `append_cancel`, `label_inj`, `pblock_start`, `isNumber_ne`: what the proof of `bIn_inj` uses: two
    strings with equally long first parts; a label fixes number, tree, index (below 2^16, 2^48,
    2^64); a block fixes the start (of 32 bytes); 177 is not given out.

Limits: this file does not say that BLAKE2b behaves as a random function of (block, message), or
that the two halves of a digest of 64 bytes are independent: the instance's assumption.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules23Laws

set_option autoImplicit false

namespace Fmt

/-- BLAKE2b's input for a string of the oracle: parameter block and message. -/
def bIn (x : ByteArray) : ByteArray × ByteArray :=
  match oParse x with
  | none => (pblock reserved zero32, label reserved 0 0 ++ x)
  | some q =>
    if oUsed q then (pblock q.number q.start, label q.number q.tree q.index ++ q.bytes)
    else (pblock reserved zero32, label reserved 0 0 ++ x)

/-- BLAKE2b at a block and a message -/
def bOf (p : ByteArray × ByteArray) : ByteArray :=
  blake2b (byteAt p.1 0).toNat (p.1.extract 32 48) (p.1.extract 48 64) p.2

/-- which half of the digest is the answer -/
def hOf (x : ByteArray) : Nat := if inImage x then (byteAt x 0).toNat else 0

theorem append_cancel (a b a' b' : ByteArray) (hs : a.size = a'.size) (e : a ++ b = a' ++ b') :
    a = a' ∧ b = b' := by
  have h1 := extract_mid ByteArray.empty a b
  have h2 := extract_mid ByteArray.empty a' b'
  rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h1 h2
  have h3 := extract_mid a b ByteArray.empty
  have h4 := extract_mid a' b' ByteArray.empty
  rw [ByteArray.append_empty] at h3 h4
  have hb : b.size = b'.size := by
    have := congrArg ByteArray.size e
    rw [ByteArray.size_append, ByteArray.size_append] at this
    omega
  constructor
  · rw [← h1, ← h2, e, hs]
  · rw [← h3, ← h4, e, hs, hb]

theorem label_inj (n t i n' t' i' : Nat) (hn : n < 65536) (hn' : n' < 65536) (ht : t < 2 ^ 48)
    (ht' : t' < 2 ^ 48) (hi : i < 2 ^ 64) (hi' : i' < 2 ^ 64) (e : label n t i = label n' t' i') :
    n = n' ∧ t = t' ∧ i = i' := by
  have h0 := label_w0 n t i (by omega)
  have h0' := label_w0 n' t' i' (by omega)
  have h1 := label_w1 n t i hi
  have h1' := label_w1 n' t' i' hi'
  rw [e] at h0 h1
  rw [h0] at h0'
  rw [h1] at h1'
  omega

theorem pblock_start (n : Nat) (s : ByteArray) (hs : s.size = 32) :
    (pblock n s).extract 32 64 = s := by
  have h1 := extract_mid (⟨#[UInt8.ofNat (dlen n), 0, 1, 1]⟩ ++ zeroBytes 28) s ByteArray.empty
  rw [ByteArray.append_empty, ByteArray.size_append, size_four, size_zeros, hs] at h1
  unfold pblock
  rw [fit_self 32 s hs]
  exact h1

theorem isNumber_ne (n : Nat) (h : isNumber n = true) : n ≠ 177 := by
  simp [isNumber, numbers] at h
  omega

theorem bIn_in (h : UInt8) (n t i : Nat) (s b : ByteArray)
    (hd : hDom n t i s b = true) (hh : h = 0 ∨ (h = 1 ∧ n = 162)) :
    bIn (oStr h n t i s b) = (pblock n s, label n t i ++ b) := by
  unfold bIn
  rw [oParse_oStr h n t i s b (hh.elim Or.inl fun a => Or.inr a.1) hd]
  have hu : oUsed ⟨h, n, t, i, s, b⟩ = true := by
    simp only [oUsed, Bool.or_eq_true, beq_iff_eq]
    exact hh.elim Or.inl fun a => Or.inr a.2
  simp only [hu, if_true]

theorem bIn_out (x : ByteArray) (hx : inImage x = false) :
    bIn x = (pblock reserved zero32, label reserved 0 0 ++ x) := by
  unfold inImage at hx
  unfold bIn
  rcases hq : oParse x with _ | q
  · rfl
  · rw [hq] at hx
    simp only [Option.any_some] at hx
    simp [hx]

/-- One to one on all strings, but for the two halves under 162. -/
theorem bIn_inj (x y : ByteArray) (e : bIn x = bIn y) :
    x = y ∨ ∃ (t i : Nat) (s b : ByteArray),
      hDom 162 t i s b = true ∧
      ((x = oStr 0 162 t i s b ∧ y = oStr 1 162 t i s b) ∨
        (x = oStr 1 162 t i s b ∧ y = oStr 0 162 t i s b)) := by
  by_cases hx : inImage x = true
  · obtain ⟨h, n, t, i, s, b, hd, hh, rfl⟩ := (inImage_iff x).1 hx
    obtain ⟨hn, ht, hi, hs⟩ := hDom_spec n t i s b hd
    rw [bIn_in h n t i s b hd hh] at e
    by_cases hy : inImage y = true
    · obtain ⟨h', n', t', i', s', b', hd', hh', rfl⟩ := (inImage_iff y).1 hy
      obtain ⟨hn', ht', hi', hs'⟩ := hDom_spec n' t' i' s' b' hd'
      rw [bIn_in h' n' t' i' s' b' hd' hh'] at e
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, rfl⟩ := append_cancel _ _ _ _ (by rw [size_label, size_label]) e2
      obtain ⟨rfl, rfl, rfl⟩ := label_inj
        n t i n' t' i' (isNumber_lt n hn) (isNumber_lt n' hn') ht ht' (by omega) (by omega) e3
      have es : s = s' := by rw [← pblock_start n s hs, ← pblock_start n s' hs', e1]
      subst es
      rcases hh with rfl | ⟨rfl, rfl⟩
      · rcases hh' with rfl | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨t, i, s, b, hd, Or.inl ⟨rfl, rfl⟩⟩
      · rcases hh' with rfl | ⟨rfl, -⟩
        · exact Or.inr ⟨t, i, s, b, hd, Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inl rfl
    · rw [bIn_out y (by simpa using hy)] at e
      obtain ⟨-, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, -⟩ := append_cancel _ _ _ _ (by rw [size_label, size_label]) e2
      obtain ⟨e4, -, -⟩ := label_inj n t i reserved 0 0 (isNumber_lt n hn)
        (by unfold reserved; omega) ht (by omega) (by omega) (by omega) e3
      exact absurd e4 (isNumber_ne n hn)
  · rw [bIn_out x (by simpa using hx)] at e
    by_cases hy : inImage y = true
    · obtain ⟨h', n', t', i', s', b', hd', hh', rfl⟩ := (inImage_iff y).1 hy
      obtain ⟨hn', ht', hi', hs'⟩ := hDom_spec n' t' i' s' b' hd'
      rw [bIn_in h' n' t' i' s' b' hd' hh'] at e
      obtain ⟨-, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, -⟩ := append_cancel _ _ _ _ (by rw [size_label, size_label]) e2
      obtain ⟨e4, -, -⟩ := label_inj reserved 0 0 n' t' i' (by unfold reserved; omega)
        (isNumber_lt n' hn') (by omega) ht' (by omega) (by omega) e3
      exact absurd e4.symm (isNumber_ne n' hn')
    · rw [bIn_out y (by simpa using hy)] at e
      obtain ⟨-, e2⟩ := Prod.mk.inj e
      exact Or.inl (append_cancel _ _ _ _ rfl e2).2

theorem extract_extract' (a : ByteArray) (i j k l : Nat) (h : i + l ≤ j) :
    (a.extract i j).extract k l = a.extract (i + k) (i + l) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_extract,
    Array.extract_extract, Nat.min_eq_left h]

theorem pblock_head (n : Nat) (s : ByteArray) : (byteAt (pblock n s) 0).toNat = dlen n := by
  have h1 := byteAt_mid ByteArray.empty ⟨#[UInt8.ofNat (dlen n), 0, 1, 1]⟩
    (zeroBytes 28 ++ fit 32 s) 0 (by rw [size_four]; omega)
  rw [ByteArray.empty_append, ByteArray.size_empty] at h1
  unfold pblock
  rw [ByteArray.append_assoc]
  rw [show (0 : Nat) + 0 = 0 from rfl] at h1
  rw [h1]
  unfold dlen
  split <;> rfl

/-- the hash of the format, at a start of 32 bytes, is BLAKE2b at its block and "label, bytes" -/
theorem H_eq_bOf (n t i : Nat) (s b : ByteArray) (hs : s.size = 32) :
    formatHash n t i s b = bOf (pblock n s, label n t i ++ b) := by
  unfold formatHash bOf
  simp only
  rw [pblock_head, fit_self 32 s hs]
  have e := pblock_start n s hs
  have e1 : (pblock n s).extract 32 48 = s.extract 0 16 := by
    have h1 := extract_extract' (pblock n s) 32 64 0 16 (by omega)
    rw [e] at h1
    exact h1.symm
  have e2 : (pblock n s).extract 48 64 = s.extract 16 32 := by
    have h1 := extract_extract' (pblock n s) 32 64 16 32 (by omega)
    rw [e] at h1
    exact h1.symm
  rw [e1, e2]

theorem hOf_in (h : UInt8) (n t i : Nat) (s b : ByteArray)
    (hd : hDom n t i s b = true) (hh : h = 0 ∨ (h = 1 ∧ n = 162)) :
    hOf (oStr h n t i s b) = h.toNat := by
  unfold hOf
  rw [if_pos ((inImage_iff _).2 ⟨h, n, t, i, s, b, hd, hh, rfl⟩), oStr_head]

theorem hOf_out (x : ByteArray) (hx : inImage x = false) : hOf x = 0 := by
  unfold hOf
  simp [hx]

/-- Every answer of the realised oracle is 32 bytes of one call of BLAKE2b. -/
theorem oracle_bIn (x : ByteArray) :
    oracle x = (bOf (bIn x)).extract (32 * hOf x) (32 * hOf x + 32) := by
  by_cases hx : inImage x = true
  · obtain ⟨h, n, t, i, s, b, hd, hh, rfl⟩ := (inImage_iff x).1 hx
    obtain ⟨-, -, -, hs⟩ := hDom_spec n t i s b hd
    rw [bIn_in h n t i s b hd hh, hOf_in h n t i s b hd hh, ← H_eq_bOf n t i s b hs]
    rcases hh with rfl | ⟨rfl, rfl⟩
    · exact oracle_in0 n t i s b hd
    · exact oracle_in1 t i s b hd
  · have hx' : inImage x = false := by simpa using hx
    have hz : (formatHash 177 0 0 zero32 x).size = 32 := size_H 177 0 0 zero32 x
    rw [bIn_out x hx', hOf_out x hx', oracle_out x hx']
    show formatHash 177 0 0 zero32 x = (bOf (pblock 177 zero32, label 177 0 0 ++ x)).extract 0 32
    rw [← H_eq_bOf 177 0 0 zero32 x rfl, ← hz, ByteArray.extract_zero_size]

/-- so input and half together are one to one on all strings -/
theorem bIn_hOf_inj (x y : ByteArray) (e : bIn x = bIn y) (eh : hOf x = hOf y) : x = y := by
  rcases bIn_inj x y e with h | ⟨t, i, s, b, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h
  · rw [hOf_in 0 162 t i s b hd (Or.inl rfl), hOf_in 1 162 t i s b hd (Or.inr ⟨rfl, rfl⟩)] at eh
    exact absurd eh (by decide)
  · rw [hOf_in 0 162 t i s b hd (Or.inl rfl), hOf_in 1 162 t i s b hd (Or.inr ⟨rfl, rfl⟩)] at eh
    exact absurd eh (by decide)

/-! ### Tests -/

#guard (bIn (oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))).1 = pblock 164 (pattern 32) && (bIn (oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))).2 = label 164 (leafPlace 9 3 5) 12 ++ pattern 64
#guard bIn (oStr 0 162 7 3 (pattern 32) (pattern 16)) = bIn (oStr 1 162 7 3 (pattern 32) (pattern 16)) && hOf (oStr 0 162 7 3 (pattern 32) (pattern 16)) = 0 && hOf (oStr 1 162 7 3 (pattern 32) (pattern 16)) = 1
#guard (bIn (pattern 7)).2 = label 177 0 0 ++ pattern 7 && (bIn (oStr 1 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))).2 = label 177 0 0 ++ oStr 1 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)
#guard [ByteArray.empty, pattern 7, pattern 200, oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64), oStr 0 162 7 3 (pattern 32) (pattern 16), oStr 1 162 7 3 (pattern 32) (pattern 16), oStr 0 166 0 0 (pattern 32) (pattern 64),
  oStr 0 177 0 0 zero32 ByteArray.empty, oStr 2 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)].all fun x => oracle x = (bOf (bIn x)).extract (32 * hOf x) (32 * hOf x + 32)

end Fmt
