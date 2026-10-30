-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules23Laws.lean: the format's hash and the single oracle, the laws for all inputs.
It proves these laws, each under the hypotheses of its statement:
  `oParse_oStr`, `oStr_oParse`: `oParse` reads the oracle's strings back, and only them.
  `oStr_inj`: so the oracle's strings are one to one.
  `inImage_iff`: `inImage` decides the image exactly.
  `HO_oracle`: on the domain the hash over the realised oracle (`HO oracle`) is the direct call of
    BLAKE2b (`formatHash`).
The third paragraph defines these terms.

Theorems and proofs. No Mathlib.
Sections 2 and 3 of the format page (docs/format/FORMAT.md, which comes with the programs): written
at an edition that is not the one that ships, and not held against the page that ships;
Fmt/Rules23.lean renders another edition, which is not that page's either.
Fmt/Rules23.lean has the definitions, with tests (#guard) at values; Fmt/Rules23Known.lean the
page's known answers as theorems.

`formatHash number tree index start bytes` is BLAKE2b of a label of 16 bytes and then the bytes.
  The label's first word is the number (which use) + 2^16 times what stands in the tree's place.
  The label's second word is the index.
  The start, 32 bytes, goes into BLAKE2b's parameter block.
`hDom` decides the domain: the calls that the hash admits.
`oStr half number tree index start bytes` encodes a call as one string, a query to a single oracle
  with answers of 32 bytes. The half (0 or 1) says which 32 bytes of the digest are asked for.
`oParse` decodes such a string.
`inImage` decides the image (the strings that a hash of the format asks).
`oracle` is that oracle computed by BLAKE2b on all strings.
`HO O` is the hash put together from the answers of an oracle O.
Under a leaf's number `leafPlace tree W s8` stands in the tree's place: the tree's number with the
  leaf's shape W, s8. W counts the words of the leaf's content.

Why: the proofs of `leafOK_other` and `hDom_leaf` unfold `leafOK`. Those of `isNumber_lt`,
`treeBound_le`, `idxOK_lt` and `hDom_spec` unfold `numbers`, `treeBound`, `idxOK` and `hDom`. The
other proofs read, of the table of numbers (R3.1) and of the bounds (R2.3), these facts alone:
  a number that is given out lies below 2^16;
  what stands in the tree's place lies below 2^48;
  the index lies below 2^63;
  a start has 32 bytes (`hDom_spec`).
So these proofs stand when a row of the table changes what it takes
(a start, a tree, a named index).






On a leaf's shape in its label: `placeTree_leafPlace`,
`placeW_leafPlace`, `placeS_leafPlace`, `leafPlace_lt`,
`leafPlace_place`, `leafPlace_inj`, `leafOK_other`, `hDom_leaf` and `leafStr_inj`.
`leafPlace_inj` says: one place, one shape, for a tree's number below 2^16 and W below 2^24.
`leafStr_inj` says that for halves 0, 1, on the domain, within these two bounds, the map from
(half, number, tree, W, s8, index, start, bytes) to strings is one to one.

Main names:
  `size_label`: a label has 16 bytes.
  `size_pblock`: for a start of 32 bytes, the parameter block has 64 bytes.
  `size_oStr`: for a start of 32 bytes, the string of a call has 81 bytes and the call's bytes.
  `size_H`: formatHash returns as many bytes as the digest length.
  `size_oracle`: every answer of the oracle has 32 bytes.
  `oParse_oStr`: for a half 0 or 1 and (number, tree, index, start, bytes) in the domain (R2.3): the
    string is read back as these six.
  `oStr_oParse`: if `oParse` reads a string back, then that string is `oStr` of what `oParse`
    returns, the half is 0 or 1, and the five others lie in the domain.
  `oStr_inj`: R2.4's "one to one": on halves 0, 1 and the domain.
  `inImage_iff`: the image: exactly the strings of the domain with the half 0, or with the half 1
    under the number 162.
  `oracle_in0`, `oracle_in1`, `oracle_out`: the oracle in the image is bytes 0 to 31 of formatHash; under 162
    at the half 1, bytes 32 to 63; outside, formatHash under the reserved number 177 (R2.5), tree 0, index 0,
    no start (`zero32`: 32 zero bytes), of the whole string.
  `HO_oracle` (the tie): on the domain `HO oracle` = `formatHash`.

Notation: 162, 174, 179: entries of `numbers` (Fmt/Rules23.lean); 162: the number of a call of a
round's query; 174: one of the three numbers of leaves (`isLeaf`); 179: the number of the
commitment ID.

Limits: this file does not say that BLAKE2b behaves as a random function. It says nothing on formatHash
outside its domain, but for its length (`size_H`) and for `oracle_out`, where formatHash stands under the
number 177. It says nothing on bits against bytes (a file of Run/: Run/OracleBits.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules23
import Fmt.Rules1Laws
import Fmt.Rules1Only
import Fmt.Blake2bLaws

set_option autoImplicit false

namespace Fmt

theorem size_zeros (n : Nat) : (zeroBytes n).size = n := by
  simp [zeroBytes, ByteArray.size]

theorem fit_self (n : Nat) (b : ByteArray) (h : b.size = n) : fit n b = b := by
  subst h
  unfold fit
  rw [if_pos (Nat.le_refl _)]
  apply ByteArray.ext
  rw [ByteArray.data_extract, ← ByteArray.size_data, Array.extract_size]

theorem size_u64n (x : Nat) : (u64n x).size = 8 := rfl

theorem size_label (n t i : Nat) : (label n t i).size = 16 := by
  unfold label
  rw [ByteArray.size_append, size_u64n, size_u64n]

theorem size_one (h : UInt8) : (⟨#[h]⟩ : ByteArray).size = 1 := rfl
theorem size_four (a b c d : UInt8) : (⟨#[a, b, c, d]⟩ : ByteArray).size = 4 := rfl

theorem size_pblock (n : Nat) (s : ByteArray) (hs : s.size = 32) : (pblock n s).size = 64 := by
  unfold pblock
  rw [ByteArray.size_append, ByteArray.size_append, size_four, size_zeros, fit_self 32 s hs, hs]

theorem wordAt_u64n (x : Nat) (hx : x < 2 ^ 64) : (wordAt (u64n x) 0).toNat = x := by
  unfold u64n
  rw [wordAt_u64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hx

theorem label_w0 (n t i : Nat) (h : n + 65536 * t < 2 ^ 64) :
    (wordAt (label n t i) 0).toNat = n + 65536 * t := by
  have h1 := wordAt_mid ByteArray.empty (u64n (n + 65536 * t)) (u64n i) 0 (by rw [size_u64n]; omega)
  rw [ByteArray.empty_append, ByteArray.size_empty] at h1
  unfold label
  rw [h1, wordAt_u64n _ h]

theorem label_w1 (n t i : Nat) (h : i < 2 ^ 64) : (wordAt (label n t i) 8).toNat = i := by
  have h1 := wordAt_mid (u64n (n + 65536 * t)) (u64n i) ByteArray.empty 0 (by rw [size_u64n]; omega)
  rw [ByteArray.append_empty, size_u64n] at h1
  unfold label
  rw [h1, wordAt_u64n _ h]

theorem isNumber_lt (n : Nat) (h : isNumber n = true) : n < 65536 := by
  simp [isNumber, numbers] at h
  omega

theorem treeBound_le (n : Nat) : treeBound n ≤ 2 ^ 48 := by
  unfold treeBound
  split <;> omega

theorem idxOK_lt (n i : Nat) (h : idxOK n i = true) : i < 2 ^ 63 := by
  simp only [idxOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem hDom_spec (n t i : Nat) (s b : ByteArray) (h : hDom n t i s b = true) :
    isNumber n = true ∧ t < 2 ^ 48 ∧ i < 2 ^ 63 ∧ s.size = 32 := by
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, Nat.lt_of_lt_of_le h.1.1.1.1.1.1.2 (treeBound_le n),
    idxOK_lt n i h.1.1.1.1.2, h.1.1.2⟩

/-! ### A leaf's place -/

theorem placeTree_leafPlace (tree W s8 : Nat) (h : tree < 2 ^ 16) :
    placeTree (leafPlace tree W s8) = tree := by
  unfold placeTree leafPlace
  omega

theorem placeW_leafPlace (tree W s8 : Nat) (h : tree < 2 ^ 16) (hW : W < 2 ^ 24) :
    placeW (leafPlace tree W s8) = W := by
  unfold placeW leafPlace
  omega

theorem placeS_leafPlace (tree W s8 : Nat) (h : tree < 2 ^ 16) (hW : W < 2 ^ 24) :
    placeS (leafPlace tree W s8) = s8 := by
  unfold placeS leafPlace
  omega

theorem leafPlace_lt (tree W s8 : Nat) (h : tree < 2 ^ 16) (hW : W < 2 ^ 24) (hs : s8 < 2 ^ 8) :
    leafPlace tree W s8 < 2 ^ 48 := by
  unfold leafPlace
  omega

/-- a place is put together from what is read off it -/
theorem leafPlace_place (t : Nat) : leafPlace (placeTree t) (placeW t) (placeS t) = t := by
  unfold leafPlace placeTree placeW placeS
  omega

/-- One place, one shape: for trees' numbers below 2^16 and W, W' below 2^24. -/
theorem leafPlace_inj (tree W s8 tree' W' s8' : Nat) (h : tree < 2 ^ 16) (hW : W < 2 ^ 24)
    (h' : tree' < 2 ^ 16) (hW' : W' < 2 ^ 24) (e : leafPlace tree W s8 = leafPlace tree' W' s8') :
    tree = tree' ∧ W = W' ∧ s8 = s8' := by
  unfold leafPlace at e
  omega

/-- under a number that is no leaf's, `leafOK` asks nothing -/
theorem leafOK_other (n t : Nat) (b : ByteArray) (h : isLeaf n = false) : leafOK n t b = true := by
  unfold leafOK
  rw [h]
  rfl

/-- Part of what the domain says of a leaf: the bounds on its shape and the length of its bytes. -/
theorem hDom_leaf (n t i : Nat) (s b : ByteArray)
    (h : hDom n t i s b = true) (hl : isLeaf n = true) :
    1 ≤ placeW t ∧ 5 ≤ placeS t ∧ placeS t ≤ 8 ∧
    b.size = 8 * placeW t + leafFill (placeW t) (8 * placeS t) + 8 * placeS t := by
  simp only [hDom, Bool.and_eq_true] at h
  have h1 := h.2
  unfold leafOK at h1
  rw [hl] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  exact ⟨h1.1.1.1.1.1, h1.1.1.1.1.2, h1.1.1.1.2, h1.1.2⟩

section
variable (h : UInt8) (n t i : Nat) (s b : ByteArray)

theorem size_oStr (hs : s.size = 32) : (oStr h n t i s b).size = 81 + b.size := by
  unfold oStr
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, size_one,
    size_pblock n s hs, size_label]

/-- the first byte is the half -/
theorem oStr_head : byteAt (oStr h n t i s b) 0 = h := by
  have h1 :=
    byteAt_mid ByteArray.empty ⟨#[h]⟩ (pblock n s ++ label n t i ++ b) 0 (by rw [size_one]; omega)
  rw [ByteArray.empty_append, ByteArray.size_empty] at h1
  unfold oStr
  simp only [ByteArray.append_assoc] at h1 ⊢
  exact h1

theorem oStr_w0 (hs : s.size = 32) : wordAt (oStr h n t i s b) 65 = wordAt (label n t i) 0 := by
  have h1 := wordAt_mid (⟨#[h]⟩ ++ pblock n s) (label n t i) b 0 (by rw [size_label]; omega)
  rw [ByteArray.size_append, size_one, size_pblock n s hs] at h1
  exact h1

theorem oStr_w1 (hs : s.size = 32) : wordAt (oStr h n t i s b) 73 = wordAt (label n t i) 8 := by
  have h1 := wordAt_mid (⟨#[h]⟩ ++ pblock n s) (label n t i) b 8 (by rw [size_label]; omega)
  rw [ByteArray.size_append, size_one, size_pblock n s hs] at h1
  exact h1

theorem oStr_block (hs : s.size = 32) : (oStr h n t i s b).extract 1 65 = pblock n s := by
  have h1 := extract_mid ⟨#[h]⟩ (pblock n s) (label n t i ++ b)
  rw [size_one, size_pblock n s hs] at h1
  unfold oStr
  rw [ByteArray.append_assoc]
  exact h1

theorem oStr_start (hs : s.size = 32) : (oStr h n t i s b).extract 33 65 = s := by
  have h1 :=
    extract_mid (⟨#[h]⟩ ++ ⟨#[UInt8.ofNat (dlen n), 0, 1, 1]⟩ ++ zeroBytes 28) s (label n t i ++ b)
  rw [ByteArray.size_append, ByteArray.size_append, size_one, size_four, size_zeros, hs] at h1
  unfold oStr pblock
  rw [fit_self 32 s hs]
  simp only [ByteArray.append_assoc] at h1 ⊢
  exact h1

theorem oStr_bytes (hs : s.size = 32) :
    (oStr h n t i s b).extract 81 (oStr h n t i s b).size = b := by
  have h1 := extract_mid (⟨#[h]⟩ ++ pblock n s ++ label n t i) b ByteArray.empty
  rw [ByteArray.append_empty, ByteArray.size_append, ByteArray.size_append, size_one,
    size_pblock n s hs, size_label] at h1
  rw [size_oStr h n t i s b hs]
  exact h1

/-- A string of the domain, with the half 0 or 1, is read back. -/
theorem oParse_oStr (hh : h = 0 ∨ h = 1) (hd : hDom n t i s b = true) :
    oParse (oStr h n t i s b) = some ⟨h, n, t, i, s, b⟩ := by
  obtain ⟨hn, ht, hi, hs⟩ := hDom_spec n t i s b hd
  have hn' := isNumber_lt n hn
  have e0 : (wordAt (oStr h n t i s b) 65).toNat = n + 65536 * t := by
    rw [oStr_w0 h n t i s b hs, label_w0 n t i (by omega)]
  have e1 : (wordAt (oStr h n t i s b) 73).toNat = i := by
    rw [oStr_w1 h n t i s b hs, label_w1 n t i (by omega)]
  have em : (n + 65536 * t) % 65536 = n := by omega
  have ed : (n + 65536 * t) / 65536 = t := by omega
  unfold oParse
  rw [if_neg (by rw [size_oStr h n t i s b hs]; omega)]
  simp only [oStr_head, e0, e1, em, ed, oStr_start h n t i s b hs, oStr_bytes h n t i s b hs,
    oStr_block h n t i s b hs, hd]
  rcases hh with rfl | rfl <;> simp

end

theorem extract_one (x : ByteArray) (h : 1 ≤ x.size) : x.extract 0 1 = ⟨#[byteAt x 0]⟩ := by
  have hs : x.data.size = x.size := ByteArray.size_data
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext
  · rw [Array.size_extract]
    simp
    omega
  · intro k h1 h2
    rw [Array.getElem_extract]
    have hk : k = 0 := by
      simp at h2
      omega
    subst hk
    simp [byteAt_in x 0 (by omega)]

theorem label_of_words (x : ByteArray) (h : 81 ≤ x.size) :
    label ((wordAt x 65).toNat % 65536) ((wordAt x 65).toNat / 65536) (wordAt x 73).toNat =
      x.extract 65 81 := by
  have e : (wordAt x 65).toNat % 65536 + 65536 * ((wordAt x 65).toNat / 65536) =
      (wordAt x 65).toNat :=
    Nat.mod_add_div _ _
  unfold label u64n
  rw [e, UInt64.ofNat_toNat, UInt64.ofNat_toNat,
    u64_wordAt x 65 (by omega), u64_wordAt x 73 (by omega)]
  show x.extract 65 73 ++ x.extract 73 81 = x.extract 65 81
  rw [← ByteArray.extract_eq_extract_append_extract 73 (by omega) (by omega)]

/-- What is read back is the string of what is returned. -/
theorem oStr_oParse (x : ByteArray) (q : OQ) (h : oParse x = some q) :
    x = oStr q.half q.number q.tree q.index q.start q.bytes ∧
    (q.half = 0 ∨ q.half = 1) ∧
    hDom q.number q.tree q.index q.start q.bytes = true := by
  unfold oParse at h
  by_cases hz : x.size < 81
  · rw [if_pos hz] at h
    exact absurd h (by simp)
  · rw [if_neg hz] at h
    simp only at h
    split at h
    · rename_i hc
      have hq := Option.some.inj h
      subst hq
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hh, hd⟩, hb⟩ := hc
      refine ⟨?_, hh, hd⟩
      have hb' : x.extract 1 65 = pblock ((wordAt x 65).toNat % 65536) (x.extract 33 65) :=
        ByteArray.ext hb
      unfold oStr
      simp only
      rw [← hb', label_of_words x (by omega), ← extract_one x (by omega),
        ← ByteArray.extract_eq_extract_append_extract 1 (by omega) (by omega),
        ← ByteArray.extract_eq_extract_append_extract 65 (by omega) (by omega),
        ← ByteArray.extract_eq_extract_append_extract 81 (by omega) (by omega),
        ByteArray.extract_zero_size]
    · exact absurd h (by simp)

/-- The strings are one to one on the domain, for halves 0, 1. -/
theorem oStr_inj (h h' : UInt8) (n n' t t' i i' : Nat) (s s' b b' : ByteArray) (hh : h = 0 ∨ h = 1)
    (hh' : h' = 0 ∨ h' = 1) (hd : hDom n t i s b = true) (hd' : hDom n' t' i' s' b' = true)
    (e : oStr h n t i s b = oStr h' n' t' i' s' b') :
    h = h' ∧ n = n' ∧ t = t' ∧ i = i' ∧ s = s' ∧ b = b' := by
  have h1 := oParse_oStr h n t i s b hh hd
  rw [e, oParse_oStr h' n' t' i' s' b' hh' hd'] at h1
  have h2 := Option.some.inj h1
  injection h2 with a1 a2 a3 a4 a5 a6
  exact ⟨a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm⟩

/-- A leaf's string holds its shape: for halves 0, 1, on the domain, for trees' numbers below 2^16
and contents below 2^24 words. -/
theorem leafStr_inj (h h' : UInt8) (n n' tree tree' W W' s8 s8' i i' : Nat) (s s' b b' : ByteArray)
    (hh : h = 0 ∨ h = 1) (hh' : h' = 0 ∨ h' = 1) (ht : tree < 2 ^ 16) (hW : W < 2 ^ 24)
    (ht' : tree' < 2 ^ 16) (hW' : W' < 2 ^ 24) (hd : hDom n (leafPlace tree W s8) i s b = true)
    (hd' : hDom n' (leafPlace tree' W' s8') i' s' b' = true)
    (e : oStr h n (leafPlace tree W s8) i s b = oStr h' n' (leafPlace tree' W' s8') i' s' b') :
    h = h' ∧ n = n' ∧ tree = tree' ∧ W = W' ∧ s8 = s8' ∧ i = i' ∧ s = s' ∧ b = b' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := oStr_inj h h' n n' _ _ i i' s s' b b' hh hh' hd hd' e
  obtain ⟨c1, c2, c3⟩ := leafPlace_inj tree W s8 tree' W' s8' ht hW ht' hW' a3
  exact ⟨a1, a2, c1, c2, c3, a4, a5, a6⟩

/-- The format's image, exactly. -/
theorem inImage_iff (x : ByteArray) :
    inImage x = true ↔
    ∃ (h : UInt8) (n t i : Nat) (s b : ByteArray),
      hDom n t i s b = true ∧ (h = 0 ∨ (h = 1 ∧ n = 162)) ∧ x = oStr h n t i s b := by
  constructor
  · intro hx
    unfold inImage at hx
    rcases hq : oParse x with _ | q
    · rw [hq] at hx
      exact absurd hx (by simp)
    · rw [hq] at hx
      obtain ⟨e, hh, hd⟩ := oStr_oParse x q hq
      simp only [Option.any_some, oUsed, Bool.or_eq_true, beq_iff_eq] at hx
      refine ⟨q.half, q.number, q.tree, q.index, q.start, q.bytes, hd, ?_, e⟩
      rcases hx with h0 | h2
      · exact Or.inl h0
      · rcases hh with h0 | h1
        · exact Or.inl h0
        · exact Or.inr ⟨h1, h2⟩
  · rintro ⟨h, n, t, i, s, b, hd, hh, rfl⟩
    unfold inImage
    rw [oParse_oStr h n t i s b (hh.elim Or.inl fun a => Or.inr a.1) hd]
    simp only [Option.any_some, oUsed, Bool.or_eq_true, beq_iff_eq]
    exact hh.elim Or.inl fun a => Or.inr a.2

/-- The oracle in the image: the first half; under the number 162 the second (`oracle_in1`). -/
theorem oracle_in0 (n t i : Nat) (s b : ByteArray) (hd : hDom n t i s b = true) :
    oracle (oStr 0 n t i s b) = (formatHash n t i s b).extract 0 32 := by
  unfold oracle
  rw [oParse_oStr 0 n t i s b (Or.inl rfl) hd]
  simp [oUsed]

theorem oracle_in1 (t i : Nat) (s b : ByteArray) (hd : hDom 162 t i s b = true) :
    oracle (oStr 1 162 t i s b) = (formatHash 162 t i s b).extract 32 64 := by
  unfold oracle
  rw [oParse_oStr 1 162 t i s b (Or.inr rfl) hd]
  simp [oUsed]

/-- The oracle outside the image: the hash under the reserved number, of the whole string. -/
theorem oracle_out (x : ByteArray) (hx : inImage x = false) : oracle x = formatHash 177 0 0 zero32 x := by
  unfold inImage at hx
  unfold oracle
  rcases hq : oParse x with _ | q
  · rfl
  · rw [hq] at hx
    simp only [Option.any_some] at hx
    simp only [hx]
    rfl

theorem size_H (n t i : Nat) (s b : ByteArray) : (formatHash n t i s b).size = dlen n := by
  unfold formatHash
  apply size_blake2b
  unfold dlen
  split <;> omega

/-- The tie: on the domain the hash over the realised oracle is the direct call. -/
theorem HO_oracle (n t i : Nat) (s b : ByteArray) (hd : hDom n t i s b = true) :
    HO oracle n t i s b = formatHash n t i s b := by
  unfold HO
  by_cases h2 : n = 162
  · subst h2
    have hz : (formatHash 162 t i s b).size = 64 := size_H 162 t i s b
    rw [if_pos rfl, oracle_in0 162 t i s b hd, oracle_in1 t i s b hd,
      ← ByteArray.extract_eq_extract_append_extract 32 (by omega) (by omega),
      ← hz, ByteArray.extract_zero_size]
  · have hz : (formatHash n t i s b).size = 32 := by
      rw [size_H, dlen, if_neg h2]
    rw [if_neg h2, oracle_in0 n t i s b hd, ← hz, ByteArray.extract_zero_size]

/-- every answer of the oracle has 32 bytes -/
theorem size_oracle (x : ByteArray) : (oracle x).size = 32 := by
  by_cases hx : inImage x = true
  · obtain ⟨h, n, t, i, s, b, hd, hh, rfl⟩ := (inImage_iff x).1 hx
    rcases hh with rfl | ⟨rfl, rfl⟩
    · rw [oracle_in0 n t i s b hd, ByteArray.size_extract, size_H]
      unfold dlen
      split <;> omega
    · rw [oracle_in1 t i s b hd, ByteArray.size_extract, size_H]
      rfl
  · rw [oracle_out x (by simpa using hx), size_H]
    rfl

end Fmt
