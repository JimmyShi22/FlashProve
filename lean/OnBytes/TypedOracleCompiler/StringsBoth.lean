-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsBoth.lean: one code of bodies that are strings for BOTH leaves' numbers: a
prover's own leaf (164) and a stored table's leaf (174).

The sibling's page takes one code of bodies whose strings begin with the 16
bits of 164 or of 174 (`PageC.leafTag`), a test on body and salt together (`PageC.leafOK`), and,
beside the page, three plain maps from a typed query to a call of the format (`CallsX`,
OnBytes/TypedOracleCompiler/Run/PageXAgree.lean). Its condition on leaves (`FitX.leaf`): what the page's code of
leaf queries writes is the bits of the string of the call that the map gives.

`rd2` reads a body: from its first 64 bits the number (the word's low 16 bits) and what stands above
it; from the next 64 the index; the rest as bytes. It computes and refuses nothing. `ok2` is the
test: a whole number of bytes, at least 16; the number is 164 or 174; and the body IS the bits of
the label and bytes that `rd2` reads from it. `call2` is the map: for a leaf query whose body
passes, the call under the number that was read, with the typed salt's first 256 bits as the start
and the rest behind the bytes; for any other, none.
 - `pBody2_tag`: the identity on the bodies that pass `ok2` meets the widened `leafTag`;
 - `pLeaf2_put`: what the sibling's code of leaf queries over it writes is the bits of the string of
   `call2`'s call, at salts of whole bytes;
 - `fitX_leaf`: so `FitX.leaf` holds at every page with this leaf code whose salts are whole bytes,
   and at all maps with this map of leaves, whatever the page's test `leafOK`;
 - `rd2_spell`, `ok2_spell`: the bits of a label under 164 or 174 and of bytes are read back and
   pass, if what stands above the number is below 2 ^ 48 and the index below 2 ^ 64;
 - `ok2_rd2_embTail`, `Stretches.ok2_rd2_embS`: a prover's symbol's body passes, and is read back
   with the number 164 and its leaf's spelling, under the conditions on the trees and the salt of
   OnBytes/TypedOracleCompiler/StringsBounds.lean.

Main definitions: `spell2`, `rd2`, `ok2`, `call2`.
Main theorems: `rd2_spell`, `ok2_spell`, `pBody2_tag`, `pLeaf2_put`, `fitX_leaf`,
`ok2_rd2_of_spell`, `ok2_rd2_embTail`, `Stretches.ok2_rd2_embS`.

Not claimed. No page and no maps are made: their other fields are given by nobody here, and of
`FitX` the clause on leaves alone is shown. No way of writing a stored symbol into a body is given
HERE: OnBytes/TypedOracleCompiler/StringsStoredAt.lean has one (`embX`), with what `rd2` reads from it, a test for
`leafOK` (`leafOK2`), and that a stored symbol's body and a body that begins with the 16 bits of 164
are apart. `ok2` passes every label under the two numbers with any bytes behind it, also outside the
domain of the format's hash, and under 174 also what is no stored symbol's body:
OnBytes/TypedOracleCompiler/StringsAt.lean has a narrower test (`okA`). With `pBody ok2` as its leaf code, and a
test that lets a query under 174 through, the sibling's `PageFit` is false whatever the spellings
(by hand): such a page goes by `FitX` alone. What ties `call2` to the sibling's `leafCall` is in
OnBytes/TypedOracleCompiler/StringsAt.lean (`call2_of_okRd`: under 164 alone).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsBounds
import OnBytes.TypedOracleCompiler.Run.PageXAgree

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open _root_.Run (t164 bytesToBits bitsToBytes length_bytesToBits bitsToBytes_bytesToBits
  bytesToBits_append length_u64n take16 pre33 oStr32_bits size_bitsToBytes bytesToBits_bitsToBytes
  whole_iff strOf)
open TypedOracleCompiler.Run (t174 tag_low)

/-- The bits of the label under the number n with two numbers, and of bytes. -/
def spell2 (n : ℕ) (z : ℕ × ℕ × ByteArray) : List Bool :=
  bytesToBits (_root_.Fmt.label n z.1 z.2.1) ++ bytesToBits z.2.2

/-- A body read: the number (the first word's low 16 bits); what stands above it; the second word;
the rest as bytes. -/
def rd2 (b : List Bool) : ℕ × ℕ × ℕ × ByteArray :=
  ((_root_.Fmt.wordAt (bitsToBytes (b.take 64)) 0).toNat % 65536,
    (_root_.Fmt.wordAt (bitsToBytes (b.take 64)) 0).toNat / 65536,
    (_root_.Fmt.wordAt (bitsToBytes ((b.drop 64).take 64)) 0).toNat,
    bitsToBytes (b.drop 128))

/-- From the bits of a label and of bytes `rd2` reads the number, the two numbers and the bytes,
if the number is below 2 ^ 16, what stands above it below 2 ^ 48, the index below 2 ^ 64. -/
theorem rd2_spell (n t i : ℕ) (z : ByteArray) (hn : n < 65536) (ht : t < 2 ^ 48)
    (hi : i < 2 ^ 64) : rd2 (spell2 n (t, i, z)) = (n, t, i, z) := by
  have e : spell2 n (t, i, z) =
      bytesToBits (_root_.Fmt.u64n (n + 65536 * t)) ++
        (bytesToBits (_root_.Fmt.u64n i) ++ bytesToBits z) := by
    unfold spell2 _root_.Fmt.label
    rw [bytesToBits_append, List.append_assoc]
  have h1 : (spell2 n (t, i, z)).take 64 = bytesToBits (_root_.Fmt.u64n (n + 65536 * t)) := by
    rw [e]
    exact List.take_left' (length_u64n _)
  have h2 : (spell2 n (t, i, z)).drop 64 = bytesToBits (_root_.Fmt.u64n i) ++ bytesToBits z := by
    rw [e]
    exact List.drop_left' (length_u64n _)
  have h3 : ((spell2 n (t, i, z)).drop 64).take 64 = bytesToBits (_root_.Fmt.u64n i) := by
    rw [h2]
    exact List.take_left' (length_u64n _)
  have h4 : (spell2 n (t, i, z)).drop 128 = bytesToBits z := by
    have : (spell2 n (t, i, z)).drop 128 = ((spell2 n (t, i, z)).drop 64).drop 64 := by
      rw [List.drop_drop]
    rw [this, h2]
    exact List.drop_left' (length_u64n _)
  have hw : n + 65536 * t < 2 ^ 64 := by omega
  unfold rd2
  rw [h1, h3, h4, bitsToBytes_bytesToBits, bitsToBytes_bytesToBits, bitsToBytes_bytesToBits,
    _root_.Fmt.wordAt_u64n _ hw, _root_.Fmt.wordAt_u64n _ hi]
  have a1 : (n + 65536 * t) % 65536 = n := by omega
  have a2 : (n + 65536 * t) / 65536 = t := by omega
  rw [a1, a2]

/-- The test: a whole number of bytes, at least 16; the number read is 164 or 174; the body is the
bits of what `rd2` reads from it. -/
def ok2 (b : List Bool) : Bool :=
  decide (b.length % 8 = 0) && decide (128 ≤ b.length) &&
    (decide ((rd2 b).1 = 164) || decide ((rd2 b).1 = 174)) &&
    decide (b = spell2 (rd2 b).1 (rd2 b).2)

theorem ok2_iff (b : List Bool) : ok2 b = true ↔
    (b.length % 8 = 0 ∧ 128 ≤ b.length) ∧ ((rd2 b).1 = 164 ∨ (rd2 b).1 = 174) ∧
      b = spell2 (rd2 b).1 (rd2 b).2 := by
  unfold ok2
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff, and_assoc]

/-- The bits of a label under 164 or 174 and of bytes pass `ok2`, within the two bounds. -/
theorem ok2_spell (n t i : ℕ) (z : ByteArray) (hn : n = 164 ∨ n = 174) (ht : t < 2 ^ 48)
    (hi : i < 2 ^ 64) : ok2 (spell2 n (t, i, z)) = true := by
  have hn' : n < 65536 := by rcases hn with rfl | rfl <;> decide
  have hl : (spell2 n (t, i, z)).length = 8 * 16 + 8 * z.size := by
    unfold spell2
    rw [List.length_append, length_bytesToBits, length_bytesToBits, _root_.Fmt.size_label]
  rw [ok2_iff, rd2_spell n t i z hn' ht hi, hl]
  exact ⟨⟨by omega, by omega⟩, hn, rfl⟩

/-- The first 16 bits of what is spelled under n are those of the word n. -/
theorem spell2_take (n : ℕ) (z : ℕ × ℕ × ByteArray) :
    16 ≤ (spell2 n z).length ∧
      (spell2 n z).take 16 = (bytesToBits (_root_.Fmt.u64n n)).take 16 := by
  have e : spell2 n z = bytesToBits (_root_.Fmt.u64n (n + 65536 * z.1)) ++
      (bytesToBits (_root_.Fmt.u64n z.2.1) ++ bytesToBits z.2.2) := by
    unfold spell2 _root_.Fmt.label
    rw [bytesToBits_append, List.append_assoc]
  have hl : (bytesToBits (_root_.Fmt.u64n (n + 65536 * z.1))).length = 64 := length_u64n _
  rw [e]
  exact ⟨by rw [List.length_append, hl]; omega,
    (take16 _ _ (by rw [hl]; omega)).trans (tag_low n z.1)⟩

/-- The identity on the bodies that pass `ok2` meets the sibling's widened `leafTag`. -/
theorem pBody2_tag (y m : List Bool) (h : (pBody ok2).put y = some m) :
    16 ≤ m.length ∧ (m.take 16 = t164 ∨ m.take 16 = t174) := by
  have h0 : (if ok2 y then some y else none) = some m := h
  by_cases hy : ok2 y = true
  · rw [if_pos hy] at h0
    cases h0
    obtain ⟨-, hn, he⟩ := (ok2_iff y).1 hy
    have ht := spell2_take (rd2 y).1 (rd2 y).2
    rw [← he] at ht
    refine ⟨ht.1, ?_⟩
    rcases hn with hn | hn
    · exact Or.inl (by rw [ht.2, hn]; rfl)
    · exact Or.inr (by rw [ht.2, hn]; rfl)
  · rw [if_neg hy] at h0
    cases h0

variable {I X : Type} (L : _root_.Iop.BatchProtocol I X)

/-- The map from a leaf query to a call of the format: for a body that passes `ok2`, the call under
the number that was read; the typed salt's first 256 bits are the start, the rest goes behind the
bytes. For any other body, none. -/
def call2 (q : Compile.Batch.LeafIn (strung L)) : Option _root_.Fmt.OQ :=
  if ok2 q.body then
    some ⟨0, (rd2 q.body).1, (rd2 q.body).2.1, (rd2 q.body).2.2.1, bitsToBytes (q.salt.take 256),
      (rd2 q.body).2.2.2 ++ bitsToBytes (q.salt.drop 256)⟩
  else none

/-- What the sibling's code of leaf queries over `pBody ok2` writes is the bits of the string of
`call2`'s call, at salts of whole bytes. -/
theorem pLeaf2_put (n k : ℕ) (hn : n = 8 * k) (q : Compile.Batch.LeafIn (strung L))
    (s : List Bool) (h : (TypedOracleCompiler.Run.pLeaf (L := strung L) n (pBody ok2)).put q = some s) :
    ∃ c, call2 L q = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨y0, sa⟩ := q
  obtain ⟨y, rfl⟩ : ∃ y : List Bool, y = y0 := ⟨y0, rfl⟩
  have h1 : (if sa.length = 256 + n then
          ((pBody ok2).put y).map (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)))
        else none) = some s := h
  by_cases hl : sa.length = 256 + n
  · rw [if_pos hl] at h1
    have h2 : ((if ok2 y then some y else none : Option (List Bool))).map
        (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256))) = some s := h1
    by_cases hy : ok2 y = true
    · rw [if_pos hy] at h2
      have es : s = pre33 ++ (sa.take 256 ++ ((y : List Bool) ++ sa.drop 256)) :=
        (Option.some.inj h2).symm
      have e1 : (sa.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
      have e2 : (sa.drop 256).length = 8 * k := by rw [List.length_drop, hl]; omega
      obtain ⟨-, hnum, he⟩ := (ok2_iff y).1 hy
      have h162 : (rd2 y).1 ≠ 162 := by rcases hnum with h | h <;> rw [h] <;> decide
      refine ⟨⟨0, (rd2 y).1, (rd2 y).2.1, (rd2 y).2.2.1, bitsToBytes (sa.take 256),
        (rd2 y).2.2.2 ++ bitsToBytes (sa.drop 256)⟩, if_pos hy, ?_⟩
      show s = bytesToBits (_root_.Fmt.oStr 0 (rd2 y).1 (rd2 y).2.1 (rd2 y).2.2.1
        (bitsToBytes (sa.take 256)) ((rd2 y).2.2.2 ++ bitsToBytes (sa.drop 256)))
      rw [oStr32_bits _ _ _ _ _ h162 (size_bitsToBytes _ 32 e1),
        bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩),
        bytesToBits_append, bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨k, e2⟩), es]
      conv_lhs => rw [he]
      unfold spell2
      rw [List.append_assoc]
    · rw [if_neg hy] at h2
      cases h2
  · rw [if_neg hl] at h1
    cases h1

/-- The clause on leaves of the sibling's `FitX`, at every page whose leaf code is `pBody ok2`
and whose salts are whole bytes, and every maps whose map of leaves is `call2`; whatever the page's
test. -/
theorem fitX_leaf {K : ℕ} {tg : _root_.Compile.Tag} (C : TypedOracleCompiler.Run.PageC (strung L) K tg)
    (T : TypedOracleCompiler.Run.CallsX (strung L) K tg) (hC : C.leafP = pBody ok2) (k : ℕ)
    (hk : C.saltBits = 8 * k) (hT : T.leaf = call2 L) (q : Compile.Batch.LeafIn (strung L))
    (s : List Bool) (h : (TypedOracleCompiler.Run.pLeafC C).put q = some s) :
    ∃ c, T.leaf q = some c ∧ s = bytesToBits (strOf c) := by
  have h1 := (TypedOracleCompiler.Run.pLeafC_put C q s h).2
  rw [hC] at h1
  rw [hT]
  exact pLeaf2_put L C.saltBits k hk q s h1

/-- What OnBytes/TypedOracleCompiler/StringsRead.lean's `spell` spells (a label under 164, and bytes) passes `ok2`
and is read back with the number 164, if both words of the label are below 2 ^ 64. -/
theorem ok2_rd2_of_spell {b : List Bool} (t i : ℕ) (z : ByteArray) (hb : b = spell (t, i, z))
    (ht : 164 + 65536 * t < 2 ^ 64) (hi : i < 2 ^ 64) :
    ok2 b = true ∧ rd2 b = (164, t, i, z) := by
  have ht' : t < 2 ^ 48 := by omega
  rw [hb]
  exact ⟨ok2_spell 164 t i z (Or.inl rfl) ht' hi, rd2_spell 164 t i z (by decide) ht' hi⟩

end TypedOracleCompiler.Strings

namespace TypedOracleCompiler.Slice
open _root_.Iop (OPos OSym)
open TypedOracleCompiler.Run TypedOracleCompiler.Strings

variable (salt : ℕ) (C : PQ.CK)

/-- A prover's symbol's body passes `ok2`, and `rd2` reads from it the number 164 and the
sibling's own spelling of its leaf, in one list of rounds, under the conditions on the trees and
the salt. -/
theorem ok2_rd2_embTail (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds)
    (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) :
    ok2 (embTail salt C ds p a) = true ∧
      rd2 (embTail salt C ds p a) = (164, PQ.leafSL C salt ds ⟨p, a⟩) := by
  have hw := inWordsL_of salt C h8 ds h ⟨p, a⟩
  rw [← leafSL_eq salt C ds ⟨p, a⟩] at hw ⊢
  exact ok2_rd2_of_spell _ _ _ (fits_tail salt C ds h.shallow p a) hw.1 hw.2

/-- The same at the protocol in three stretches, with `Stretches.leafS` as the spelling. -/
theorem Stretches.ok2_rd2_embS (G : Stretches) (h8 : salt / 8 < 2 ^ 8) (h : G.Small)
    (p : OPos G.sh) (a : OSym G.sh p) :
    ok2 (G.embS salt p a) = true ∧ rd2 (G.embS salt p a) = (164, G.leafS salt p a) :=
  ok2_rd2_of_spell _ _ _ (G.embS_fit salt h.shallow p a) (G.inWords_of salt h8 h p a).1
    (G.inWords_of salt h8 h p a).2

end TypedOracleCompiler.Slice
