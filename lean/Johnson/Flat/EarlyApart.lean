-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/EarlyApart.lean: two instances with different early parts have different request files.

The early part of an instance, under the ruled typing, is the instance with the reply 0
(`withoutReply`, Johnson/Flat/LinksAt.lean). The statement's item "request" is made of the request
file (`requestBytesOf`, Johnson/Flat/WordsBytes.lean). Here: the early part holds nothing that the
request file does not say.

Main names:
  `words32_bytesOfWords`: the words of the bytes of a list of words are that list: with
    `bytesOfWords_words32` the two ways are inverse on files of whole words. `bytesOfWords_inj`.
  `requestWordsOf_inj`: where the window is below 2 ^ 32 and the vocabulary at most 2 ^ 32: two
    instances with the same request words have the same tokens, r and e.
  `early_of_requestBytes`: there, two instances with one request file have one early part. Read the
    other way: TWO DIFFERENT EARLY PARTS HAVE TWO DIFFERENT REQUEST FILES.
Limits: nothing on the item: in it the request file stands as a digest of the second hash function,
so two request files may have one item. The two bounds are premises; `sizesAt_planned`
(Johnson/Flat/SizesPlanned.lean) pays them at the sizes of a parameter file.

-/
import Johnson.Flat.WordsBytes

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify

/-- A word is written as four bytes. -/
theorem size_word32 (x : Nat) : (word32 x).size = 4 := Fmt.size_lowBytes 4 x (by decide)

/-- Two lists of strings, one after the other. -/
theorem cat_app (l m : List ByteArray) : Fmt.cat (l ++ m) = Fmt.cat l ++ Fmt.cat m := by
  induction l with
  | nil => rw [List.nil_append, Fmt.cat_nil, ByteArray.empty_append]
  | cons x l ih => rw [List.cons_append, Fmt.cat_cons, Fmt.cat_cons, ih, ByteArray.append_assoc]

/-- The bytes of n words are 4 n. -/
theorem size_catWords (l : List UInt32) :
    (Fmt.cat (l.map fun a => word32 a.toNat)).size = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, Fmt.cat_cons, ByteArray.size_append, size_word32, ih, List.length_cons]
    omega

/-- The word behind l1 in the bytes of l1, a, l2 is a. -/
theorem klWord_cat (l1 : List UInt32) (a : UInt32) (l2 : List UInt32) :
    klWord (Fmt.cat ((l1 ++ a :: l2).map fun a => word32 a.toNat)) l1.length = a.toNat := by
  have e : Fmt.cat ((l1 ++ a :: l2).map fun a => word32 a.toNat) =
      Fmt.cat (l1.map fun a => word32 a.toNat) ++ Fmt.lowBytes 4 a.toNat ++
        Fmt.cat (l2.map fun a => word32 a.toNat) := by
    rw [List.map_append, cat_app, List.map_cons, Fmt.cat_cons, ByteArray.append_assoc]
    rfl
  have ha : a.toNat < 256 ^ 4 := a.toNat_lt
  have U := Fmt.undoes_readLE 4 (by decide) a.toNat ha (Fmt.cat (l1.map fun a => word32 a.toNat))
    (Fmt.cat (l2.map fun a => word32 a.toNat))
  rw [← e, size_catWords] at U
  unfold Fmt.readLE at U
  unfold klWord
  split at U
  · rename_i hs
    rw [if_pos hs]
    exact congrArg Prod.fst (Option.some.inj U)
  · cases U

/-- **The words of the bytes of a list of words are that list.** -/
theorem words32_bytesOfWords (w : Array UInt32) : words32 (bytesOfWords w) = w := by
  have hs : (bytesOfWords w).size = 4 * w.size := by
    unfold bytesOfWords
    rw [size_catWords, Array.length_toList]
  apply Array.ext
  · unfold words32 fileWords
    rw [Array.size_map, Array.size_map, Array.size_range, hs]
    omega
  · intro i h1 h2
    have hsplit : w.toList = w.toList.take i ++ w[i] :: w.toList.drop (i + 1) := by
      have hi : i < w.toList.length := by rw [Array.length_toList]; exact h2
      have e0 : w.toList[i] = w[i] := Array.getElem_toList h2
      rw [← e0, ← List.drop_eq_getElem_cons hi]
      exact (List.take_append_drop i w.toList).symm
    have hlen : (w.toList.take i).length = i := by
      rw [List.length_take, Array.length_toList]
      omega
    have hk := klWord_cat (w.toList.take i) w[i] (w.toList.drop (i + 1))
    rw [← hsplit, hlen] at hk
    unfold words32 fileWords
    simp only [Array.getElem_map, Array.getElem_range]
    show (klWord (bytesOfWords w) i).toUInt32 = w[i]
    unfold bytesOfWords
    rw [hk]
    exact UInt32.ofNat_toNat

/-- Two lists of words with the same bytes are one list. -/
theorem bytesOfWords_inj {w w' : Array UInt32} (h : bytesOfWords w = bytesOfWords w') : w = w' := by
  rw [← words32_bytesOfWords w, ← words32_bytesOfWords w', h]

/-- A number below 2 ^ 32 comes back from its word. -/
theorem ofNat32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : UInt32.ofNat a = UInt32.ofNat b) : a = b := by
  have := congrArg UInt32.toNat h
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

/-- **Two instances with the same request words have the same tokens, r and e.** -/
theorem requestWordsOf_inj {P : Params} (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32)
    {x x' : Instance' P} (h : requestWordsOf x = requestWordsOf x') :
    x.prompt = x'.prompt ∧ x.rF = x'.rF ∧ x.eF = x'.eF := by
  have bR : ∀ z : Instance' P, z.r < 2 ^ 32 := fun z => by
    have := Nat.lt_succ_iff.1 z.rF.isLt
    show z.rF.val < _
    omega
  have bE : ∀ z : Instance' P, z.e < 2 ^ 32 := fun z => by
    have := Nat.lt_succ_iff.1 z.eF.isLt
    show z.eF.val < _
    omega
  refine ⟨?_, ?_, ?_⟩
  · funext t
    have a1 : ∀ z : Instance' P, (requestWordsOf z).getD t.val 0 = UInt32.ofNat (z.prompt t).val :=
      fun z => by
        have ht : t.val < (requestWordsOf z).size := by
          rw [size_requestWordsOf]
          omega
        have e0 : (requestWordsOf z).getD t.val 0 = (requestWordsOf z)[t.val] := by
          simp [Array.getD_eq_getD_getElem?, ht]
        rw [e0]
        simp [requestWordsOf, t.isLt]
    have e := a1 x
    rw [h, a1 x'] at e
    exact Fin.ext (ofNat32_inj (Nat.lt_of_lt_of_le (x.prompt t).isLt hV)
      (Nat.lt_of_lt_of_le (x'.prompt t).isLt hV) e.symm)
  · have e := requestWordsOf_r x
    rw [h, requestWordsOf_r x'] at e
    exact Fin.ext (ofNat32_inj (bR x) (bR x') e.symm)
  · have e := requestWordsOf_e x
    rw [h, requestWordsOf_e x'] at e
    exact Fin.ext (ofNat32_inj (bE x) (bE x') e.symm)

/-- **Two instances with one request file have one early part.** -/
theorem early_of_requestBytes {P : Params} (hT : P.T < 2 ^ 32) (hV' : P.V ≤ 2 ^ 32) (hV : 0 < P.V)
    {x x' : Instance' P} (h : requestBytesOf x = requestBytesOf x') :
    withoutReply hV x = withoutReply hV x' := by
  obtain ⟨e1, e2, e3⟩ := requestWordsOf_inj hT hV' (bytesOfWords_inj h)
  unfold withoutReply
  rw [e1, e2, e3]

end OnBytes.Flat
