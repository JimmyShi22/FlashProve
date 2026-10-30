-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WordsBytes.lean: a file of whole 32-bit words is rebuilt from its words, and the
request file and the reply file are rebuilt from the instance that they say.

`Model.Verify.words32` (OnBytes/Model/VerifyStages.lean) reads a file as its 32-bit words, the
lowest byte first. `bytesOfWords` writes words back as bytes, by the port's own `word32`
(OnBytes/Hash/SecondHashFunction.lean). An instance holds tokens and numbers, no bytes; what is hashed of a
request is made of the request FILE (`Proof.requestItem`, OnBytes/Proof/RequestItem.lean). So
whoever goes from an instance to what is hashed needs the file's bytes back.

Main names:
  `bytesOfWords`: the bytes of a list of words.
  `bytesOfWords_words32`: a file whose length is a multiple of four bytes is `bytesOfWords` of its
    `words32`.
  `requestBytesOf x`, `replyBytesOf x`: the two files that say an instance.
  `requestBytesOf_withoutReply`: the request file at the instance with the reply 0 is the one at the
    instance (by rfl).
  `insOf_bytes`: under the premises of `insOf_words` (Johnson/Flat/InsOf.lean), for two files of
    whole words: the files rebuilt from the built instance ARE the user's request file and reply
    file.
Limits: nothing on a file with bytes behind its last whole word: `words32` leaves them out.

-/
import Johnson.Flat.InsOf
import Johnson.Flat.LinksAt
import Fmt.ParsedReadLaws

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify

/-- The bytes of a list of 32-bit words, each the lowest byte first. -/
def bytesOfWords (w : Array UInt32) : ByteArray := Fmt.cat (w.toList.map fun a => word32 a.toNat)

/-- Two neighbouring pieces of a string. -/
theorem extract_next (b : ByteArray) (j k : Nat) (h : j ≤ k) :
    b.extract 0 j ++ b.extract j k = b.extract 0 k := by
  apply ByteArray.ext
  rw [ByteArray.data_append, ByteArray.data_extract, ByteArray.data_extract,
    ByteArray.data_extract, Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right h]

/-- A list of strings and one more. -/
theorem cat_snoc (l : List ByteArray) (x : ByteArray) : Fmt.cat (l ++ [x]) = Fmt.cat l ++ x := by
  unfold Fmt.cat
  rw [List.foldl_append]
  rfl

/-- Word i of a file, written back, is the file's piece at that word. -/
theorem word32_klWord (b : ByteArray) (i : Nat) (h : 4 * i + 4 ≤ b.size) :
    word32 (klWord b i) = b.extract (4 * i) (4 * i + 4) := by
  unfold klWord
  rw [if_pos h]
  exact Fmt.lowBytes_leNat b (4 * i) 4 (by decide) h

/-- A word of a file is below 2 ^ 32. -/
theorem klWord_lt (b : ByteArray) (i : Nat) : klWord b i < 2 ^ 32 := by
  unfold klWord
  split
  · exact Fmt.leNat_lt b 4 (4 * i)
  · decide

/-- The first n words of a file, written back, are its first 4 n bytes. -/
theorem cat_words (b : ByteArray) : ∀ n : Nat, 4 * n ≤ b.size →
    Fmt.cat ((List.range n).map fun i => word32 (klWord b i)) = b.extract 0 (4 * n)
  | 0, _ => by
    rw [List.range_zero, List.map_nil, Fmt.cat_nil, Nat.mul_zero, Fmt.extract_same]
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_singleton, cat_snoc,
      cat_words b n (by omega), word32_klWord b n (by omega)]
    exact extract_next b (4 * n) (4 * (n + 1)) (by omega)

/-- **A file of whole words is rebuilt from its words.** -/
theorem bytesOfWords_words32 (b : ByteArray) (h : b.size % 4 = 0) :
    bytesOfWords (words32 b) = b := by
  have e : (words32 b).toList.map (fun a => word32 a.toNat) =
      (List.range (b.size / 4)).map fun i => word32 (klWord b i) := by
    unfold words32 fileWords
    simp only [Array.toList_map, Array.toList_range, List.map_map]
    apply List.map_congr_left
    intro i _
    show word32 (klWord b i).toUInt32.toNat = word32 (klWord b i)
    rw [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (klWord_lt b i)]
  unfold bytesOfWords
  rw [e, cat_words b (b.size / 4) (by omega)]
  have hs : 4 * (b.size / 4) = b.size := by omega
  rw [hs]
  apply ByteArray.ext
  rw [ByteArray.data_extract, ← ByteArray.size_data]
  exact Array.extract_size

/-- The request file that says an instance. -/
def requestBytesOf {P : Params} (x : Instance' P) : ByteArray := bytesOfWords (requestWordsOf x)

/-- The reply file that says an instance. -/
def replyBytesOf {P : Params} (x : Instance' P) : ByteArray := bytesOfWords (replyWordsOf x)

/-- The request file at the instance with the reply 0 is the one at the instance. -/
theorem requestBytesOf_withoutReply {P : Params} (hV : 0 < P.V) (x : Instance' P) :
    requestBytesOf (withoutReply hV x) = requestBytesOf x := rfl

/-- **The two files rebuilt from the built instance are the user's.** -/
theorem insOf_bytes {P : Params} {x : K.UserStm} {so : Head.StOwn} {cov : Head.Covered}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) P.T = .ok so)
    (hc : Head.coveredOf so P.T P.V = .ok cov) (hr : x.request.size % 4 = 0)
    (hy : x.y.size % 4 = 0) :
    ∃ i : Instance' P, insOf P x = some i ∧ requestBytesOf i = x.request ∧
      replyBytesOf i = x.y := by
  obtain ⟨i, g0, g1, g2, _⟩ := insOf_words h hc
  refine ⟨i, g0, ?_, ?_⟩
  · unfold requestBytesOf
    rw [g1]
    exact bytesOfWords_words32 _ hr
  · unfold replyBytesOf
    rw [g2]
    exact bytesOfWords_words32 _ hy

end OnBytes.Flat
