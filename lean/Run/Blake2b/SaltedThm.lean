-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.Salted
import Run.Blake2b.LoadThm
import Run.Blake2b.ResumeThm
/-!
# Theorems on Salted.lean

* size_bytes, size_blake2bSalted: a digest of outlen ≤ 64 bytes has outlen bytes.
* message_bytes_append: a message of bytes that begins with whole blocks, cut after them.
* stateSalted_append: the same for the functions of Salted.lean: the last state of pre ++ rest is
  resumeBytes on rest from the state that absorbBytes leaves after pre, if pre.size is a multiple
  of 128 and rest is not empty.
* blake2bSalted_zero: if the first sixteen bytes of the salt and of the personalization read as 0
  (sixteen zero bytes, or a shorter array of zeros, or the empty array), blake2bSalted is blake2b of
  Hash.lean without a key.

What is not proved here: nothing is said about a message whose rest is empty or whose beginning is
not a multiple of 128 bytes long. For a salt or a personalization that is not zero no theorem ties
blake2bSalted to the plain definition of Spec.lean: there only the known answers of Test/Salted.lean
and Fmt/Blake2bKnown.lean support it.
-/
namespace Run.Blake2b

/-! ## 1. Bytes in two parts -/

/-- A read at or after the seam of two arrays in a row, also beyond the end. -/
theorem getD_append_right (a b : Array UInt8) (k : Nat) :
    (a ++ b).getD (a.size + k) 0 = b.getD k 0 := by
  by_cases h : k < b.size
  · exact getD_append_ge h
  · rw [getD_of_ge (by rw [Array.size_append]; omega), getD_of_ge h]

/-- A message of bytes cut after a beginning of whole blocks. If at least one byte follows, the
message's last state is that of the rest, begun in the state after the beginning. -/
theorem message_bytes_append (S : State) (pre rest : ByteArray) (hp : pre.size % 128 = 0)
    (hr : 0 < rest.size) :
    message (fun j => MessageBlock.ofBytes (pre ++ rest) (128 * j)) (pre ++ rest).size S =
      message (fun j => MessageBlock.ofBytes rest (128 * j)) rest.size
        (updateBlocks (fun j => MessageBlock.ofBytes pre (128 * j)) (pre.size / 128) 0 S) := by
  have hs : (pre ++ rest).size = 128 * (pre.size / 128) + rest.size := by
    rw [ByteArray.size_append]; omega
  have ea : updateBlocks (fun j => MessageBlock.ofBytes (pre ++ rest) (128 * j)) (pre.size / 128) 0 S =
      updateBlocks (fun j => MessageBlock.ofBytes pre (128 * j)) (pre.size / 128) 0 S := by
    refine updateBlocks_congr _ _ _ (fun j _ hj => ?_)
    show MessageBlock.ofBytes ⟨(pre ++ rest).data⟩ (128 * j) = MessageBlock.ofBytes ⟨pre.data⟩ (128 * j)
    refine ofBytes_congr (fun m hm => ?_)
    rw [ByteArray.data_append, getD_append_lt (by rw [ByteArray.size_data]; omega)]
  rw [hs, message_split _ _ _ _ hr, ea]
  refine message_congr _ _ (fun j _ => ?_)
  show MessageBlock.ofBytes ⟨(pre ++ rest).data⟩ (128 * (pre.size / 128 + j)) =
    MessageBlock.ofBytes ⟨rest.data⟩ (128 * j)
  refine ofBytes_congr (fun m _ => ?_)
  rw [ByteArray.data_append,
    show 128 * (pre.size / 128 + j) + m = pre.data.size + (128 * j + m) from by
      rw [ByteArray.size_data]; omega,
    getD_append_right]

/-! ## 2. The digest's length -/

/-- The first outlen ≤ 64 bytes of the full hash are outlen bytes. -/
theorem size_bytes (s : ChainingValue) (outlen : Nat) (h : outlen ≤ 64) : (s.bytes outlen).size = outlen := by
  unfold ChainingValue.bytes
  rw [ByteArray.size_extract, ← ByteArray.size_data, size_bytes64]
  omega

/-- A digest of outlen ≤ 64 bytes has outlen bytes; for outlen = 0 it is empty. -/
theorem size_blake2bSalted (salt personal data : ByteArray) (outlen : Nat) (h : outlen ≤ 64) :
    (blake2bSalted salt personal data outlen).size = outlen := by
  unfold blake2bSalted
  by_cases h0 : outlen = 0 ∨ outlen > 64
  · rw [if_pos h0, ByteArray.size_empty]
    omega
  · rw [if_neg h0]
    exact size_bytes _ _ h

/-! ## 3. A beginning and a rest -/

/-- The last state of pre ++ rest from the state after pre. The beginning has whole blocks only and
the rest is not empty. -/
theorem stateSalted_append (salt personal pre rest : ByteArray) (outlen : Nat)
    (hp : pre.size % 128 = 0) (hr : 0 < rest.size) :
    stateSalted salt personal (pre ++ rest) outlen =
      resumeBytes (absorbBytes (firstStateSalted outlen salt personal) pre (pre.size / 128))
        rest := by
  unfold stateSalted resumeBytes absorbBytes
  rw [message_bytes_append _ _ _ hp hr]

/-! ## 4. Without a salt and a personalization -/

/-- Eight bytes that read as 0 are the word 0. -/
theorem load64_zero (a : ByteArray) (k : Nat) (h : ∀ j, j < 8 → byteOrZero a (k + j) = 0) :
    load64 a k = 0 := by
  rw [load64_eq_plain]
  unfold load64Plain
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]
  decide +kernel

/-- A salt and a personalization whose first sixteen bytes read as 0 give the first state of
Hash.lean without a key. -/
theorem firstStateSalted_zero (outlen : Nat) (salt personal : ByteArray)
    (hs : ∀ i, i < 16 → byteOrZero salt i = 0) (hp : ∀ i, i < 16 → byteOrZero personal i = 0) :
    firstStateSalted outlen salt personal = firstState 0 outlen := by
  unfold firstStateSalted firstState
  rw [load64_zero salt 0 (fun j hj => hs _ (by omega)),
    load64_zero salt 8 (fun j hj => hs _ (by omega)),
    load64_zero personal 0 (fun j hj => hp _ (by omega)),
    load64_zero personal 8 (fun j hj => hp _ (by omega))]

/-- With a salt and a personalization whose first sixteen bytes read as 0, blake2bSalted is blake2b
without a key, for all data and every outlen. -/
theorem blake2bSalted_zero (salt personal data : ByteArray) (outlen : Nat)
    (hs : ∀ i, i < 16 → byteOrZero salt i = 0) (hp : ∀ i, i < 16 → byteOrZero personal i = 0) :
    blake2bSalted salt personal data outlen = blake2b ByteArray.empty data outlen := by
  have hk : ¬ ByteArray.empty.size > 64 := by rw [ByteArray.size_empty]; omega
  have hz : ¬ ByteArray.empty.size > 0 := by rw [ByteArray.size_empty]; omega
  unfold blake2bSalted blake2b
  by_cases h0 : outlen = 0 ∨ outlen > 64
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, if_neg hk]
    unfold stateSalted state
    dsimp only
    rw [if_neg hz, firstStateSalted_zero outlen salt personal hs hp, ByteArray.size_empty]

end Run.Blake2b

#print axioms Run.Blake2b.getD_append_right
#print axioms Run.Blake2b.message_bytes_append
#print axioms Run.Blake2b.size_bytes
#print axioms Run.Blake2b.size_blake2bSalted
#print axioms Run.Blake2b.stateSalted_append
#print axioms Run.Blake2b.load64_zero
#print axioms Run.Blake2b.firstStateSalted_zero
#print axioms Run.Blake2b.blake2bSalted_zero
