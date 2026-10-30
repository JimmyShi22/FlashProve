-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules5Fast.lean: the blocks of a round's answer, computed with the hash's state kept after the
whole blocks of what all calls of the round share, with a proof that they are the same blocks.

Why. Call j of round i hashes the label, the prover's message and then two words, of which the first
holds j (docs/format/FORMAT.md, R5.2). So all calls of a round share everything but their last
sixteen bytes.
Fmt/Rules5.lean hashes each call from its start: with a message of many thousand bytes and eleven
calls that is eleven times the whole message. Fmt/Blake2bFast.lean has the state behind the whole
blocks of a prefix (absorb), the rest from there (finish), and the theorem that the two together are
the hash; `call_finish` applies it (`finish_absorb`) with its two premises: the prefix's length is a
multiple of 128 (h1), the rest is not empty (h2). Call, an answer's block and chain: Fmt/Rules5.lean
(`callW`, `fetchW`, `Chain`); the hash's own blocks: `wholeOf`.

Sources. Section 5 of the format page (FORMAT.md, which comes with the programs), and R2.6's
remark, rules R5.1 to R5.7 and R2.6; this file is not held against the page as it ships, and
may differ from it. No Mathlib.

1. What the file contains.
   `HF`: The hash formatHash with the flat form of BLAKE2b (Fmt/Blake2bFast.lean) under it.
   `finishCalls st left kind w nonce n j acc`: The state `st` is an argument, so it is made once.
   `fetchF lab rho i msg kind w nonce n`: The blocks 0 .. n - 1 of the answer of round i.
   `Chain.queryF`: The step of a chain on fetchF.

2. What is checked when the file compiles. Three tests (#guard).

3. Theorems.
   `HF_eq`: HF = formatHash.
   `call_finish`: One call: finished from the state = hashed from its start.
   `fetchF_eq`: fetchF = the fetching of Fmt/Rules5.lean at the identity monad and the hash formatHash, for
      all arguments.
   `queryF_eq`: Chain.queryF is Chain.query.

4. What is not claimed. Nothing on time (it is measured elsewhere). The forms over a variable monad
keep no state: a state cannot be kept across calls of a hash that is handed in as a function.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules5
import Fmt.Blake2bFast

namespace Fmt

/-- the hash formatHash with the flat form of BLAKE2b under it -/
def HF (number tree index : Nat) (start bytes : ByteArray) : ByteArray :=
  blake2bF (dlen number) ((fit 32 start).extract 0 16)
    ((fit 32 start).extract 16 32) (label number tree index ++ bytes)

/-- the calls j, j + 1, .., each finished from the state, each cut in two, behind what is there -/
def finishCalls (st : B2.Mid) (left : ByteArray) (kind : Kind) (w nonce : Nat) :
    Nat → Nat → Array ByteArray → Array ByteArray
  | 0, _, acc => acc
  | n + 1, j, acc =>
    finishCalls st left kind w nonce n (j + 1)
      ((acc.push ((finish 64 st (left ++ tail kind w nonce j)).extract 0 32)).push
        ((finish 64 st (left ++ tail kind w nonce j)).extract 32 64))

/-- what all calls of a round share -/
def shared (lab i : Nat) (msg : ByteArray) : ByteArray := label 162 lab i ++ msg

/-- the number of bytes in b's whole blocks of 128 bytes (blocks of the hash's input, not the
answer's blocks of 32 bytes) -/
def wholeOf (b : ByteArray) : Nat := 128 * (b.size / 128)

/-- The blocks 0 .. n - 1 of the answer of round i, the state kept. -/
def fetchF (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce n : Nat) : Array ByteArray :=
  (finishCalls
      (absorb 64 ((fit 32 rho).extract 0 16) ((fit 32 rho).extract 16 32)
        ((shared lab i msg).extract 0 (wholeOf (shared lab i msg))))
      ((shared lab i msg).extract (wholeOf (shared lab i msg)) (shared lab i msg).size) kind w nonce
      ((n + 1) / 2) 0 #[]).extract
    0 n

/-- The step of a chain, on fetchF -/
def Chain.queryF (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    Option (Chain × Array ByteArray) :=
  if askOK c.label c.rho (c.round + 1) msg kind work nonce then
    (fun bs =>
        if passesA work bs then some (⟨c.label, nextA work bs, c.round + 1⟩, msgA work bs)
        else none)
      (fetchF c.label c.rho (c.round + 1) msg kind work nonce (firstBlock work + K))
  else none

namespace Spec
def HF_eq : Prop := HF = formatHash
def fetchF_eq : Prop :=
  ∀ (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce n : Nat),
    fetchF lab rho i msg kind w nonce n = fetchW (m := Id) formatHash lab rho i msg kind w nonce n
def queryF_eq : Prop :=
  ∀ (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat),
    c.queryF msg kind work nonce K = c.query msg kind work nonce K
end Spec

theorem HF_eq : Spec.HF_eq := by
  funext number tree index start bytes
  exact blake2bF_eq _ _ _ _

/-- for q ≤ b.size (h): a string is its first q bytes and the rest -/
theorem extract_split (b : ByteArray) (q : Nat) (h : q ≤ b.size) :
    b.extract 0 q ++ b.extract q b.size = b := by
  apply ByteArray.ext
  rw [ByteArray.data_append, ByteArray.data_extract, ByteArray.data_extract, ← ByteArray.size_data]
  rw [← ByteArray.size_data] at h
  rw [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right h, Array.extract_size]

theorem size_tail (kind : Kind) (w nonce j : Nat) : (tail kind w nonce j).size = 16 := rfl

/-- One call: finished from the state = hashed from its start. -/
theorem call_finish (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce j : Nat) :
    finish 64 (absorb 64 ((fit 32 rho).extract 0 16) ((fit 32 rho).extract 16 32)
          ((shared lab i msg).extract 0 (wholeOf (shared lab i msg))))
        ((shared lab i msg).extract (wholeOf (shared lab i msg)) (shared lab i msg).size ++
          tail kind w nonce j) =
      callW (m := Id) formatHash lab rho i msg kind w nonce j := by
  have hq : wholeOf (shared lab i msg) ≤ (shared lab i msg).size := Nat.mul_div_le _ _
  have h1 : ((shared lab i msg).extract 0 (wholeOf (shared lab i msg))).size % 128 = 0 := by
    rw [ByteArray.size_extract, Nat.min_eq_left hq, Nat.sub_zero]
    exact Nat.mul_mod_right _ _
  have h2 : 0 <
      ((shared lab i msg).extract (wholeOf (shared lab i msg)) (shared lab i msg).size ++
        tail kind w nonce j).size := by
    rw [ByteArray.size_append, size_tail]
    omega
  rw [finish_absorb 64 _ _ _ _ h1 h2, ← ByteArray.append_assoc, extract_split _ _ hq]
  show blake2b 64 _ _ (label 162 lab i ++ msg ++ tail kind w nonce j) =
    blake2b (dlen 162) _ _ (label 162 lab i ++ (msg ++ tail kind w nonce j))
  rw [ByteArray.append_assoc]
  rfl

theorem finishCalls_eq (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce : Nat) :
    ∀ (n j : Nat) (acc : Array ByteArray),
      finishCalls (absorb 64 ((fit 32 rho).extract 0 16) ((fit 32 rho).extract 16 32)
            ((shared lab i msg).extract 0 (wholeOf (shared lab i msg))))
          ((shared lab i msg).extract (wholeOf (shared lab i msg)) (shared lab i msg).size)
          kind w nonce n j acc =
        fetchFrom (m := Id) formatHash lab rho i msg kind w nonce n j acc
  | 0, _, _ => rfl
  | n + 1, j, acc => by
    unfold finishCalls
    rw [call_finish, finishCalls_eq lab rho i msg kind w nonce n (j + 1)]
    rfl

theorem fetchF_eq : Spec.fetchF_eq := by
  intro lab rho i msg kind w nonce n
  unfold fetchF
  rw [finishCalls_eq]
  rfl

theorem queryF_eq : Spec.queryF_eq := by
  intro c msg kind work nonce K
  unfold Chain.queryF
  rw [fetchF_eq]
  show _ = Chain.queryW (m := Id) formatHash c msg kind work nonce K
  unfold Chain.queryW
  split <;> rfl

-- fetchF against fetchW at formatHash, also at lengths around a 128-byte block's end: the same; HF against formatHash
#guard [0, 8, 96, 104, 112, 120, 240, 1000].all fun n => [1, 2, 3, 6, 7].all fun k => fetchF 7 (pattern 32) 3 (pattern n) .elems 0 0 k == fetchW (m := Id) formatHash 7 (pattern 32) 3 (pattern n) .elems 0 0 k
#guard fetchF 1 (pattern 32 5 1) 30 (pattern 4000) .positions 20 77 21 == fetchW (m := Id) formatHash 1 (pattern 32 5 1) 30 (pattern 4000) .positions 20 77 21
#guard HF 166 0 0 (pattern 32) (pattern 64) == formatHash 166 0 0 (pattern 32) (pattern 64)

end Fmt
