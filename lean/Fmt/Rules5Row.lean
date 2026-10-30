-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules5Row.lean: the row of blocks that is fetched for a round, block by block, at any hash h.
This file proves, at the identity monad, that n blocks are fetched and that, for b < n, entry b of
what is fetched is `blockW h .. b`, that is half (b mod 2) of call (b div 2).

One definition; theorems and proofs. No Mathlib.
Sources. The programs' format, section 5 (an edition of the format page; a second edition moves no
rule that is rendered here; R5.2 and R5.4 have one and the same text at several further editions,
compared with one another by program; all the editions named here are older than the one that
ships).

In each round of a chain the prover's message is hashed together with the chain's value so far, in
one or more calls (`callW`, Fmt/Rules5.lean; 64 bytes each at the format's hash `Fmt.formatHash`). At that
hash the answer is a row of blocks of 32 bytes, which gives the chain's next value and the
verifier's message (the challenges).
Fmt/Rules5.lean fetches the blocks 0 .. n - 1 of a round's answer by a loop over the calls, each cut
in two, and cuts the array to n (`fetchW`, `fetchFrom`).

Why: whoever connects another description of the blocks with `fetchW` needs the array's entries.

Main names:
  `blockW h .. b` (R5.2, R5.4), `getD_push`, `fetchFrom_succ`, `fetchFrom_spec`.
  `size_fetchW`: n blocks are fetched.
  `fetchW_getD`: for b < n: entry b of what is fetched is `blockW h .. b`.

Notation: `rho`, `kind`, `w`: arguments of `callW` (Fmt/Rules5.lean); `rho`: a `ByteArray`: in
`Chain` (the same file), the chain's value; `kind`: a `Kind` (Fmt/Plan.lean): what the verifier's
message of a round consists of; `w`: a natural number: the round's bits of work.

Limits: only the identity monad. The definition `blockW` and every statement on fetching are at the
identity monad only (`m := Id`). This file says nothing on the hash.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules5

set_option autoImplicit false

namespace Fmt

section
variable (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
  (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce : Nat)

/-- block b of the row of blocks of round i, at any hash: half (b mod 2) of call (b div 2) -/
def blockW (b : Nat) : ByteArray :=
  (callW (m := Id) h lab rho i msg kind w nonce (b / 2)).extract (32 * (b % 2)) (32 * (b % 2) + 32)

omit h lab rho i msg kind w nonce in
theorem getD_push (a : Array ByteArray) (x : ByteArray) (b : Nat) (e : ByteArray) :
    (a.push x).getD b e = if b = a.size then x else a.getD b e := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

theorem fetchFrom_succ (n j : Nat) (acc : Array ByteArray) :
    fetchFrom (m := Id) h lab rho i msg kind w nonce (n + 1) j acc =
      fetchFrom (m := Id) h lab rho i msg kind w nonce n (j + 1)
        ((acc.push ((callW (m := Id) h lab rho i msg kind w nonce j).extract 0 32)).push
          ((callW (m := Id) h lab rho i msg kind w nonce j).extract 32 64)) := rfl

/-- What is fetched: after j calls whose 2 j blocks are in acc, n calls more. -/
theorem fetchFrom_spec :
    ∀ (n j : Nat) (acc : Array ByteArray), acc.size = 2 * j →
      (∀ b, b < 2 * j → acc.getD b ByteArray.empty = blockW h lab rho i msg kind w nonce b) →
      (fetchFrom (m := Id) h lab rho i msg kind w nonce n j acc).size = 2 * (j + n) ∧
      ∀ b, b < 2 * (j + n) →
        (fetchFrom (m := Id) h lab rho i msg kind w nonce n j acc).getD b ByteArray.empty =
          blockW h lab rho i msg kind w nonce b
  | 0, j, acc, hs, ha => ⟨hs, ha⟩
  | n + 1, j, acc, hs, ha => by
      rw [fetchFrom_succ]
      have e : j + (n + 1) = (j + 1) + n := by omega
      rw [e]
      refine fetchFrom_spec n (j + 1) _
        (by rw [Array.size_push, Array.size_push, hs]; omega) fun b hb => ?_
      rw [getD_push, getD_push, Array.size_push, hs]
      by_cases h1 : b < 2 * j
      · rw [if_neg (by omega), if_neg (by omega)]
        exact ha b h1
      · by_cases h2 : b = 2 * j
        · subst h2
          rw [if_neg (by omega), if_pos rfl]
          unfold blockW
          rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
        · have h3 : b = 2 * j + 1 := by omega
          subst h3
          rw [if_pos rfl]
          unfold blockW
          rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]

theorem size_fetchW (n : Nat) : (fetchW (m := Id) h lab rho i msg kind w nonce n).size = n := by
  have s := (fetchFrom_spec h lab rho i msg kind w nonce ((n + 1) / 2) 0 #[] rfl
    (fun b hb => absurd hb (Nat.not_lt_zero _))).1
  show ((fetchFrom (m := Id) h lab rho i msg kind w nonce ((n + 1) / 2) 0 #[]).extract 0 n).size = n
  rw [Array.size_extract, s]
  omega

/-- The row that is fetched, block by block: for b < n. -/
theorem fetchW_getD (n b : Nat) (hb : b < n) :
    (fetchW (m := Id) h lab rho i msg kind w nonce n).getD b ByteArray.empty =
      blockW h lab rho i msg kind w nonce b := by
  have s := fetchFrom_spec h lab rho i msg kind w nonce ((n + 1) / 2) 0 #[] rfl
    (fun b hb => absurd hb (Nat.not_lt_zero _))
  rw [← s.2 b (by omega)]
  show ((fetchFrom (m := Id) h lab rho i msg kind w nonce ((n + 1) / 2) 0 #[]).extract 0 n).getD
      b ByteArray.empty = _
  have hb' : b < (fetchFrom (m := Id) h lab rho i msg kind w nonce ((n + 1) / 2) 0 #[]).size := by
    rw [s.1]; omega
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_extract_of_lt (by omega), Array.getElem?_eq_getElem hb']
  simp only [Nat.zero_add]

end

end Fmt
