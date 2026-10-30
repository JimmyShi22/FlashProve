-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/MaskChunks.lean: a set of numbered positions as an array of small masks, for a test
that costs the same at every position. Definitions that compute; one law. General. The compiler
under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.
Why. The library's maskOf | maskBit (Run/ThinExtReads.lean) turn the set of external positions read
into one number and test a position by Nat.testBit: which shifts the whole number: at two tables of
depth 23 a number of 2 MB, at each of 16.8 million positions. The evaluable verifiers ask of (mk,
tst) only "tst (mk R) p = true ↔ p ∈ R" (thin_ext's and lax_thin's hypothesis).
  chunks B n m  the number m cut into n numbers of B bits: n shifts, once. The low B bits are taken
      by "&&& (2 ^ B - 1)", not "% 2 ^ B": a division of a number of 2 MB,
      4,097 times: 30.8 s at depth 23
  chunkBit B M i  bit i: chunk i / B, its bit i % B: an array's look-up and a testBit in a number of
      B bits
  chunkBit_eq  0 < B, i < n * B ⇒ chunkBit B (chunks B n m) i = m.testBit i
  mkC idx B n, tstC idx B, tstC_eq  at a one-to-one numbering below n * B: tstC idx B (mkC idx B n
      R) p = true ↔ p ∈ R
What is not said. Any time. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.ThinExtReads

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open _root_.Run.Thin (maskOf maskBit maskBit_eq)

/-- a number cut into n numbers of B bits -/
def chunks (B n m : ℕ) : Array ℕ :=
  let low := 2 ^ B - 1
  Array.ofFn (n := n) fun c => (m >>> (c.val * B)) &&& low

/-- bit i of the number that was cut -/
def chunkBit (B : ℕ) (M : Array ℕ) (i : ℕ) : Bool := (M.getD (i / B) 0).testBit (i % B)

theorem chunkBit_eq {B n : ℕ} (hB : 0 < B) (m i : ℕ) (h : i < n * B) :
    chunkBit B (chunks B n m) i = m.testBit i := by
  have hq : i / B < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  have hg : (chunks B n m).getD (i / B) 0 = (m >>> (i / B * B)) % 2 ^ B := by
    unfold chunks
    simp [Array.getD, hq, Nat.and_two_pow_sub_one_eq_mod]
  unfold chunkBit
  rw [hg, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true (Nat.mod_lt i hB),
      Bool.true_and,
    Nat.div_add_mod' i B]

variable {α : Type} (idx : α → ℕ)

def mkC (B n : ℕ) (R : Finset α) : Array ℕ := chunks B n (maskOf idx R)
def tstC (B : ℕ) (M : Array ℕ) (p : α) : Bool := chunkBit B M (idx p)

/-- The law that the evaluable verifiers ask. -/
theorem tstC_eq [DecidableEq α] (hi : Function.Injective idx) {B n : ℕ} (hB : 0 < B)
    (hb : ∀ p, idx p < n * B)
    (R : Finset α) (p : α) : tstC idx B (mkC idx B n R) p = true ↔ p ∈ R := by
  unfold tstC mkC
  rw [chunkBit_eq hB _ _ (hb p)]
  exact maskBit_eq idx hi R p

end TypedOracleCompiler.Run.Thin
