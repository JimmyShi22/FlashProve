-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawBS.lean: from a reader of a row of words to a block sampler: a block of 256 bits is four
words of 64.

This file is about how a round's verifier message is made from blocks of 256 bits. Definitions and
statements (each a `Prop` in `Run.Spec`); the proofs are in Run/DrawBSProofs.lean.
A reader `t : Tr W C` (Run/DrawRow.lean) is a decision tree that takes the next word of a row, one
at a time, and ends with a value in C. Its law `Tr.Good d t K w κ`: t asks for at most K words,
every value has at most w rows of K words, and w · |C| ≤ κ · |W|^K.
A block sampler (`Iop.BS`, Iop/Draw.lean) is a number b of blocks, a function of b blocks, and a
bound w on its fibres. Its law `BS.Good s κ`: no value has more than w tuples of b blocks, and w
times |C| is at most κ times the number of all such tuples. So, if C is finite, one value takes at
most the share κ/|C| of all tuples: κ bounds the bias. `Shape.Draws.Good κ₀`: every round with b
blocks obeys the law with κ = κ₀^b.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The convention: bit 64 j + t of a block is bit t of its word j (j < 4, t < 64), and bit t of a word
has the weight 2^t. With a block given as 32 bytes, bit i being bit (i mod 8), from the lowest, of
byte (i div 8), that is: word j is the bytes 8 j to 8 j + 7, lowest byte first. Whoever turns 32
bytes into 256 bits has to take the same convention.

Main names:
  `rowOf e b u`: the row of 4 b words of b blocks.
  `toBS e d t K w`: the block sampler of the reader t with at most K words: b = ⌈K / 4⌉ blocks; the
    value of t on their row; as the bound on fibres w · (2^64)^(4 b - K), where w bounds the rows
    of K words with one value: the words behind the K-th are never read. It computes.
  `Spec.drawBS_row`: `rowOf e b` is a bijection.
  `Spec.drawBS_good`: `Tr.Good d t K w κ` ⇒ `BS.Good (toBS e d t K w) κ`.
  `Spec.drawBS_pow`: `Tr.Good d t K w (κ₀^n)`, 1 ≤ κ₀ and 4 n ≤ K ⇒
    `BS.Good (toBS e d t K w) (κ₀^b)`.

Why there is no stop: `toBS` sets the fields `z`, `nz` of `Iop.BS` to "never" and 0. These fields
serve an older rule of other programs ("every drawn element of E that is 0 is refused"); the format
that is followed here has no such rule: a drawn element may be 0, and where 0 must not come a draw
of its own avoids it.

Limits: the field `w` of `toBS` is a closed expression in numerals (a product of powers); it is
evaluated when the record is built, though no verifier reads it: for a round with very many draws
that is a large number.
This file does not say which blocks of a round's answer these b blocks are. They are the blocks of
the verifier's message; in the format these begin behind the chain's next value, and behind the
test block too in a round with work: a matter of the wiring, not of the sampler.
It does not say which readers the format has, or their numbers K, w, n: Run/DrawPage.lean.
It does not say that a reader is the function on bytes that runs: Run/DrawTie.lean (there: on
machine words; on the blocks' bytes: `Spec.bs_bytes`, Run/ToyChalLaw.lean).

Terms: lean/GLOSSARY.md.
-/
import Run.DrawRow

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

/-- 64 bits are a number below 2^64: bit t has the weight 2^t -/
def eFin64 : Dig 64 ≃ Fin (2 ^ 64) :=
  (Equiv.piCongrRight fun _ : Fin 64 => finTwoEquiv.symm).trans
    (finFunctionFinEquiv (m := 2) (n := 64))

/-- 64 bits are a machine word. -/
def e64 : Dig 64 ≃ UInt64 := eFin64.trans ⟨UInt64.ofFin, UInt64.toFin, fun _ => rfl, fun _ => rfl⟩

/-- The machine words are finitely many.
The two marks are for compiled programs; they change no term. Before `main`, a compiled program
runs the start-up code of every module that it imports, and this module's would compute this
instance: the list of all 2^64 words. The program would run out of memory.
`noncomputable`: Lean makes no code for this name, so there is nothing to compute at the start.
`macro_inline`: a definition that names the instance is compiled with the right-hand side written
in its place, so `fintypeDVal` (Run/PlanDraws.lean) and all that uses it keep their code. There
Lean 4.29 computes the list only if a run reaches it; none should.
Without the marks the library still builds, and every program that imports this module dies as it
starts. -/
@[macro_inline] noncomputable instance fintypeWord : Fintype UInt64 := Fintype.ofEquiv _ e64

section
variable {W C : Type}

/-- Word j of a block: its bits 64 j to 64 j + 63. -/
def wordBits (x : Dig 256) (j : Fin 4) : Dig 64 := fun t => x ⟨64 * j.val + t.val, by omega⟩

/-- The row of words of b blocks. -/
def rowOf (e : Dig 64 ≃ W) (b : ℕ) (u : Fin b → Dig 256) : Fin (4 * b) → W :=
  fun i => e (wordBits (u ⟨i.val / 4, by omega⟩) ⟨i.val % 4, by omega⟩)

/-- The block sampler of a reader. d is the word that `Tr.ev` takes where a reader asks beyond the
end of the row. -/
def toBS (e : Dig 64 ≃ W) (d : W) (t : Tr W C) (K w : ℕ) : BS 256 C :=
  ⟨(K + 3) / 4, fun u => t.ev d (4 * ((K + 3) / 4)) (rowOf e ((K + 3) / 4) u),
    w * (2 ^ 64) ^ (4 * ((K + 3) / 4) - K), fun _ => false, 0⟩

end

namespace Spec

def drawBS_row : Prop := ∀ (W : Type) (e : Dig 64 ≃ W) (b : ℕ), Function.Bijective (rowOf e b)

/-- The same bias. -/
def drawBS_good : Prop :=
  ∀ (W C : Type) [Finite W] (e : Dig 64 ≃ W) (d : W) (t : Tr W C) (K w : ℕ) (κ : ℝ≥0∞),
    t.Good d K w κ → (toBS e d t K w).Good κ

/-- The clause of `Shape.Draws.Good`. -/
def drawBS_pow : Prop :=
  ∀ (W C : Type) [Finite W] (e : Dig 64 ≃ W) (d : W) (t : Tr W C) (K w n : ℕ) (κ₀ : ℝ≥0∞),
    1 ≤ κ₀ → 4 * n ≤ K → t.Good d K w (κ₀ ^ n) → (toBS e d t K w).Good (κ₀ ^ (toBS e d t K w).b)

end Spec
end Run
