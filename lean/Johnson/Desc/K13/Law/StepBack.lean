-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/StepBack.lean: the step back from (Eval), free of any chain's record: of a row
on the matrix, the row (Eval) that is made of it, words, and a matrix, row weights and a vector
given by numbers. Statements with their proofs.
It stands over Johnson/Desc/K13/Law/EvalProofs.lean alone.
Main names:
  `matBy k T`: the matrix whose entry at row i and at a column's bits b is T i (the number of b).
  `matBy_congr`: it reads T at the rows below nR and the columns below 2^k alone.
  `wis_by_numbers`: "W's message holds g^T M" (`WIs`) out of three sentences with numbers: the
    vector V lies in W's message; V c is the sum over the rows y below nR of g y times T y c; g y is
    the sum of the claim's vectors' entries at y.
  `EvalAt`, `EvalAt.Ok`: the row on the matrix, W's number and layout, the row (Eval) and the
    statement, as one record; and the three public facts that `eval_back` asks of them.
  `stepBack`: **under these, (Eval) says its claim of the words just if the row on the matrix is
    true of the matrix T and of the words' mask entries.**
  `not_stepBack`: a try: the row "0 = 1" is true of no matrix and no words.
Used of `verify-on-bytes`: `linEvalRow`, `memberClaim`, `Tensor.entry`, as pure functions.

What is not claimed. The three sentences with numbers: they are premises. That a record holds an
`EvalAt` that is `Ok` (Johnson/Desc/K13/Law/Laid.lean: `EvalLaid` says it of the first chain's
record). `wis_by_numbers` says what `wis_of_numbers` (Johnson/Desc/K13/Law/WisOf.lean
[not in this library]) says, with
the weights and the vector as letters; where both stand, one goes. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.EvalProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words Says)

variable {nR : ℕ}

/-- The matrix by numbers. -/
def matBy (k : ℕ) (T : ℕ → ℕ → GE) : Fin nR → (Fin k → Bool) → GE := fun i b => T i (Nat.ofBits b)

/-- It reads T at the rows below nR and the columns below 2^k alone. -/
theorem matBy_congr {k : ℕ} {T T' : ℕ → ℕ → GE} (h : ∀ y < nR, ∀ c < 2 ^ k, T y c = T' y c) :
    matBy (nR := nR) k T = matBy k T' := by
  funext i b
  exact h i i.2 _ (Nat.ofBits_lt_two_pow b)

/-- The number whose bit t is bit t of c is c, for c below 2^k. -/
theorem ofBits_low {k c : ℕ} (hc : c < 2 ^ k) : Nat.ofBits (lowBits k c) = c := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · rw [Nat.testBit_ofBits_lt _ _ hi]
    rfl
  · rw [Nat.testBit_ofBits_ge _ _ (by omega),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))]

/-- **"W's message holds g^T M" out of three sentences with numbers.** -/
theorem wis_by_numbers {k : ℕ} (T : ℕ → ℕ → GE) (g V : ℕ → GE) (m : Words GE) (gs : List Tensor)
    (w : ℕ) (lay : VectorLay)
    (hg : ∀ y < nR, g y = (gs.map fun t => ρg.val (t.entry y)).sum)
    (hvec : ∀ c < 2 ^ k, m w .main (lay.index c) = V c)
    (hV : ∀ c < 2 ^ k, V c = ∑ y ∈ Finset.range nR, g y * T y c) :
    WIs (matBy (nR := nR) k T) m gs w lay := by
  intro e he
  rw [hvec e he, hV e he, ← Fin.sum_univ_eq_sum_range (fun y => g y * T y e) nR]
  refine Finset.sum_congr rfl fun i _ => ?_
  show g i * T i e = weights ρg nR gs i * T i (Nat.ofBits (lowBits k e))
  rw [ofBits_low he, hg i i.2]
  rfl

/-- The row on the matrix, W's number and layout, the row (Eval), the statement. -/
structure EvalAt where
  row : TensorRow
  w : ℕ
  lay : VectorLay
  r : OnBytes.Row
  st : Statement

/-- The three public facts. -/
def EvalAt.Ok (Sh : LinShape) (D : EvalAt) : Prop :=
  Sh.kCol ≤ D.lay.bits ∧ linEvalRow Sh (memberClaim D.row) D.w D.lay = some D.r ∧
    EvalIn D.st D.w D.lay D.row.masks

/-- **The step back from (Eval), and the step forth.** -/
theorem stepBack (Sh : LinShape) (D : EvalAt) (hD : D.Ok Sh) (m : Words GE) (T : ℕ → ℕ → GE)
    (g V : ℕ → GE) (hg : ∀ y < nR, g y = (D.row.g.map fun t => ρg.val (t.entry y)).sum)
    (hvec : ∀ c < 2 ^ Sh.kCol, m D.w .main (D.lay.index c) = V c)
    (hV : ∀ c < 2 ^ Sh.kCol, V c = ∑ y ∈ Finset.range nR, g y * T y c) :
    Says ρg D.st D.r m ↔ Holds ρg (witOf (matBy (nR := nR) Sh.kCol T) m) D.row :=
  eval_back nR Sh D.row D.w D.lay D.r D.st m _ hD.1 hD.2.1 hD.2.2
    (wis_by_numbers T g V m D.row.g D.w D.lay hg hvec hV)

/-- **A try**: the row "0 = 1" is true of no matrix and no words. -/
theorem not_stepBack {k : ℕ} (T : ℕ → ℕ → GE) (m : Words GE) :
    ¬ Holds ρg (witOf (matBy (nR := nR) k T) m) (⟨[], [], [], oneE⟩ : TensorRow) := by
  intro H
  have h : lhs ρg (witOf (matBy (nR := nR) k T) m) (⟨[], [], [], oneE⟩ : TensorRow) =
      ρg.val oneE := H
  have hz : lhs ρg (witOf (matBy (nR := nR) k T) m) (⟨[], [], [], oneE⟩ : TensorRow) = 0 := by
    simp [lhs, weights, formVal, colOf, Alg.mle]
  rw [hz, ρg.one] at h
  exact zero_ne_one h

end VerifiableInference.Desc.K13.Law

