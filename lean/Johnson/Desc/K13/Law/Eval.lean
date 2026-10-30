-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Eval.lean: the row (Eval) that kind K13 lays behind W's commitment, and the
claim's row. Definitions, and statements as definitions of propositions; the proofs are in
Johnson/Desc/K13/Law/EvalProofs.lean.

The claim's row speaks of the stored matrix M: < g (x) eq(psi, .), M > + a mask form = a target. The
prover sends a vector W, said to be g^T M. The row (Eval) speaks of W alone: < eq(psi, .), W > + the
mask form = the target. What a row says of words is not restated here: `OnBytes.Means.Says`.
Main names:
  `maskOf`, `witOf`: the mask entries off the words; a matrix with them.
  `lowBits`, `WIs`: W's message, read through its layout, holds g^T M.
  `EvalIn`: the row's summands lie on tables that the statement has, and within them.
  `Spec.eval_value`: what (Eval) is worth on words. `Spec.eval_back`: under `WIs`, (Eval) says its
    claim of the words exactly if the claim's row is true.
  `sum_lowBits`.
Used of `verify-on-bytes`, pure functions: `linEvalRow`, `memberClaim`, `VectorLay.index`.

What is not claimed. `WIs` is a premise, and nothing here or in this folder gives it. It is meant
to come from the law of the test on the stored table (the rows on the folded row and on Omega, the
row (Dot), and a count at the shared point, before which W is fixed): not proved by anybody yet.

-/
import Johnson.Desc.K13.Law.View
import Johnson.Desc.Means.Says
import OnBytes.Slice.BlkLinRead
import OnBytes.Slice.BlkCross

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words Says value tableSize)
open Johnson.L5.Layers (rd)

variable {nR k : ℕ}

/-- The mask entries, off the words. -/
def maskOf (m : Words GE) : Slot → GE := fun s => m s.oracle .mask s.index

/-- A matrix, with the mask entries off the words. -/
def witOf (mat : Fin nR → (Fin k → Bool) → GE) (m : Words GE) : Wit GE nR k := ⟨mat, maskOf m⟩

/-- The column with the number e: bit t of e is coordinate t. -/
def lowBits (k e : ℕ) : Fin k → Bool := fun t => e.testBit t

/-- **W's message holds g^T M**: entry e of the vector that lies in the main table of the oracle
message w, under the layout lay, is the combination of the matrix's rows at the column e. -/
def WIs (mat : Fin nR → (Fin k → Bool) → GE) (m : Words GE) (g : List Tensor) (w : ℕ)
    (lay : VectorLay) : Prop :=
  ∀ e < 2 ^ k, m w .main (lay.index e) = ∑ i, weights ρg nR g i * mat i (lowBits k e)

/-- The row's summands lie on tables that the statement has, and within them. -/
structure EvalIn (St : Statement) (w : ℕ) (lay : VectorLay) (masks : MaskForm) : Prop where
  there : w < St.oracles.size
  size : tableSize St w .main = 2 ^ lay.bits
  masks : ∀ t ∈ masks, t.1.oracle < St.oracles.size ∧ t.1.index < tableSize St t.1.oracle .mask

namespace Spec

/-- What the row (Eval) is worth on words. -/
def eval_value : Prop :=
  ∀ (S : LinShape) (row : TensorRow) (w : ℕ) (lay : VectorLay) (r : OnBytes.Row) (St : Statement)
    (m : Words GE), S.kCol ≤ lay.bits → linEvalRow S (memberClaim row) w lay = some r →
    EvalIn St w lay row.masks →
    value ρg St r m =
      (∑ e ∈ Finset.range (2 ^ S.kCol),
        Alg.eqk (rd ρg S.kCol row.psi) (lowBits S.kCol e) * m w .main (lay.index e)) +
      formVal ρg (maskOf m) row.masks

/-- **Where (Eval) says its claim of the words and W's message holds g^T M, the claim's row is
true** of the matrix and of the words' mask entries; and the other way round. -/
def eval_back : Prop :=
  ∀ (nR : ℕ) (S : LinShape) (row : TensorRow) (w : ℕ) (lay : VectorLay) (r : OnBytes.Row)
    (St : Statement) (m : Words GE) (mat : Fin nR → (Fin S.kCol → Bool) → GE), S.kCol ≤ lay.bits →
    linEvalRow S (memberClaim row) w lay = some r → EvalIn St w lay row.masks →
    WIs mat m row.g w lay → (Says ρg St r m ↔ Holds ρg (witOf mat m) row)

end Spec

/-- A sum over the numbers below 2^k, by their bits, is the sum over the vertices of the cube. -/
theorem sum_lowBits {M : Type} [AddCommMonoid M] (k : ℕ) (F : (Fin k → Bool) → M) :
    ∑ e ∈ Finset.range (2 ^ k), F (lowBits k e) = ∑ b, F b := by
  rw [← Alg.sum_num fun c => F (lowBits k c)]
  refine Fintype.sum_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl Bool)) _ _ fun b => ?_
  congr 1
  funext t
  have h := congrFun (Alg.bits_num b) (Fin.rev t)
  unfold Alg.bits at h
  have e : k - 1 - ((Fin.rev t : Fin k) : ℕ) = t := by
    rw [Fin.val_rev]
    omega
  rw [e] at h
  simpa [lowBits, Equiv.arrowCongr] using h

end VerifiableInference.Desc.K13.Law
