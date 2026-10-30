-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Work.lean: an equation between terms, for a wire with proof of work (`QueryLayout.grind`).
What work adds to ζ (`zetaBGen`, Compile/Batch/SpecHop.lean), at the hash term with the vertices at
2 λ (CompileK/Defer2Cost.lean: `hashTerms2`): the same one term `sqWork` as at `hashTermsBGTot`.
(not all hypotheses are named here: see `Spec.zeta_work2`)

`muB2_grind`, `hashSq_work2`, `hashTerms_work2`, `Spec.zeta_work2` with its proof: the analogues of
`muB_grind` (Compile/Batch/TotalAtGrind.lean) and of `hashSq_work`, `hashTerms_work`, `zeta_work`
(CompileK/GrindCost.lean, which defines `sqWork`). Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.

Notation: `L`: `BatchProtocol I X` (Iop/Batch.lean): an interface with batches; `Wr`: `QueryLayout lam L`
(Iop/BatchWire.lean): a wire of `L`; `Wr.OK` is `QueryLayout.OK`; `gT`, `gL`, `gB`: `GBits` of
`L.offline.shape`, `L.link.shape`, `L.onlineBatch.loc.shape` (Iop/GBits.lean): for each round a number of test
bits; `Dg`: `GrData Nn` (Iop/GrindWire.lean): what the wire adds to the numbers of test bits; `t`: a
natural number; in the doc comment of `Spec.zeta_work2`: the adversary's number of queries; `n`: a
natural number; in the head of CompileK/GrindCost.lean: setup and n batches.

Limits: what the head of CompileK/GrindCost.lean lists as not said is not said here either.
-/
import CompileK.Defer2Cost
import CompileK.GrindCost

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cost
open Iop Compile Compile.Batch
open scoped ENNReal

variable {Nn : Type} [Inhabited Nn] {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (Wr : QueryLayout lam L)
  (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
  (gB : GBits L.onlineBatch.loc.shape) (p : Params)

theorem muB2_grind (n : ℕ) : muB2 (Wr.grind Dg gT gL gB) p n = muB2 Wr p n := by
  unfold muB2
  rw [xTree_grind Wr Dg gT gL gB p n, xFb_grind]
  rfl

theorem hashSq_work2 (hW : Wr.OK) (n : ℕ) :
    hashSqBG2 (Wr.grind Dg gT gL gB) p n = hashSqBG2 Wr p n + sqWork Wr Dg gT gL gB p n := by
  have e : xReq (L.grind Nn gT gL gB) n = xReq L n := rfl
  unfold hashSqBG2 sqWork
  rw [xTree_grind, xFb_grind, xGr_of_ok hW, e, Nat.cast_zero, zero_mul, ENNReal.zero_div, add_zero]
  abel

theorem hashTerms_work2 (hW : Wr.OK) (t n : ℕ) :
    hashTerms2 (Wr.grind Dg gT gL gB) p t n = hashTerms2 Wr p t n + sqWork Wr Dg gT gL gB p n := by
  unfold hashTerms2
  rw [muB2_grind, hashSq_work2 Wr Dg gT gL gB p hW, add_assoc]

/-- States, under the hypotheses below: privacy: work adds one term, which does not depend on the
adversary's number of queries. -/
def Spec.zeta_work2 : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L)
      (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (p : Params),
    Wr.OK → ∀ (M : LH.Nums) (t n : ℕ),
      zetaBGen (L.grind Nn gT gL gB) p M (hashTerms2 (Wr.grind Dg gT gL gB) p) t n =
        zetaBGen L p M (hashTerms2 Wr p) t n + sqWork Wr Dg gT gL gB p n

theorem zeta_work2 : Spec.zeta_work2 := by
  intro Nn _ I X lam L Wr Dg gT gL gB p hW M t n
  have e : zetaBGen (L.grind Nn gT gL gB) p M = zetaBGen L p M := rfl
  rw [e]
  unfold zetaBGen
  rw [hashTerms_work2 Wr Dg gT gL gB p hW]
  abel

end Compile.Batch.Cost
