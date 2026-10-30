-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/FlagsFree.lean: the bounds on queries named below and the binding bound ε do not
depend on the flags for pruned Merkle paths. For a wire record W and flags F (`W.setPr F`,
Iop/BatchWirePr.lean):
    `cTrees_setPr`, `xTree_setPr`      bounds on the honest parties' queries for trees
    `tVB_setPr`, `epsB_setPr`          the bound on V's queries, and ε (by definition)
(Under `W.OK` α = `alphaB L M`, which does not depend on the wire record at all.) So an explicit
bound on α (under `W.OK`) or ε for a wire record holds for the same wire record with flags. (α, ε,
ζ: the bounds of the compiler's theorem: the arguments of `IsZKCPArgWith`, ZKCP/Gen.lean; its α is
`alphaBG W M` (Compile/Batch/SpecGrind.lean), which is `alphaB L M` under `W.OK`: `alphaBG_of_ok`,
CompileK/Counts.lean.) This ε is `epsB W M` (Compile/Batch/SpecBinding.lean), a formula in a number
that a record of numbers lists (the data field `LH.Nums.εs`, Iop/InteractiveOracleProof.lean): that the protocols are
sound at the number that the record lists is no statement of this file; in `bindingBatchG`
(Compile/Batch/BindingG.lean) it is a hypothesis (the field `sound` of `L.PropsNoAcc Ryes Rno M`).
Limits: the same is not proved here for ζ: that ζ does not depend on the flags is neither stated nor
proved in this library.
-/
import Compile.Batch.Counts
import Compile.Batch.Spec
import Compile.Batch.SpecBinding
import Iop.BatchWirePr

noncomputable section

namespace Compile.Batch
open Iop
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem cTrees_setPr {K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (fl : OpenList s) (Ns : ℕ),
      cTrees s A (RoundsQueryLayout.setPr s A W fl) Ns = cTrees s A W Ns
  | [], _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), (_, fs), Ns =>
    congrArg (Ns * 2 ^ w.depthJ + 2 ^ w.depth0 + ·) (cTrees_setPr s A W fs Ns)

variable (W : QueryLayout lam L) (F : PrFlags L) (p : Params)

theorem xTree_setPr (n : ℕ) : xTree (W.setPr F) p n = xTree W p n := by
  show (p.leaves + 1) * 2 ^ W.depth + cTrees L.offline.shape _ (RoundsQueryLayout.setPr _ _ W.T.sh F.T) 1 +
      p.leaves * cTrees L.link.shape _ (RoundsQueryLayout.setPr _ _ W.Lk.sh F.Lk) 1 +
      n * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann (RoundsQueryLayout.setPr _ _ W.B.sh F.B) L.maxBatchSize = _
  rw [cTrees_setPr, cTrees_setPr, cTrees_setPr]
  rfl


theorem tVB_setPr : tVB (W.setPr F) = tVB W := rfl

/-- ε does not depend on the flags. -/
theorem epsB_setPr (M : LH.Nums) : epsB (W.setPr F) M = epsB W M := rfl

end Compile.Batch
