-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/BatchVQueriesDraw.lean: a bound on the number `cVBN` (Compile/Batch/NeedCost.lean) at the wire
  records of Iop/BatchWireDraw.lean, where challenge samplers derive the challenges from hash
  blocks; `cVBN` bounds the marked blocks of the verifier's typed queries (by which theorems and for
  which query encodings: below). Marked: in Rom/OverOneN.lean a query to a typed oracle becomes
  queries to the one oracle f only for the hash blocks of the answer that a function of the query
  (`Need`) marks.
  Beside Top/BatchVQueriesN.lean.
    `cVBN_ofDraws_le`:
        cVBN (QueryLayout.ofDraws ..) (nbD dr) ≤ blocksD dr + opensOf + (depthReq + 2); `opensOf`:
        Top/BatchVQueriesN.lean.
  With `costBoundAt_V` (Compile/Batch/NeedCost.lean) and `costBoundAt_V_argP`
  (Compile/Batch/NeedP.lean) this bounds the marked blocks of V's queries, for a query encoding with
  `Std`. A bound on the number of V's queries to f (`QueryBound`), for the schemes of
  Compile/Batch/NeedP.lean and Compile/Batch/NeedL.lean, is not in this library.
  (Terms: lean/GLOSSARY.md.)

  Notation: `nbD dr`: the number of blocks that round i of protocol t needs: that of its sampler
  (Compile/Batch/NeedDraws.lean); `blocksD dr`: the part of the Fiat-Shamir chains; `opensOf`: the
  part of the openings in the bound (Top/BatchVQueriesN.lean); depthReq: the depth of a request tree
  (`QueryLayout.depthReq`, Iop/BatchWire.lean).

  Limits: No numeral. For a sampler that rejects and samples again, all its attempts are counted.
-/
import Top.BatchVQueriesN
import Compile.Batch.NeedDraws

set_option autoImplicit false

noncomputable section

namespace Top.Batch
open Iop Rom Compile Compile.Batch Compile.Batch.Need Blocks

theorem maxDepth_ofLocalD_le (lam K : ℕ) :
    ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts),
      RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) ≤ depths s pts
  | [], _, _, _ => Nat.le_refl _
  | _ :: s, (_, pts), (_, ds), (_, nps) =>
    max_le_max (max_le (Nat.zero_le _) (Nat.le_refl _)) (maxDepth_ofLocalD_le lam K s pts ds nps)

theorem maxDepth_ofDraws_le (lam K : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPosB A pts),
      RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) ≤ depths s pts
  | [], _, _, _, _ => Nat.le_refl _
  | r :: s, (a, A), (pt, pts), (_, ds), (_, _, nps) => by
      letI := pt.finPos
      exact max_le_max
        (max_le (Nat.clog_mono_right 2 (Fintype.card_subtype_le _))
          (Nat.clog_mono_right 2 (Fintype.card_subtype_le _)))
        (maxDepth_ofDraws_le lam K s A pts ds nps)

variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (dr : L.Draws lam) (ax : L.Aux pT pL pB)

/-- The part of the openings (`cOpens`, Compile/Batch/NeedCost.lean) at `QueryLayout.ofDraws ..` is at
most `opensOf`. -/
theorem cOpens_ofDraws_le :
    cOpens (QueryLayout.ofDraws lam L pT pL pB z no dr ax) ≤ opensOf L pT pL pB no :=
  Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left _
        (Nat.add_le_add_right
          (max_le_max (Nat.le_refl _) (maxDepth_ofLocalD_le lam dr.K L.offline.shape pT dr.T ax.posT))
          1))
      (Nat.mul_le_mul_left _
        (Nat.add_le_add_right
          (max_le_max (Nat.le_refl _) (maxDepth_ofLocalD_le lam dr.K L.link.shape pL dr.Lk ax.posL))
          1)))
    (Nat.mul_le_mul_left _
      (Nat.add_le_add_right
        (max_le_max (Nat.le_refl _)
          (maxDepth_ofDraws_le lam dr.K L.onlineBatch.loc.shape L.onlineBatch.ann pB dr.B ax.posB)) 1))

variable {lam L}

/-- The part of the Fiat-Shamir chains: the blocks of all samplers, and a chaining value for each
round. -/
def blocksD (dr : L.Draws lam) : ℕ :=
  (Shape.Draws.totB _ dr.T + L.offline.shape.length) +
    (Shape.Draws.totB _ dr.Lk + L.link.shape.length) +
    (Shape.Draws.totB _ dr.B + L.onlineBatch.loc.shape.length)

variable (lam L)

/-- The verifier's count (`cVBN`) at the wire records of the challenge samplers
(`QueryLayout.ofDraws`). -/
theorem cVBN_ofDraws_le :
    cVBN (QueryLayout.ofDraws lam L pT pL pB z no dr ax) (nbD dr) ≤
      blocksD dr + opensOf L pT pL pB no + (ax.depthReq + 2) := by
  rw [cVBN_eq, cChain_nbD]
  exact Nat.add_le_add_right (Nat.add_le_add_left (cOpens_ofDraws_le lam L pT pL pB z no dr ax) _) _

end Top.Batch
