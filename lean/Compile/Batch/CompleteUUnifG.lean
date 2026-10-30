-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUUnifG.lean: under lazily sampled oracles and the hypotheses of `Spec.unifBUG`
(Compile/Batch/SpecCompleteUG.lean: `L.PropsNoAcc`, `W.OKG`, `GrFitB`, `WP.OK`, `Fmt`, and request
number a is x, in `Ryes i`), the small experiment of the prover with free empty slots (`RBU`,
Compile/Batch/CompleteURefDefs.lean) shows "bad" (`none`, or a failed search) with probability at
most `M.pO` + `cFail` (Compile/Batch/SpecGrind.lean: the sum, over the rounds, of the probabilities
that a search fails). For wire records that may have proof-of-work bits (words of this library:
lean/GLOSSARY.md). Towards completeness of the compiled scheme.

  `pr_badAtUG`  One execution (`proveOU`), for a slot with a request, under the hypotheses below: at
                most the probability of the withheld set, plus `cFail`.
  `unifBUG`  It proves `Spec.unifBUG` (Compile/Batch/SpecCompleteUG.lean).

The proof: the hash blocks of a slot with a request are independent, each with the distribution of
its round (`blocks_proveOUG`, `pr_noneAtUG` of Compile/Batch/CompleteUUnif.lean); under that
distribution some proof-of-work check fails with probability at most `cFail` (`pr_pass_ublkG` of
Compile/Batch/CompleteUnifG.lean: each search's probability exact, then a union bound). Then a union
bound over `none` and a failed search.

Notation: free empty slots (lean/GLOSSARY.md): `argBU` (Compile/Batch/StarU.lean), the compiled
scheme without queries for empty slots; `RBU` (Compile/Batch/CompleteURefDefs.lean): a fresh node
and one batch on it; a node (`nodeO`, Compile/Batch/CompleteRefDefs.lean): a fresh encoding of i and
the root of its tree; `M.pO`: a field of `M`, an `LH.Nums` (Iop/InteractiveOracleProof.lean: all numbers of the
interface), in ℝ≥0∞; the withheld set: `Honest.withheld` (Iop/InteractiveOracleProof.lean).
-/
import Compile.Batch.CompleteUnifG
import Compile.Batch.CompleteUUnif
import Compile.Batch.SpecCompleteUG

noncomputable section

namespace Compile.Batch
open Iop Rom Prob Ref RefU CompleteUnif CompleteUnifG CompleteUUnif
open scoped ENNReal

namespace CompleteUUnifG

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

/-- `none`, or a failed search, for a slot with a request. -/
theorem pr_badAtUG (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hE : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh ∨ Function.Injective embP) (hF : Q.ann.Fmt)
    (xs : List (Option Y)) (n : ℕ) (x : Y) (hn : xs[n]? = some (some x))
    (hwh : ∀ ρ, ρ ∈ H.one.withheld w x ↔ RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ H.one.withheld w x)
    (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    pr (((proveOU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | badAt Q H wq wp w x n bss = true} ≤
      prRho (H.one.withheld w x) + cFail Q.loc.shape Q.ann wq.sh := by
  have e : {bss : List (List (Blk lam K)) | badAt Q H wq wp w x n bss = true} =
      {bss | noneAt Q H wq wp w x n bss = true} ∪
        {bss | RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n [])) =
          false} := by
    ext bss
    simp only [badAt, Set.mem_setOf_eq, Set.mem_union, Bool.or_eq_true, Bool.not_eq_true']
  rw [e]
  refine (pr_union_le _ _ _).trans
    (add_le_add
      (le_of_eq
        (pr_noneAtUG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW hE hF xs n x hn hwh T hT))
      ?_)
  have h := blocks_proveOUG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW hE hF xs n x hn T hT
  have e2 : pr
        (((proveOU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n [])) =
          false} =
      pr (ublkG Q.loc.shape Q.ann wq.sh)
        {l | RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh l) = false} := by
    rw [← h, pr_map, pr_map]
    rfl
  rw [e2]
  exact pr_pass_ublkG _ _ _ hW

end Prove

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (i : I) {Ryes : I → X → Prop}

theorem pr_batOUG (hW : W.OKG) (hG : GrFitB W Ryes) (hF : L.onlineBatch.ann.Fmt) (xs : List X)
    (a : Fin L.maxBatchSize) (x : X) (hx : xs[a.val]? = some x) (nd : L.EncodingRandomness × Dig lam)
    (T : Table (spec lam W.K L)) (hT : FbLt Tag.onl 0 T) :
    pr (((batOU W WP p i xs a x nd).runLazy T).map Prod.fst) {b | b = true} ≤
      prRho (L.honestOnlineBatchProver.one.withheld (i, nd.1) x) + cFail L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh := by
  unfold batOU
  refine pr_bind_le _ _ _ _ _ fun y hy => ?_
  rw [pr_bind_pure]
  exact pr_badAtUG p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [nd.2] (i, nd.1)
    hW.B.sh (Or.inr Function.injective_id) hF (slotsOfReq y.1 xs) (y.1 a).val x
    (by rw [Cmpl.getElem?_slotsOfReq, hx]) (hG.B.wh _ _) y.2
    (FbLt.of_notFb (onlyQ_drawO Tag.onl WP.perm) hT y hy)

end Scheme

end CompleteUUnifG

open CompleteUUnifG

/-- Under the hypotheses of `Spec.unifBUG`: the small experiment of the prover with free empty slots
shows "bad" with probability at most pO + cFail. -/
theorem unifBUG : Spec.unifBUG := by
  intro I X lam L W WP p Ryes Rno M h hW hG _ hF i xs a x hxa hx
  exact pr_bind_le _ _ _ _ _ fun y hy =>
    (pr_batOUG W WP p i hW hG hF xs a x hxa y.1 y.2
        (FbLt.of_notFb (onlyQ_nodeO W WP p i Tag.onl) (fbLt_empty _) y hy)).trans
      (add_le_add (h.prB _ _ hx) le_rfl)

end Compile.Batch
