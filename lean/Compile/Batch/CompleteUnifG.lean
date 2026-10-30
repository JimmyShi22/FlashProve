-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUnifG.lean: under lazily sampled oracles each of the small experiments `RT`,
`RL` (Compile/Batch/CompleteRefDefs.lean) ends in "bad" with probability at most `M.pT` or `M.pL`
(bounds on the probability of the withheld set) plus the sum of the probabilities that a search
fails (words of this library: lean/GLOSSARY.md). Towards completeness of the compiled scheme whose
rounds may have proof-of-work bits.

The proofs of `Spec.unifTG`, `Spec.unifLG` (Compile/Batch/SpecCompleteG.lean; hypotheses
`L.PropsNoAcc`, `W.OKG`, `GrFitB`, `WP.OK`), from `blocks_proveOG` and `pr_noneAtG`
(Compile/Batch/CompleteUnif.lean).

  `pr_gblk_fail`, `pr_rblk_fail`  One round with b proof-of-work bits, under the hypotheses below:
                                  the final attempt fails its check with probability exactly (1 -
                                  2^-b)^(`more` + 1) (`Prob.pr_retry_fail`,
                                  `Compile.Batch.ok_share`); 0 in a round without such bits.
  `pr_pass_ublkG`  One slot's transcript, under `RoundsQueryLayout.OKG`: some proof-of-work bit is 1 with
                   probability at most `cFail`: a union bound over the rounds.
  `pr_badAtG`  `none`, or a failed search ("bad"), under the hypotheses below: at most `prRho` of
               the withheld set plus `cFail`.
  `pr_testOG`, `pr_linkOG`, `unifTG`, `unifLG`  The two experiments; the two statements.

Up to `pr_testOG` and `pr_linkOG` the only inequalities are the union bounds (over the rounds; over
`none` and a failed search: `badAt`). `unifTG` and `unifLG` then bound the probability of the
withheld set by `M.pT` and `M.pL`.

Limits: what the head of Compile/Batch/SpecCompleteG.lean lists as not said is not said here either.
-/
import Compile.Batch.CompleteUnif
import Compile.Batch.SpecCompleteG
import Compile.Batch.LoopLaw

noncomputable section

namespace Compile.Batch
open Iop Rom Prob Ref CompleteUnif
open scoped ENNReal

namespace CompleteUnifG

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## One round, one slot's transcript -/

/-- The final attempt of a search fails its check with probability exactly (1 - 2^-b)^(more + 1),
under the hypotheses below; there is no check to fail without a record `GrW`. ps: the check, as the
wire record states it -/
theorem pr_gblk_fail {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG) {P : Type}
    (gr : Option (GrW r.Chal P)) (hg : ∀ g, gr = some g → g.OK) (ps : r.Chal → Bool)
    (h0 : gr = none → ∀ c, ps c = true) (h1 : ∀ g, gr = some g → ∀ c, ps c = g.ok c) :
    pr (gblk gr w.chal) {bl | ps (w.chal bl) = false} = failOf gr := by
  cases gr with
  | none =>
      show _ = (0 : ℝ≥0∞)
      refine pr_eq_zero_of_forall_not_mem _ fun bl _ h => ?_
      rw [Set.mem_setOf_eq, h0 rfl] at h
      cases h
  | some g =>
      show pr
          ((retry (fun x : (Fin K → Dig lam) × Dig lam => g.ok (w.chal x.1)) g.more).map Prod.fst)
          {bl | ps (w.chal bl) = false} = grFail g
      rw [pr_map]
      have e : (Prod.fst ⁻¹' {bl | ps (w.chal bl) = false} : Set ((Fin K → Dig lam) × Dig lam)) =
          {x | g.ok (w.chal x.1) = false} := Set.ext fun x => by
        show ps (w.chal x.1) = false ↔ g.ok (w.chal x.1) = false
        rw [h1 g rfl]
      rw [e, pr_retry_fail, ok_share lam K r a w P g hw (hg g rfl)]
      rfl

theorem pr_rblk_fail {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG) :
    pr (rblk a w) {bl | w.pass (w.chal bl) = false} =
      (match a.kind with | .lo => failOf w.grJ | .sh => failOf w.gr0) := by
  unfold rblk
  cases hk : a.kind with
  | lo =>
    exact pr_gblk_fail w hw w.grJ hw.grJ_ok w.pass
      (fun h c => by unfold WireRB.pass; rw [hk]; simp only [h])
      (fun g h c => by unfold WireRB.pass; rw [hk]; simp only [h])
  | sh =>
    exact pr_gblk_fail w hw w.gr0 hw.gr0_ok w.pass
      (fun h c => by unfold WireRB.pass; rw [hk]; simp only [h])
      (fun g h c => by unfold WireRB.pass; rw [hk]; simp only [h])

/-- Under `RoundsQueryLayout.OKG`, some proof-of-work bit of a slot's transcript is 1 with probability at most
the sum of the probabilities that a search fails. -/
theorem pr_pass_ublkG :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      pr (ublkG s A W) {l | RoundsQueryLayout.pass s A W (rhoOf s A W l) = false} ≤ cFail s A W
  | [], _, _, _ => by
      refine le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => ?_)
      cases h
  | r :: s, (a, A), (w, W), hW => by
      show pr ((rblk a w).bind fun bl => (ublkG s A W).map fun l => bl :: l) _ ≤
        (match a.kind with | .lo => failOf w.grJ | .sh => failOf w.gr0) + cFail s A W
      rw [← pr_rblk_fail w hW.1]
      refine pr_bind_le_add _ _ _ _ fun bl _ hbl => ?_
      rw [pr_map]
      refine le_trans (le_of_eq (congrArg _ (Set.ext fun l => ?_))) (pr_pass_ublkG s A W hW.2)
      have hb : w.pass (w.chal bl) = true := by
        cases h : w.pass (w.chal bl)
        · exact absurd h hbl
        · rfl
      show (w.pass (w.chal bl) && RoundsQueryLayout.pass s A W (rhoOf s A W l)) = false ↔
        RoundsQueryLayout.pass s A W (rhoOf s A W l) = false
      rw [hb, Bool.true_and]

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

/-- `none`, or a failed search. -/
theorem pr_badAtG (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hE : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh ∨ Function.Injective embP) (hF : Q.ann.Fmt)
    (xs : List (Option Y)) (n : ℕ) (hn : n < xs.length) (x : Y)
    (hwh : ∀ ρ, ρ ∈ H.one.withheld w x ↔ RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ H.one.withheld w x)
    (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    pr (((proveO sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
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
        (pr_noneAtG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW hE hF xs n hn x hwh T hT))
      ?_)
  have h := blocks_proveOG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW hE hF xs n hn T hT
  have e2 : pr
        (((proveO sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n [])) =
          false} =
      pr (ublkG Q.loc.shape Q.ann wq.sh)
        {l | RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh l) = false} := by
    rw [← h, pr_map, pr_map]
    rfl
  rw [e2]
  exact pr_pass_ublkG _ _ _ hW

end Prove

/-! ## The two small experiments -/

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (i : I) {Ryes : I → X → Prop}

theorem pr_testOG (hW : W.OKG) (hG : GrFitB W Ryes) (nd : L.EncodingRandomness × Dig lam)
    (T : Table (spec lam W.K L)) (hT : FbLt Tag.test 0 T) :
    pr (((testO W WP p i nd).runLazy T).map Prod.fst) {b | b = true} ≤
      prRho (L.honestOfflineProver.withheld (i, nd.1) ()) + cFail L.offline.shape _ W.T.sh := by
  unfold testO
  rw [pr_bind_pure, ← BatchOne.ofHonest_withheld]
  exact pr_badAtG p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver)
    W.T WP.T _ id _ W.depthReq [nd.2] (i, nd.1) hW.T.sh (Or.inr Function.injective_id)
    (RoundSplits.fmt_allLocal _) [some ()] 0 (by simp) () (hG.T.wh _ _) T hT

theorem pr_linkOG (hW : W.OKG) (hG : GrFitB W Ryes) (nd0 nd : L.EncodingRandomness × Dig lam)
    (T : Table (spec lam W.K L)) (hT : FbLt Tag.link 0 T) :
    pr (((linkO W WP p i nd0 nd).runLazy T).map Prod.fst) {b | b = true} ≤
      prRho (L.honestLinkProver.withheld (i, nd0.1, nd.1) ()) + cFail L.link.shape _ W.Lk.sh := by
  unfold linkO
  rw [pr_bind_pure, ← BatchOne.ofHonest_withheld]
  exact pr_badAtG p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk
    WP.Lk _ id _ W.depthReq [nd0.2, nd.2] (i, nd0.1, nd.1) hW.Lk.sh (Or.inr Function.injective_id)
    (RoundSplits.fmt_allLocal _) [some ()] 0 (by simp) () (hG.Lk.wh _ _) T hT

end Scheme

end CompleteUnifG

open CompleteUnifG

theorem unifTG : Spec.unifTG := by
  intro I X lam L W WP p Ryes Rno M h hW hG _ i
  exact pr_bind_le _ _ _ _ _ fun x hx =>
    (pr_testOG W WP p i hW hG x.1 x.2
        (FbLt.of_notFb (onlyQ_nodeO W WP p i Tag.test) (fbLt_empty _) x hx)).trans
      (add_le_add (h.prT _ _) le_rfl)

theorem unifLG : Spec.unifLG := by
  intro I X lam L W WP p Ryes Rno M h hW hG _ i
  refine pr_bind_le _ _ _ _ _ fun x hx => pr_bind_le _ _ _ _ _ fun y hy => ?_
  have t1 := FbLt.of_notFb (onlyQ_nodeO W WP p i Tag.link) (fbLt_empty _) x hx
  exact (pr_linkOG W WP p i hW hG x.1 y.1 y.2
      (FbLt.of_notFb (onlyQ_nodeO W WP p i Tag.link) t1 y hy)).trans
    (add_le_add (h.prL _ _) le_rfl)

end Compile.Batch
