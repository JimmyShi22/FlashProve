-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/KeptCut.lean: from the bounds of Compile/Batch/Kept.lean to the cost hypotheses of
  two changes of oracles composed (`Spec.cutState`, Rom/SpecCut.lean; words of this library:
  lean/GLOSSARY.md).
  The two changes. First the split of answers, `cutFS` (Compile/Batch/CutFit.lean): for K = K' + 2 a
  Fiat-Shamir answer (K hash blocks and a chaining value) is split after its first hash block; an
  algorithm asks for the first part, and for the rest only where a rule that sees the first part
  says so (Rom/SpecCut.lean). Then the expansion from a state, `linksS`
  (Compile/Batch/CutLinks.lean): the rest of such an answer is expanded from a state of two hash
  blocks. The cost hypotheses have the form `CostBoundV (wCut C1 need (wCh C2))`
  (`OComp.CostBoundV w c t`, Rom/SpecOverOneA.lean: on every path the weights of the queries add up
  to at most t).
    `wCut_le_kept`       under `Test0` (the proof-of-work check depends on block 0 alone), for every
                         weight u on the split oracles that is 0 at every oracle `.inl o` (first
                         parts, and oracles that are not split) and at most 1 at the rest of a
                         Fiat-Shamir answer: wCut (cutFS ..) (needT W) u o q r ≤ wKept W o q r
                         (`wKept`, Compile/Batch/SpecKept.lean: at `fb t`, 0 for a failed attempt
                         that is not the last, else 1; at every other oracle 0)
    `cC_kept`, `cP_kept`  so, under `Test0`, for `W.OKG` and the seed's oracle `other`, in the
                          weight wCut (cutFS ..) (needT W) (wCh (linksS ..)): the committer of
                          `prunedK W p (argPL ..)` has weight at most `kCB L p`; its prover, on a
                          batch of at most L.maxBatchSize requests, at most `kPU L L.maxBatchSize`
    `cV_kept`            V runs under the rule "always" (the rest of a split answer is always
                         queried). Coarse, on purpose: at most `cVB W` (Compile/Batch/VCost.lean:
                         all hash blocks of all its queries). In `Spec.cutState` the bound kV on V's
                         weight occurs only in terms with the denominator 2^(2 lam).
  Limits: no sharp count for V. No numeral.
-/
import Compile.Batch.Kept
import Compile.Batch.CutLinks
import Compile.Batch.SizeO

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- Under `Test0`: at a failed attempt that is not the last the rest is not queried. -/
theorem needT_of_fails (W : QueryLayout lam L) (hT : Test0 W) {t : Tag} {q : FbIn lam L t}
    {r : rngOf lam W.K (.fb t)} (hf : failsAt W t q r.1 = true) :
    needT W (.fb t) q ((cutFS lam W.K L (.fb t)).front r) = false := by
  unfold failsAt at hf
  show (match tryInfoT W t q.plain with
    | some x => x.1 (fun _ => frontBl lam W.K ((cutFb lam W.K).front r)) || x.2
    | none => true) = false
  cases hx : tryInfoT W t q.plain with
  | none => rw [hx] at hf; exact nomatch hf
  | some x =>
    rw [hx] at hf
    have h1 : (!x.1 r.1 && !x.2) = true := hf
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
    have h0 : 0 < W.K := (hT t _ x hx).1
    show (x.1 (fun _ => frontBl lam W.K ((cutFb lam W.K).front r)) || x.2) = false
    rw [frontBl_front W.K h0 r,
      ← (hT t _ x hx).2 r.1 (fun _ => r.1 ⟨0, h0⟩) fun _ => rfl, h1.1, h1.2]
    rfl

/-- Under `Test0`, `hl`, `hr`: `wCut` is at most `wKept`. -/
theorem wCut_le_kept (W : QueryLayout lam L) (hT : Test0 W)
    (u : (x : (cutSpec (spec lam W.K L) (cutFS lam W.K L)).ι) →
      (cutSpec (spec lam W.K L) (cutFS lam W.K L)).Dom x → ℕ)
    (hl : ∀ o q, u (.inl o) q = 0) (hr : ∀ t q, u (.inr (.fb t)) q ≤ 1) (o : OracleName)
    (q : domOf lam L o) (r : rngOf lam W.K o) :
    wCut (cutFS lam W.K L) (needT W) u o q r ≤ wKept W o q r := by
  unfold wCut
  rw [hl, Nat.zero_add]
  by_cases ho : ∃ t, o = .fb t
  · obtain ⟨t, rfl⟩ := ho
    by_cases hf : failsAt W t q r.1 = true
    · rw [needT_of_fails W hT hf]
      simp
    · have e : wKept W (.fb t) q r = 1 := if_neg hf
      rw [e]
      split_ifs
      · exact Nat.zero_le _
      · exact hr t q
  · rw [isWhole_cutFS (lam := lam) (L := L) (o := o) fun t e => ho ⟨t, e⟩]
    simp

theorem kPU_mono (L : BatchProtocol I X) {n n' : ℕ} (h : n ≤ n') : kPU L n ≤ kPU L n' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- under "always" the weight of a query is at most the number of hash blocks of its answer -/
theorem wCut_le_blk (K : ℕ) (o : OracleName) (q : domOf lam L o) (r : rngOf lam K o) :
    wCut (cutFS lam K L) (fun _ _ _ => true) (wCh (linksS lam K L)) o q r ≤ blk K o := by
  unfold wCut
  rw [wCh_inl, Nat.zero_add]
  by_cases ho : ∃ t, o = .fb t
  · obtain ⟨t, rfl⟩ := ho
    split_ifs
    · exact Nat.zero_le _
    · exact (wCh_inr_le _ q).trans (Nat.succ_le_succ (Nat.zero_le K))
  · rw [isWhole_cutFS (lam := lam) (L := L) (o := o) fun t e => ho ⟨t, e⟩]
    simp

section
variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
  (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ)
  (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b)

/-- the committer, under `Test0`, `W.OKG`, and the seed's oracle `other` -/
theorem cC_kept (hT : Test0 W) (hW : W.OKG) (hσ : σ.o = OracleName.other) (i : I) :
    ((prunedK W p (Seed.argPL W WP p bk σ ℓ no)).C i).CostBoundV
      (wCut (cutFS lam W.K L) (needT W) (wCh (linksS lam W.K L))) (kCB L p) :=
  OComp.CostBoundV.weight (wCut_le_kept W hT _ wCh_inl fun t q => wCh_inr_le (.fb t) q)
    (keptC I X lam L W WP p bk σ ℓ no hW hσ i)

/-- the prover, on a batch of at most L.maxBatchSize requests, under the same hypotheses -/
theorem cP_kept (hT : Test0 W) (hW : W.OKG) (hσ : σ.o = OracleName.other)
    (k : (I × Fin (σ.sd + 1)) × Seed.Ca lam) (c : List (X × Unit)) (hc : c.length ≤ L.maxBatchSize) :
    ((prunedK W p (Seed.argPL W WP p bk σ ℓ no)).P k c).CostBoundV
      (wCut (cutFS lam W.K L) (needT W) (wCh (linksS lam W.K L))) (kPU L L.maxBatchSize) :=
  (OComp.CostBoundV.weight (wCut_le_kept W hT _ wCh_inl fun t q => wCh_inr_le (.fb t) q)
      (keptP I X lam L W WP p bk σ ℓ no hW hσ k c)).mono (kPU_mono L hc)

/-- the verifier, under "always"; a coarse bound -/
theorem cV_kept (v : IVKKO lam L) (x : X) (π : PrfKO lam L) :
    ((prunedK W p (Seed.argPL W WP p bk σ ℓ no)).V v x π).CostBoundV
      (wCut (cutFS lam W.K L) (fun _ _ _ => true) (wCh (linksS lam W.K L))) (cVB W) :=
  OComp.CostBoundV.weight (w := fun o _ _ => blk W.K o) (wCut_le_blk W.K)
    (OComp.CostBoundV.of_costBoundAt (OComp.CostBoundAt.of_costBound (costBound_VKO W p v x π)))

end

end Compile.Batch
