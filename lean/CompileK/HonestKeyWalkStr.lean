-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyWalkStr.lean: upper bounds on the honest committer's and prover's oracle queries:
the prover's typed count at a wire with searches, in the library's counts in closed form; both
parties in single strings put to the one oracle.

Statements (in `Compile.Batch.Spec`) and proofs. Generic. Nothing assumed beyond the hypotheses of
the statements and whatever the arguments hold as proofs.
lean/GLOSSARY.md has chain query (its answer: a chain answer), string, typed query. The typed
count (`hkCom`, `hkPro` at `fun _ => 1`) counts every typed query as 1. A coding (`OracleCoding`,
Rom/Family.lean) puts the typed oracles over one oracle on strings. At a wire with searches
(`QueryLayout.grind`, Iop/GrindWire.lean) a round may have a search for a nonce.

Main names:
  `Spec.honestKey_grindP`, 1 ≤ n: in its bound, `cTrees` .. n is an upper bound on the leaves of
    the trees of one execution with n slots at work (Compile/Batch/Counts.lean); `GBits.sumMo` is
    the tries after the first, every search at its cap; a shared search, which runs once, is
    charged n times.
  `Spec.honestKey_strC`, `Spec.honestKey_strP`: the committer, the prover of
    `schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))` (the prover on the batch b, its typed count at
    b.length) in strings: for `0 < lam`, at most (blocks of a chain answer) times the typed count,
    for every coding.

Limits: coarse. `honestKey_strC`, `honestKey_strP` charge every typed query the W.K + 1 blocks of a
chain answer, a leaf or vertex query too, which costs one string. The sharper formulas (sharper by
reading, not by a theorem) are `hkCom W p (blk W.K)`, `hkPro W (blk W.K) n`
(CompileK/HonestKeyWalk.lean, CompileK/HonestKeyWalkP.lean). Where the searches rule the typed count
little is lost.
This file says nothing on the value of any number. Its bounds are worst case over the oracle. It
says nothing on the mean.
-/
import CompileK.HonestKeyWalkGrind
import CompileK.HonestKeyWalkPProofs

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.OneCall (cPUW sumB cPUW_le)

namespace Spec

/-- The prover's typed count at a wire with searches. -/
def honestKey_grindP : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L)
      (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (n : ℕ),
    1 ≤ n → hkPro (Wr.grind Dg gT gL gB) (fun _ => 1) n ≤
      2 * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann Wr.B.sh n +
        ((n + 1) * L.onlineBatch.loc.shape.length + n * GBits.sumMo Dg _ gB) + (L.maxBatchSize - 1) + n

/-- The committer in strings. -/
def honestKey_strC : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Wn : Type)
      (m : OracleCoding (spec lam W.K L) lam) (i : I) (t : ℕ),
    0 < lam → hkCom W p (fun _ => 1) ≤ t →
    ((schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))).C i).QueryBound ((W.K + 1) * t)

/-- The prover in strings. -/
def honestKey_strP : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Wn : Type)
      (m : OracleCoding (spec lam W.K L) lam) (k : ISK lam L) (b : List (X × Wn)) (t : ℕ),
    0 < lam → hkPro W (fun _ => 1) b.length ≤ t →
    ((schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))).P k b).QueryBound ((W.K + 1) * t)

end Spec

theorem honestKey_grindP : Spec.honestKey_grindP := by
  intro Nn _ I X lam L Wr Dg gT gL gB n hn
  rw [honestKey_sumP]
  refine le_trans (cPUW_le (Wr.grind Dg gT gL gB) 1 (bf := fun _ _ => 1) (fun _ _ => le_rfl) n) ?_
  show 2 * cTrees (L.onlineBatch.loc.shape.grind Nn gB) (L.onlineBatch.ann.grind Nn gB)
          (RoundsQueryLayout.grind Wr.B.sh Dg gB) n +
      ((n + 1) * sumB (fun _ => 1) (L.onlineBatch.loc.shape.grind Nn gB) 0 +
        1 *
          (n * sMoreJ _ _ (RoundsQueryLayout.grind Wr.B.sh Dg gB) + sMore0 _ _ (RoundsQueryLayout.grind Wr.B.sh Dg gB))) +
      (L.maxBatchSize - 1) + n ≤ _
  rw [cTrees_grind, hk_sumB_one, Shape.grind_length, Nat.one_mul]
  have h := sMore_grind_le Dg n hn Wr.B.sh gB
  omega

theorem hk_blk_le (K : ℕ) (o : OracleName) : blk K o ≤ K + 1 := by
  cases o <;> simp [blk]

theorem honestKey_strC : Spec.honestKey_strC := fun I X lam L W WP p Wn m i t hl ht => by
  have hb : ∀ o, m.blocks o ≤ W.K + 1 :=
    fun o => by rw [honestKey_blocks I X L lam W.K m hl o]; exact hk_blk_le _ o
  have h := hk_cost_scale hb ((honestKey_cost I X lam L W WP p (fun _ => 1) i).mono ht)
  exact queryBound_overOne_of_cost m
    ((C W WP p i).bind fun o => .pure ((o.1, linksOf (keyOf o.2.1)), o.2)) _
    (OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h)

theorem honestKey_strP : Spec.honestKey_strP := fun I X lam L W WP p Wn m k b t hl ht => by
  have hb : ∀ o, m.blocks o ≤ W.K + 1 :=
    fun o => by rw [honestKey_blocks I X L lam W.K m hl o]; exact hk_blk_le _ o
  have h0 := honestKey_costP I X lam L W WP p (fun _ => 1) k (Gen.forgetW b)
  rw [show (Gen.forgetW b).length = b.length from List.length_map _] at h0
  have h := hk_cost_scale hb (h0.mono ht)
  have h1 : (PKE W WP p k (Gen.forgetW b)).CostBound m.blocks ((W.K + 1) * t + 0) :=
    OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h
  have h2 : ((Gen.withW Wn (argBKE W WP p)).P k b).CostBound m.blocks ((W.K + 1) * t + 0 + 0) :=
    OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h1
  exact queryBound_overOne_of_cost m _ _ h2

end Compile.Batch
