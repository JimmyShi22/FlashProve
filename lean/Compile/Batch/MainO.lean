-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/MainO.lean: the proof that pruning Merkle paths keeps the three bounds of a scheme.

The file proves `Spec.pruneKeepsKGr` (Compile/Batch/StarO.lean): a scheme whose verifier is `VK`,
with its keys and proofs pruned, has the same three bounds as before. The wire record (parameters of
the compiler, beside `Params`) must be well-formed (`W.OKG`; rounds may have proof-of-work bits);
only its conditions on trees and leaves are used.

  `V_le_VO`, `VO_le_V`      `VO` accepts the pruned key and proof whenever `V` accepts; if `W.OKG`
                            holds, `V` accepts the key and proof with paths filled up to full length
                            (`fillIVK`, `fillPrf`) whenever `VO` accepts. Both hold for every choice
                            of the oracle functions and within the same trace (`AccLe`,
                            Compile/GenLe.lean), and come from `accLe_prune`, `accLe_fill`
                            (Compile/Batch/PrunedFacts.lean).
  `VK_le_VKO`, `VKO_le_VK`  The same with the entries of the copies in the key (entries, copies: the
                            head of Compile/Batch/StarO.lean).
  `pruneKeepsKGr`           The theorem, from these by `GenLe.main`.
  `extractorBO_Ei`          The extractor for pruned keys reads the root cm of the key and the
                            committer's trace, as before.

Limits: the theorem does not say that a proof becomes shorter (Compile/Batch/SizeO.lean), nor how
many queries the new verifiers make. Refined completeness (`HasRefinedCompletenessError`,
ZKCP/Gen.lean) is not carried over. The bounds are the old terms: nothing is claimed to have become
better or worse.
-/
import Compile.Batch.StarO
import Compile.Batch.PrunedFacts
import Compile.Batch.CompleteRefStarG
import Compile.Batch.CompleteUnifG
import Compile.Batch.DisciplineChainAll
import Compile.Batch.EqBatch
import Compile.Batch.EqProve
import Compile.Batch.EqSetup
import Compile.Batch.GlueBinding
import Compile.Batch.GluePrivacy
import Compile.Batch.HonestK
import Compile.Batch.HopTot
import Compile.Batch.Late4
import Compile.Batch.LifeStar
import Compile.Batch.PubDefer
import Compile.Batch.PubLate
import Compile.Batch.PubLump
import Compile.Batch.PubOverrun
import Compile.Batch.Sound
import Compile.Batch.SpecPubGr
import Compile.GenStop

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenLe
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## For `W.OKG`: external positions have different numbers -/

section Inj
variable {W : QueryLayout lam L} (hW : W.OKG)
include hW

theorem extInj_T : ExtInj W.T.ext := by
  refine List.Nodup.map (fun p q h => ?_) hW.T.ext.nodup
  unfold extIdx at h
  rw [(hW.extT p).1, (hW.extT p).2, (hW.extT q).1, (hW.extT q).2] at h
  exact Fin.ext (by simpa using h)

theorem extInj_B : ExtInj W.B.ext := by
  refine List.Nodup.map (fun p q h => ?_) hW.B.ext.nodup
  unfold extIdx at h
  rw [(hW.extB p).1, (hW.extB p).2, (hW.extB q).1, (hW.extB q).2] at h
  exact Fin.ext (by simpa using h)

theorem extInj_L : ExtInj W.Lk.ext := by
  refine List.Nodup.map (fun p q h => ?_) hW.Lk.ext.nodup
  unfold extIdx at h
  have hd : W.Lk.ext.depth = W.depth := hW.extDepth.2.1
  have hf := hW.fits
  rw [hd] at h
  rcases p with p | p <;> rcases q with q | q
  · rw [(hW.extL.1 p).1, (hW.extL.1 p).2, (hW.extL.1 q).1, (hW.extL.1 q).2] at h
    exact congrArg Sum.inl (Fin.ext (by simpa using h))
  · rw [(hW.extL.1 p).1, (hW.extL.1 p).2, (hW.extL.2 q).1, (hW.extL.2 q).2] at h
    have := p.isLt
    omega
  · rw [(hW.extL.2 p).1, (hW.extL.2 p).2, (hW.extL.1 q).1, (hW.extL.1 q).2] at h
    have := q.isLt
    omega
  · rw [(hW.extL.2 p).1, (hW.extL.2 p).2, (hW.extL.2 q).1, (hW.extL.2 q).2] at h
    exact congrArg Sum.inr (Fin.ext (by simpa using h))

end Inj

/-! ## The verifiers -/

section V
variable (W : QueryLayout lam L) (p : Params)

/-- VO accepts the pruned key and proof whenever V accepts. -/
theorem V_le_VO (v : IVK lam L) (x : X) (π : Prf lam L) :
    AccLe (V W p v x π) (VO W p (pruneIVK W v) x (prunePrf W π)) := by
  obtain ⟨cm, piT⟩ := v
  obtain ⟨j, c, piL, piB⟩ := π
  cases piT with
  | none => exact AccLe.of_false _
  | some a =>
    cases piL with
    | none => exact AccLe.of_false _
    | some b =>
      cases piB with
      | none => exact AccLe.of_false _
      | some d =>
        unfold V VO pruneIVK prunePrf
        dsimp only [Option.map_some]
        split_ifs
        · exact AccLe.and3 accLe_prune accLe_prune accLe_prune
        · exact AccLe.refl _

/-- For a well-formed wire record (`W.OKG`), `V` accepts the key and proof with paths filled up to
full length (`fillIVK`, `fillPrf`) whenever `VO` accepts. -/
theorem VO_le_V (hW : W.OKG) (v : IVKO lam L) (x : X) (π : PrfO lam L) :
    AccLe (VO W p v x π) (V W p (fillIVK W v) x (fillPrf W π)) := by
  obtain ⟨cm, piT⟩ := v
  obtain ⟨j, c, piL, piB⟩ := π
  cases piT with
  | none => exact AccLe.of_false _
  | some a =>
    cases piL with
    | none => exact AccLe.of_false _
    | some b =>
      cases piB with
      | none => exact AccLe.of_false _
      | some d =>
        unfold V VO fillIVK fillPrf
        dsimp only [Option.map_some]
        split_ifs
        · exact AccLe.and3 (accLe_fill hW.T (extInj_T hW) a)
            (accLe_fill hW.Lk (extInj_L hW) b) (accLe_fill hW.B (extInj_B hW) d)
        · exact AccLe.refl _

theorem prunePrf_reK (ℓ : Links lam L) (π : PrfK lam L) :
    prunePrf W (reK ℓ (liftK π)) =
      reKO (ℓ.map fun e => (e.1, e.2.map (pruneO W.Lk))) (prunePrfK W π) := by
  unfold reK reKO prunePrfK liftK
  simp only [List.getElem?_map]
  cases ℓ[π.leaf]? <;> rfl

theorem fillPrf_reKO (ℓ : LinksO lam L) (π : PrfKO lam L) :
    fillPrf W (reKO ℓ π) =
      reK (ℓ.map fun e => (e.1, e.2.map (fillO W.Lk))) (liftK (fillPrfK W π)) := by
  unfold reK reKO fillPrfK liftK
  simp only [List.getElem?_map]
  cases ℓ[π.leaf]? <;> rfl

theorem VK_le_VKO (v : IVKK lam L) (x : X) (π : PrfK lam L) :
    AccLe (VK W p v x π) (VKO W p (pruneIVKK W v) x (prunePrfK W π)) := by
  unfold VK VKO pruneIVKK
  rw [← prunePrf_reK]
  exact V_le_VO W p v.1 x _

theorem VKO_le_VK (hW : W.OKG) (v : IVKKO lam L) (x : X) (π : PrfKO lam L) :
    AccLe (VKO W p v x π) (VK W p (fillIVKK W v) x (fillPrfK W π)) := by
  unfold VK VKO fillIVKK
  rw [← fillPrf_reKO]
  exact VO_le_V W p hW v.1 x _

end V

/-! ## Pruning keeps the three bounds (for `W.OKG` and a scheme whose verifier is `VK`) -/


theorem pruneKeepsKGr : Spec.pruneKeepsKGr := by
  intro I X lam L W p hW ISK PP A hA R B E Sim α ε ζ h
  exact GenLe.main (fun v x π => by rw [hA]; exact VK_le_VKO W p v x π)
    (fun v x π => by rw [hA]; exact VKO_le_VK W p hW v x π) h


/-! ## The extractor -/

/-- the extractor composed with the maps back (`fillIVK W`, `fillPrf W`) reads the root cm of the
key, and nothing else of key or proof -/
theorem extractorBO_Ei (W : QueryLayout lam L) (v : IVKO lam L) (tr : Trace (spec lam W.K L)) :
    (pullEK (fillIVK W) (fillPrf W) (extractorB W)).Ei v tr = (extractorB W).Ei ⟨v.cm, none⟩ tr :=
  rfl

theorem extractorBKO_Ei (W : QueryLayout lam L) (v : IVKKO lam L) (tr : Trace (spec lam W.K L)) :
    (pullEK (fillIVKK W) (fillPrfK W) (extractorBK W)).Ei v tr =
      (extractorB W).Ei ⟨v.1.cm, none⟩ tr := rfl

/-- If leaf and node answers are one hash block under m, the extractor composed with the maps back
(`fillIVK W`, `fillPrf W`) reads only entries at oracles with one-block answers, as `extractorB`
does. -/
theorem extractorBO_local (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) :
    LocalTo (pullEK (fillIVK W) (fillPrf W) (extractorB W)) m :=
  localTo_pullEK _ _ (extractorB_local W m hl hn)

end Compile.Batch
