-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/ShareK5.lean: the share of the sub-protocol kind K5 in the premise `shares` of zeroKnowledgeOnServedRequests_atTheG (AtFullSide/T3/TheOneAtTheG.lean), at the sides theGOfReturn: KindPays and the five statements on the
lists, joined into one term of KindShare. On holds at all arguments at these lists; the kind has no list in the two later chains.

The premise is that K holds K5's lot of rows. That the kind's lists stand in G, and how many there are, is not shown here. The kind spends coins that another kind owns: their
freshness is ownerFresh_at_base, which is no part of this share. This file proves zero knowledge of nothing.
-/
import AtFullSide.T3.TheOneAtTheG
import E2E.AttentionAtTheOneG

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (KindRows kindPays_K5_at_return attention_lists_at_return)
open ProofFile.Honest (OnlineProverWithDescription Cells ThreadsP ready onlineProverFromPublicFiles KindShare Prover onAtRun₁_of_always)
open ProofFile.Honest.K5 (k5SLot)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifiableInference.Desc (KindName)
open VerifierAndGoals (PublicFiles)

variable {files : PublicFiles} {Wt : Type}

/-- **K5's share**, at every prover beside the lists, every relation and every family of invariants. -/
theorem k5_kind_share {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows baseFilling A.Z A.G)
    (laid : k5SLot (W₀ := FullSizeMatrix) (Rc := ProofFile.Honest.IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id
      ProofFile.Honest.K5.keyOfK3 ∈ K.lots)
    (H : Prover FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T K) H Rel Th KindName.K5 :=
  have lists := attention_lists_at_return made h T K laid
  ⟨kindPays_K5_at_return made h T K laid,
    ⟨fun L hL e σ hσ u hu _ _ n _ _ ρ _ => lists.bud L hL e σ hσ u hu n _ ρ,
      fun L hL e => absurd e (lists.noneShared L hL), fun L hL e => absurd e (lists.noneSecond L hL)⟩,
    fun _ _ _ _ _ _ _ ρ r _ _ _ =>
      ⟨fun L hL e => onAtRun₁_of_always _ ρ r (lists.on L hL e),
        fun L hL e => absurd e (lists.noneShared L hL),
        fun L hL e => absurd e (lists.noneSecond L hL)⟩⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.k5_kind_share
