-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/ShareK7.lean: the share of the sub-protocol kind K7 in the premise `shares` of zeroKnowledgeOnServedRequests_atTheG (AtFullSide/T3/TheOneAtTheG.lean), at the sides theGOfReturn: the kind's
own theorem, called. The premise is that K holds the kind's lot of rows. This file proves zero knowledge of nothing.
-/
import AtFullSide.T3.TheOneAtTheG
import E2E.ReplyShareAtTheG

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides
open ProofFile.Honest (OnlineProverWithDescription Cells ThreadsP ready onlineProverFromPublicFiles KindShare Prover)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifiableInference.Desc (KindName)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {files : PublicFiles} {Wt : Type}

/-- **K7's share**, at every prover beside the lists, every relation and every family of invariants. -/
theorem k7_kind_share  {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows baseFilling A.Z A.G)
    (laid : replyBaseLot ∈ K.lots)
    (H : Prover FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T K) H Rel Th KindName.K7 :=
  AtPublicFiles.TheSides.reply_share_at_the_G made h T K laid H Rel Th

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.k7_kind_share
