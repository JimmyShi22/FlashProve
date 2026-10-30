-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1LaidOfMembers.lean: the shared "sending" (the kind K1): K1Laid (KindPaysK1AtTheG.lean) FROM THREE MEMBERSHIPS: at ANY value K of the kinds'
rows over the base filling: if our two lots are among K.lots and the shared chain's two sendings' rows among K.shared, then K1Laid h K:
K's own fields say that its lots' names and its shared rows' places are apart, so each search finds the member. So at a K of record
that gathers all kinds' rows K1Laid is three memberships, and KindPays (theGOfReturn made h T K) .K1 follows. Two theorems; no definition.

  k1Laid_of_mem         baseLotS ∈ K.lots · baseWS ∈ K.lots · baseSendings h ⊆ K.shared ⊢ K1Laid h K
  kindPays_K1_of_mem    the same three ⊢ KindPays (theGOfReturn made h T K) .K1

Limits. All limits of KindPaysK1AtTheG.lean. No value of K is named here. No property of the protocol is claimed.
-/
import AtFullSide.K1.K1LaidHasAMember

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest ProofFile.Honest.Term
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **K1Laid from three memberships.** -/
theorem k1Laid_of_mem (h : HeadAtReturn files A) (K : KindRows (baseFilling files) A.Z A.G)
    (h1 : baseLotS ∈ K.lots) (h2 : baseWS ∈ K.lots) (h3 : ∀ r ∈ baseSendings h, r ∈ K.shared) :
    K1Laid h K where
  lot := find_of_apart (·.name) K.lots K.apart baseLotS h1
  w := find_of_apart (·.name) K.lots K.apart baseWS h2
  shared := fun r hr => find_of_apart (·.place) K.shared K.shared_apart r (h3 r hr)

/-- **KindPays at the named sides from the three memberships.** -/
theorem kindPays_K1_of_mem (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (h1 : baseLotS ∈ K.lots) (h2 : baseWS ∈ K.lots) (h3 : ∀ r ∈ baseSendings h, r ∈ K.shared) :
    KindPays (theGOfReturn made h T K) .K1 :=
  kindPays_K1_at_theG hS hL made h T K (k1Laid_of_mem h K h1 h2 h3)

end AtFullSide.K1

#print axioms AtFullSide.K1.k1Laid_of_mem
#print axioms AtFullSide.K1.kindPays_K1_of_mem
