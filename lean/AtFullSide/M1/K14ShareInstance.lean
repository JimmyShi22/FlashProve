-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- `k14_share_of_pays` at `theG_pays_of_holds`.
/-
AtFullSide/M1/K14ShareInstance.lean: `KindShare` at the kind K14 at `theGOfReturn`, at any K that holds ours:
`pays` from `theG_pays_of_holds` across `castSides_of`, the rest from `rows_of_K`, `second_of_K`, the cut. No
property of the protocol is claimed here.
-/
import AtFullSide.M1.KLarger
import AtFullSide.K14.Sim.ShareAtTheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open Johnson.M1 (k1Lot wLot KindBud)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)

variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **K14's share at a K that holds ours.** -/
theorem k14_kind_share (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (h₁ : k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id ∈ K.lots)
    (h₂ : wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id ∈ K.lots)
    (h₃ : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
    (hsix : ∀ r ∈ baseRows A₀.Z hd.places, r ∈ K.shared)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A₀.F A₀.B ((theGOfReturn made hd T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A₀.F A₀.B ((theGOfReturn made hd T K).prover H) w₀ rc x k R) :
    KindShare A₀ (theGOfReturn made hd T K) H Rel Th KindName.K14 :=
  k14_share_of_pays hd made T K
    (castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K14) _
      (theG_pays_of_holds hd hS hL made T K h₁ h₂ h₃ hsix).2.2)
    (rows_of_K hd K hsix KindName.K14 (by decide))
    (fun r hr hk => by
      have h2 := second_of_K K r hr
      rw [hk] at h2
      cases h2)
    (no_kind_of_cut (cuts_at_return hS hL made).1 cuts_kinds.1) H Rel Th

end AtFullSide.M1

#print axioms AtFullSide.M1.k14_kind_share
