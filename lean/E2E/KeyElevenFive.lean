-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyElevenFive.lean: the five statements at member 11 of the key file's shared chain, its end. By calls.

Main name. `eleven_five`.

What stays open. As premises: the key fits the index (`hk`); no half stands at the chain's end (`hn`, `no_half_seal₂`);
`hKp`, `hEnd` on the letter `Kp`. That the thread stands at border 11 hangs on members 9 and 10, which nothing here shows.

No law over coins. Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyAcceptEleven
import E2E.KeyRowsLater
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyElevenFive
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyStandOne (inK)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **The five statements at the shared chain's end.** -/
theorem eleven_five {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hn : ((keyProver K).shared.find? fun g => g.place == (keyFileDescription Xs Nr Pl).shared.last.place) = none)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hEnd : ∀ s s', Kp 11 s s' → s' = s)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) :
    PlaysS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) Said 11 ∧
      BehindS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) Said 11 ∧
      ExchangeS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) Said 11 ∧
      RidesPastS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) Said 11 ∧
      AcceptedS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) Said fall 11 := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)
  obtain ⟨p, b, e, r⟩ := AtPublicFiles.KeyThread.row_seal₂ Xs Nr Pl hs scope _ hO
    (AtPublicFiles.KeySharedQuiet.quiet_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x) hKp)
    (AtPublicFiles.KeySharedQuiet.owes_seal Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x))
    (AtPublicFiles.KeySharedQuiet.ridesPast_seal Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x) hEnd) hn Said
  exact ⟨p, b, e, r, acceptedS_of _ Said
    (AtPublicFiles.KeyAcceptEleven.accepted_eleven Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w₀ rc x hs scope hk hn fall)⟩

end AtPublicFiles.KeyElevenFive

#print axioms AtPublicFiles.KeyElevenFive.eleven_five
