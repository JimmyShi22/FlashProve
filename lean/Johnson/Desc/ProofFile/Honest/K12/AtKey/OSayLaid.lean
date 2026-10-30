-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OSayLaid.lean: `says_in_front_at_ten` at the caller's thread and letter
(`laidThread`, `laidLetter`, ULaid.lean), at the written place of the test: the form that `SayAtStand` asks at Omega's row.

  `say_at_stand_at_laid_ten`   the statement

The field is paid by `field_of_walked`, the thread's premises by `plan_key` and `fields_made_at_key`.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `say_at_stand_at_laid_ten` bears this label; the rule is at its home, the head of
  Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: x is the made term under hx, of the first kind, with sd under its
  binder; k, m₀, E₀ stand under `ThrS`, of the first kind, which is to be shown at every k at the run's own stand. None: the
  bar is flat.
- The job is `JO` at the eight as a record: the tie to `omegaJobAtFiles` at `offlineSenders` is not said here.
- That a stand at 10 is reached is not said here.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OSayInFront
import Johnson.Desc.ProofFile.Honest.K12.AtKey.ULaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey plan_key)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub omegaTestPlace)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pU pO JO place_omega)
open AtPublicFiles.StandAtNine (K1)
open AtPublicFiles.OfflineRows (SaysInFront)
open Bind.ForProver (oodSh Seed)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi) (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (r o : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X)

/-- **Over every stand of the caller's pair at border 10, at every coin lent at the test's written place, the rows
that the test on G_omega takes in hold, in front of it.** -/
theorem say_at_stand_at_laid_ten {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) :
    ∀ k st m₀ E₀
      (c : RowCoins [(firstPart (JO Xs (K1 Xs K' f g Z₀) B) : Part Empty _ _),
        restPart (JO Xs (K1 Xs K' f g Z₀) B)]),
      ThrS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
        (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 10 k st m₀ E₀ →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) omegaTestPlace
        [(firstPart (JO Xs (K1 Xs K' f g Z₀) B) : Part Empty _ _),
          restPart (JO Xs (K1 Xs K' f g Z₀) B)] 0 = .ok c →
      SaysInFront (JO Xs (K1 Xs K' f g Z₀) B) m₀.st.input (frontOf m₀)
        (ProofFile.Honest.K12.Light.plainMany (manyAtTen Xs (K1 Xs K' f g Z₀) B (X₀ := X₀)) m₀.st.input
          (frontOf m₀) (restCoins (JO Xs (K1 Xs K' f g Z₀) B) c.2.1)) := by
  intro k st m₀ E₀ c hA hc
  have F := fields_made_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope sd hx
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  have hf := field_of_walked K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀
    (fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) (some []) (inK w₀ rc x))
    hs scope F rfl rfl hN (fun _ _ h => h ▸ saidField_start _ rfl)
  have hpl : (JO Xs (K1 Xs K' f g Z₀) B).p.place = omegaTestPlace := place_omega
  exact says_in_front_at_ten K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B
    own₀ (par_sourced hs scope) hQ _ hf k st m₀ E₀ c hA (by rw [hpl]; exact hc)

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.say_at_stand_at_laid_ten
