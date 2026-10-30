-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/ULaid.lean: the key file's shared thread as a caller lays it: the prover's parts are
`keyOf` (E2E/KeyStandMember.lean) of parts that hold the two proximity tests' halves and any halves at the fields rng
and own; the table is `tableKey` (E2E/KeyAsksKey.lean); the second condition is «the thread's own steps reach this
state from the start with the field at `some []`». That thread is the thread `TS` (E2E/StandAtNine.lean), and the
sentences of UWalked.lean hold at it in the caller's own letters, at the letter `keeps` := `keepsKey` (UKeeps.lean).

  `laidThread`, `laidLetter`   the caller's thread and second condition, written out
  `laid_thread_is_TS`   the two threads are one, by unfolding
  `owes_at_laid`, `yes_at_laid`, `next_at_laid`   `OwesS`, `YesS`, `SaidNext` at every member
  `tests_at_laid`       the five sentences at the two proximity tests, members 9 and 10

Limits.
- The senders' parts have the form `keyOf … K' f g`; the table's letter tt is `ttF` at them.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): every sentence has
  the thread's pair as a premise.
- At the honest key's input; at the written key's size alone.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UWalked
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UOStand

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
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.KeySharedQuiet (CellsAlone)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.TableFilled (ttF)
open AtPublicFiles.StandAtNine (K1 TS)
open Bind.ForProver (oodSh Seed)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : ℕ → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi) (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (r o : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X)

/-- The caller's thread. -/
abbrev laidThread :=
  threadKey Xs Nr PF (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) ℓ Nm Mg₀
      (tableKey Xs PF K₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) tk (ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀)) rest Kp Vd (inK w₀ rc x)

/-- The caller's second condition. -/
abbrev laidLetter :=
  WalkedFrom (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o)
    (fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) (some []) (inK w₀ rc x))

/-- **The two threads are one.** -/
theorem laid_thread_is_TS : laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o =
    TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ := rfl

section
variable {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
  (hK₀ : fullPub = some K₀) (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
  (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
  (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v)) (hVd : Vd (inK w₀ rc x))
include hs scope hK₀ sd hx hN hC hVd

/-- **What the chain's thread owes, in the caller's letters.** -/
theorem owes_at_laid :
    OwesS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
      (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) := by
  have F := fields_made_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope sd hx
  have hk : VerifiableInference.Desc.Own.keyFits x.key QK.par.S.fold.index = true := by
    have h := F.key (inK w₀ rc x) ⟨rfl, hVd⟩
    have e : parKey Xs PF = QK := par_sourced hs scope
    rw [e] at h
    exact h
  exact owes_walked_at_key K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀
    (fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) (some []) (inK w₀ rc x))
    hs scope F rfl rfl hN hC hk (fun _ _ h => h ▸ saidField_start _ rfl)

/-- **It is accepted at every member, in the caller's letters**, at any falls. -/
theorem yes_at_laid (fall : ℕ → St → List Fmt.Drawn → Option String) :
    YesS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
      (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) fall := by
  have F := fields_made_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope sd hx
  have hk : VerifiableInference.Desc.Own.keyFits x.key QK.par.S.fold.index = true := by
    have h := F.key (inK w₀ rc x) ⟨rfl, hVd⟩
    have e : parKey Xs PF = QK := par_sourced hs scope
    rw [e] at h
    exact h
  exact yes_walked_at_key K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀
    (fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) (some []) (inK w₀ rc x))
    hs scope F rfl rfl hN hC hk (fun _ _ h => h ▸ saidField_start _ rfl) fall

/-- **The five sentences at the two proximity tests, in the caller's letters.** -/
theorem tests_at_laid (fall : ℕ → St → List Fmt.Drawn → Option String) :
    (PlaysS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 9 ∧
        BehindS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 9 ∧
        ExchangeS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 9 ∧
        RidesPastS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 9) ∧
      (PlaysS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 10 ∧
        BehindS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 10 ∧
        ExchangeS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 10 ∧
        RidesPastS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
          (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) 10) ∧
      AcceptedS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
        (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) fall 9 ∧
      AcceptedS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o)
        (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀ r o) fall 10 := by
  have F := fields_made_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope sd hx
  have hk : VerifiableInference.Desc.Own.keyFits x.key QK.par.S.fold.index = true := by
    have h := F.key (inK w₀ rc x) ⟨rfl, hVd⟩
    have e : parKey Xs PF = QK := par_sourced hs scope
    rw [e] at h
    exact h
  exact tests_at_walked K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀
    (fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) (some []) (inK w₀ rc x))
    hs scope F rfl rfl hN hC hk (fun _ _ h => h ▸ saidField_start _ rfl) fall

end

/-- **The second condition is carried over every member.** -/
theorem next_at_laid (b : ℕ) :
    SaidNext (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o)
      (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o) b :=
  saidNext_walked _ _ b

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.laid_thread_is_TS
#print axioms ProofFile.Honest.K12.AtKey.owes_at_laid
#print axioms ProofFile.Honest.K12.AtKey.yes_at_laid
#print axioms ProofFile.Honest.K12.AtKey.tests_at_laid
#print axioms ProofFile.Honest.K12.AtKey.next_at_laid
