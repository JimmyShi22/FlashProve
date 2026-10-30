-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UWalked.lean: the key file's shared chain at the second condition `WalkedFrom`
(E2E/WalkedFrom.lean) alone: «the thread's own steps reach this state from a state that begins the chain». Where the
states that begin the chain have seen nothing and have the field `opened` at `some []`, that condition tells the
field at border 10: so the half of the test on G_omega, which plays behind a guard on the field, plays there.

  `thread_reads_two_halves_not`   the thread is the same at every value of the parts' fields rng and own
  `field_of_walked`     at border 10 `WalkedFrom` tells the field
  `owes_walked_at_key`, `yes_walked_at_key`   `OwesS`, `YesS` at `WalkedFrom`
  `tests_at_walked`     the five sentences at the two proximity tests, members 9 and 10, at `WalkedFrom`

By what. `walked_least` (E2E/WalkedFrom.lean): a second condition that holds where the chain begins and is carried over
every member holds at every state walked to.

Premise on the letter. hB: every state that begins the chain meets `SaidField` at border 0 (`saidField_start`: it has
seen nothing and its field is `some []`).

Limits.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): every sentence has
  the thread's pair as a premise.
- At one input, `inK w₀ rc x`; at the written key's size alone.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UOwes
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UStep
import E2E.WalkedFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey lettersKey)
open AtPublicFiles.KeySharedQuiet (CellsAlone)
open AtPublicFiles.KeyStandOne (inK)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.TableFilled (TR ttF)

variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Vd : Common W₀ Rc TableKey → Prop) (w₀ : W₀) (rc : Rc) (x : Xi)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (Begun : Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)

/-- **The shared chain's thread reads neither the ranges' half nor the own test's half of the prover's parts.** -/
theorem thread_reads_two_halves_not (Kp : ℕ → St → St → Prop)
    (r o : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X) :
    AtPublicFiles.KeySharedThread.threadKey Xs Nr PF { withTestsOnUAndOmega K₁ pU pO with rng := r, own := o } ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x) =
      TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀ := rfl

include hK₀ in
/-- **At border 10 the walk tells the field.** -/
theorem field_of_walked {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant)
    (hB : ∀ k m, Begun k m → SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) BaseNil 0 k m) :
    ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀)
      (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 10 k s m E →
    ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀).colsTo 10 m E = .ok cols → m.opened = some cols :=
  fun k s m E u => field_of_letter K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀ k s m E
    ⟨u.1, walked_least hB
      (saidNext_every_member K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd _ B own₀ hsource scope F hlin hsend hN
        (no_stop_at_key K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd _ B _ hsend)) u.2⟩

include hK₀ in
/-- **What the chain's thread owes, at the walk.** -/
theorem owes_walked_at_key {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hB : ∀ k m, Begun k m → SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) BaseNil 0 k m) :
    OwesS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀)
      (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) :=
  owes_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ _ hsource scope F hlin hsend hN hC hk
    (field_of_walked K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Begun hsource scope F hlin hsend hN hB)

include hK₀ in
/-- **It is accepted at every member, at the walk**, at any falls. -/
theorem yes_walked_at_key {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hB : ∀ k m, Begun k m → SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) BaseNil 0 k m)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    YesS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀)
      (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) fall :=
  yes_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ _ fall hsource scope F hlin hsend hN hC hk
    (field_of_walked K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Begun hsource scope F hlin hsend hN hB)

include hK₀ in
/-- **The five sentences at the two proximity tests, at the walk.** -/
theorem tests_at_walked {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hB : ∀ k m, Begun k m → SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) BaseNil 0 k m)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    (PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 9 ∧
        BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 9 ∧
        ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 9 ∧
        RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 9) ∧
      (PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 10 ∧
        BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 10 ∧
        ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 10 ∧
        RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) 10) ∧
      AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) fall 9 ∧
      AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) (WalkedFrom (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Begun) fall 10 := by
  have o := owes_walked_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Begun hsource scope F hlin hsend
    hN hC hk hB
  have y := yes_walked_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Begun hsource scope F hlin hsend
    hN hC hk hB fall
  have h12 := members_of_thread K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀
  exact ⟨o 9 (by rw [h12]; omega), o 10 (by rw [h12]; omega), y 9 (by rw [h12]; omega),
    y 10 (by rw [h12]; omega)⟩

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.thread_reads_two_halves_not
#print axioms ProofFile.Honest.K12.AtKey.field_of_walked
#print axioms ProofFile.Honest.K12.AtKey.owes_walked_at_key
#print axioms ProofFile.Honest.K12.AtKey.yes_walked_at_key
#print axioms ProofFile.Honest.K12.AtKey.tests_at_walked
