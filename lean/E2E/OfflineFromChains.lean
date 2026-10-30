-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFromChains.lean: a value of `OfflineDebts` at the honest provers' offline prover and the served requests, with the
shared chain paid but for its two proximity tests. What is left are the debts of the first and the last chain, that the
threads sit, members 9 and 10 of the shared chain, and what a run owes (`AtRunS`).

Main name. `offlineDebts_from_chains`.

What stays open. The premises `first` (`Sits`, and `OwesS`, `SaidNext`, `YesS` at the first and last chains), `tests` (members 9
and 10), `hat`, and the laws on the letters `Nm`, `Mg₀`, `Kp`; all at no fall. The first and last threads are letters.

No law over coins. Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.OfflineAtTheTerm
import E2E.OfflineSharedAtTied

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Fall Thread Local Common Coins Mid Sits OwesS YesS SaidNext PlaysS BehindS ExchangeS
  RidesPastS AcceptedS Table fallsBy)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.Bridge (KeyAccepts)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open ProofFile.Honest.Term (tableCoins)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStandWalked (offlineValue threadAt walkedLetter)
open LPFD.Full (XF)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZOfflineFromChains : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueOfflineFromChains : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueOfflineFromChains : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub)

/-- **The value of `OfflineDebts` at no fall, with the shared chain paid but for its two proximity tests.** -/
theorem offlineDebts_from_chains (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hN : Function.Injective Nm.tenant)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    {U₁ : FirstFamily Z description (keyBook K₀)} {U₃ : LastFamily Z description (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (first : ∀ w x, TiedAt Z description w x → (descOf description).okStart x = true →
      Sits (descOf description)
          ((bareSides (descOf description) (keyBook K₀) (proverOf Z description) [] [] []).prover
            (proverOf Z description))
          (U₁ w x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (U₃ w x) ∧
        OwesS (U₁ w x) (S₁ w x) ∧ OwesS (U₃ w x) (S₃ w x) ∧
        (∀ b, SaidNext (U₁ w x) (S₁ w x) b) ∧ (∀ b, SaidNext (U₃ w x) (S₃ w x) b) ∧
        YesS (U₁ w x) (S₁ w x)
          (fallsBy [] (descOf description).first.blocksInOrder) ∧
        YesS (U₃ w x) (S₃ w x) (fallsBy [] (descOf description).second.blocksInOrder))
    (tests : ∀ w x, TiedAt Z description w x →
      (PlaysS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9 ∧
        BehindS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9 ∧
        ExchangeS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9 ∧
        RidesPastS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9) ∧
      (PlaysS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10 ∧
        BehindS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10 ∧
        ExchangeS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10 ∧
        RidesPastS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10) ∧
      AcceptedS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (fallsBy [] (descOf description).shared.blocksInOrder) 9 ∧
      AcceptedS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (fallsBy [] (descOf description).shared.blocksInOrder) 10)
    (hat : ∀ w x (c : CoinOne (keyBook K₀) RunValue RunValue), TiedAt Z description w x →
      AtRunS (descOf description) (proverOf Z description) (U₁ w x)
        (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (U₃ w x) (S₁ w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (S₃ w x) w x c) :
    ∃ Tied TiedM, OfflineDebts Z (descOf description) (thePartsAt Z).book
      ((thePartsAt Z).prover description) runValueBytes runValueBytes
      (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_no_fall_at_term hr (thePartsAt_book (files := Z) hK₀) hd scope live
    (U₂ := fun w x => sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
    (S₂ := fun w x => sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
    (fun w x ht hok => by
      obtain ⟨sits, o₁, o₃, n₁, n₃, y₁, y₃⟩ := first w x ht hok
      obtain ⟨o₉, o₁₀, y₉, y₁₀⟩ := tests w x ht
      obtain ⟨o₂, n₂, y₂⟩ := shared_at_tied hd scope live hK₀ AtPublicFiles.AtFiles.inRange ℓ Nm Mg₀ tk tt rest
        Kp Vd Z₀ w x ht hN hKp hE hEnd hC (fallsBy [] (descOf description).shared.blocksInOrder) o₉ o₁₀ y₉ y₁₀
      exact ⟨sits, o₁, o₂, o₃, n₁, n₂, n₃, y₁, y₂, y₃⟩)
    hat

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineDebts_from_chains
