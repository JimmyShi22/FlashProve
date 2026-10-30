-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedAtTied.lean: at a tied input of the offline prover, at the description of the public files, what the
accept law owes at the shared chain, from the two proximity tests' debts.

Why. `MembersS` is asked at every tied input. `sharedOwes`, `sharedYes` (E2E/KeySharedDebts.lean) want the input's key to
be the committer's at a seed, that it fits the index, and that no half stands at the chain's end. A tied input gives the
first two, and the value gives the third.

Main name. `shared_at_tied`.

What stays open. As premises: members 9 and 10 (`owes₉`, `owes₁₀`, `yes₉`, `yes₁₀`); the letters `Nm`, `Mg₀`, `Kp` with what
they must meet. That idle ones serve at this thread is a reading, not shown here.

No law over coins. Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeySharedDebts
import E2E.KeyOodTie
import E2E.KeyOfflineSides
import E2E.KeyAcceptProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi beforeSharedPoint)
open _root_.Desc.K14 (St)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest.Term (matrixInput tableCoins)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandWalked (offlineValue threadAt walkedLetter)
open AtPublicFiles.KeySharedDebts (sharedOwes sharedYes)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyOodTie (validAt_of_tied)
open AtPublicFiles.KeyValues (faceAt keyBatt oneOf matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.KeyValueHolds (atAll_value place_p12At)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open Bind.ForProver (shapeOf oodSh keyFits_oodSh_of)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZOfflineSharedAtTied : Nonempty PadZ := pads_nonempty frS 402653181

variable {Z : PublicFiles} {description : OfflineDescription}

/-- **At a tied input: the shared chain's debts, from members 9 and 10.** -/
theorem shared_at_tied {Q₂ Q₃ P₁ Wt : Type} [Nonempty Q₂] [Inhabited Q₃]
    {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray} (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {K₀ : KeyPub}
    (hK₀ : fullPub = some K₀) (ok : AtPublicFiles.AtFiles.FullSizeMatrix → Prop) (ℓ : WitLens Wt) (Nm : NumbersS)
    (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
    (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Place × Table)
    (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Place × Table)
    (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Wt)
    (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
    (Z₀ : ProofFile.Pub) (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : AtPublicFiles.AtFiles.TiedOffline Z description.source description.numbers description.later val₂
      val₃ (offlineValue (files := Z) description) ok w x)
    (hN : Function.Injective Nm.tenant)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (fall : Nat → (VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers
      description.later).S₂ → List Fmt.Drawn → Option String)
    (owes₉ : PlaysS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 9 ∧
      BehindS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 9 ∧
      ExchangeS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 9 ∧
      RidesPastS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 9)
    (owes₁₀ : PlaysS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 10 ∧
      BehindS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 10 ∧
      ExchangeS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 10 ∧
      RidesPastS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) 10)
    (yes₉ : AcceptedS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) fall 9)
    (yes₁₀ : AcceptedS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) fall 10) :
    OwesS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) ∧
      (∀ b, SaidNext (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) b) ∧
      YesS (threadAt description.source description.numbers description.later K₀
        (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z)
        Z₀ w.1 w.2.1 x)
        (walkedLetter description.source description.numbers description.later K₀
          (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader
          (tableCoins Z) Z₀ w.1 w.2.1 x) fall := by
  have sourced := sourced_of_ok live hd
  have hk := AtPublicFiles.AtFiles.sized_sourced sourced scope
  obtain ⟨sd, hsd⟩ := validAt_of_tied Z rfl ht Z₀ description.source.chains hk
  have hx : x = ⟨oodSh (shapeOf (pubKey Z₀ description.source.chains))
      (pubKey Z₀ description.source.chains) ⟨matrixReader w.1, tableCoins Z w.2.1, sd⟩⟩ := by
    cases x with
    | mk key => exact congrArg Xi.mk hsd
  have hsd' : x.key = oodSh (shapeOf (pubKey Z₀ description.source.chains))
      (pubKey Z₀ description.source.chains) ⟨matrixReader w.1, tableCoins Z w.2.1, sd⟩ := hsd
  have hFits : keyFits x.key AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true := by
    rw [← AtPublicFiles.AtFiles.Full.par_sourced sourced scope, hsd']
    exact keyFits_oodSh_of _ _ _ rfl
  have hW : (OnBytes.linMessageW (oneOf description.source).lin).isSome = true := by
    show (OnBytes.linMessageW description.source.Y.k.oneTime.lin).isSome = true
    rw [(AtPublicFiles.AtFiles.five_sourced sourced scope).2.2.1]
    exact written_W
  have hAll := atAll_value
    (fixedKeyParts (faceAt description.source 0) (keyBatt description.source) matrixInput.dummy () ()
      idleRecord) description.source description.numbers description.later matrixReader
    (tableCoins Z) matrixInput.inRange matrixInput.dummy (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0
    hW (senders_split scope live hd) (place_p12At _ _) (place_p12At _ _)
  have hn := AtPublicFiles.AtFiles.no_half_seal₂ description.source description.numbers description.later _ hAll
  exact ⟨sharedOwes description.source description.numbers description.later K₀
      (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z) Z₀
      w.1 w.2.1 x _ sourced scope hK₀ sd hx hN (place_p12At _ _) (place_p12At _ _) hKp hE hEnd hC hFits
      hn owes₉ owes₁₀,
    fun b => saidNext_walked _ _ b,
    sharedYes description.source description.numbers description.later K₀
      (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z) Z₀
      w.1 w.2.1 x _ fall sourced scope hK₀ sd hx hN (place_p12At _ _) (place_p12At _ _) hKp hE hEnd hC
      hFits hn yes₉ yes₁₀⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.shared_at_tied
