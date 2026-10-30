-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSitsAtLaid.lean: THE FIELD `sits` OF `TheLots` (E2E/OfflineJoin.lean) at the laid letters: the first chain's own thread
`Th` (`firstFamilyAt`, E2E/OfflineFirstFamilyAtTerm.lean), the join's shared thread, and the last chain's thread `threadOwn`
(E2E/KeyLastAll.lean) at the key's parts at the offline prover's senders.

  `sits_of_last`   the three sit, at any last thread that stands at the last chain and passes the test on its tables
  `sits_at_own`    **the field**, pointwise: at every input, tied or not, and every value of `threadOwn`'s other letters

All other letters are free: Q; ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀; and twenty-six letters of `threadOwn`. A family U₃ of
`TheLots` whose value at each input is `threadOwn` at these parts has the field by this sentence at that input.

What `Sits` says (Johnson/Desc/ProofFile/Honest/Thread/File.lean): where the three threads stand (face, chain's number, first
tree's number, list of sub-protocols, halves) and that three tests with code on their tables of joints and numbers
accept. It reads no sentence of a thread. Calls and unfoldings. In scope, at a sourced description. Nothing on any
property.
-/
import E2E.KeyLastAll
import E2E.OfflineFirstFamilyAtTerm
import E2E.KeySharedDebts
import E2E.KeyLastQuiet
import E2E.KeyThreadFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyLink (bareSides bareSides_prover)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeySharedDebts (sits_chosen)
open AtPublicFiles.KeyLastQuiet (fits_last_key)
open AtPublicFiles.KeyThread (lengths)
open AtPublicFiles.FirstH (LaterFill fillH tbH)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader descOf proverOf sharedThread)
open AtPublicFiles.KeyLastChain (threadOwn)
open AtPublicFiles.KeyThread (KeyFill)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (FirstState)
open ProofFile.Honest.Term (tableCoins)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} (d : OfflineDescription) {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt)
  (Nm : NumbersS) (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)

/-- **The three sit, at any last thread that stands at the last chain and passes the test on its tables.** -/
theorem sits_of_last (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (U₃ : Thread (keyBook K₀) (descOf d).S₃ (descOf d).Cl (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit)
      (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
    (h₃ : U₃.φ = .own ∧ U₃.chain = 2 ∧ U₃.ft = (descOf d).lastChainFirstTreeNumber ∧
      U₃.bs = (descOf d).second.blocksInOrder ∧ U₃.hs = (proverOf Z d).second)
    (hf₃ : U₃.fits 4 = true) :
    Sits (descOf d)
      ((bareSides (descOf d) (keyBook K₀) (proverOf Z d) [] [] []).prover (proverOf Z d))
      (firstFamilyAt d Q w x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) U₃ := by
  rw [bareSides_prover]
  exact sits_chosen d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
    Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x hs scope
    (fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q x)
    (tbH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q) U₃ h₃
    (by rw [(lengths scope hs.named).2.2]; exact hf₃)

section Own
variable {Cells M Smp Rec P₂ Wt₂ : Type}
  (L : KeyFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Cells M Smp Rec) (ℓ₂ : WitLens Wt₂) (Nm₂ : NumbersS)
  (Mg₂ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (w₂ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) (w₀' : FullSizeMatrix) (rc' : (protocolAtFiles Z).EncodingRandomness) (x' : Xi)
  (hs₁ : List (Placed (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit))
  (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit → List Fmt.Drawn →
    Place × Table)
  (Said₁ : Nat → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
  (Said₂ : Nat → Coins (keyBook K₀) → Mid (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit → Prop)
  (dd : (Xi × FirstState) × St)
  (Dt : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit →
    MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E)) (n₁ n₂ : Nat)
  (Vd₃ : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit → Prop) (w₃ : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit)

/-- **THE FIELD `sits`, at the laid letters**: at every input, tied or not; the last thread is `threadOwn` at the key's
parts at the offline prover's senders and at every value of its other letters. -/
theorem sits_at_own (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :
    Sits (descOf d)
      ((bareSides (descOf d) (keyBook K₀) (proverOf Z d) [] [] []).prover (proverOf Z d))
      (firstFamilyAt d Q w x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x)
      (threadOwn d.source d.numbers d.later
        (keyOf (pubKey Z₀ d.source.chains) d.source d.later (offlineValue (files := Z) d) matrixReader
          (tableCoins Z))
        L ℓ₂ Nm₂ Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀' rc' x' hs₁ tb₁ Said₁ Said₂ dd Dt ML n₁ n₂ Vd₃ w₃ dfltT
        dfltM) :=
  sits_of_last d ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q hs scope w x _ ⟨rfl, rfl, rfl, rfl, rfl⟩
    (fits_last_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs.named.plan)

end Own

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.sits_of_last
#print axioms AtPublicFiles.OfflineRows.sits_at_own
