-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotSharedAtValue.lean: THE SHARED CHAIN's LETTER tt AS A NAMED TERM AT THE REAL VALUE, the tie of that term to the offline prover's own two halves, and what
the last chain's door asks of the shared chain there.

  sendersAt Z d        (its text: E2E/LotLetters.lean) the offline prover's senders (offlineSenders), of which withTests makes the two halves
  ttValue Z d K₀       (its text: E2E/LotLetters.lean) THE TERM: ttShared K₀ (bsOf S) (stOf S) (wtOf S) (rdOf S) () at S := sendersAt Z d: IOP's ttPlaced at the letters that
                       E2E/KeyPartsHalves.lean's onUOf and onOmegaOf hand the two halves
  halves_are_jobs      THE TIE, in scope: the offline prover's half at member 9 is proverSideOfProximityTest of IOP's JKU AQ … at these letters, and its half at
                       member 10 is proverSideOfProximityTest of JKO AQ … behind the guard. So ttValue's tables are texts over the prover's OWN two jobs.
  LotOpensSharedAtValue, LotDoorAsksSharedAtValue   OpensShared there; DoorAsks at 12 and the letter at the start there, with PlaysS at 9 and 10 left

IT STANDS ON IOP's TRIAL, ON NO ROW, through E2E/LotOpensShared.lean: see that file's head.
Letters that stay: ℓ, Nm, Mg₀, tk, rest, Kp, Vd, Z₀ (the thread's), w₀, rc, x, the seed sd. Premises that stay: KeySourced (so protocolDataWellFormed), InScope,
fullPub = some K₀, hx (the instance is the committer's sample at some seed), hN, PlaysS at [9, 10].
Limits. The tie is of terms: it does not say that a table of ttValue is what a half sends in a run: that is PlaysS's last clause at 9 and 10. No stand at 12
is shown. Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
import E2E.LotLetters
import E2E.LotOpensShared
import E2E.LotFieldSharedCut
import E2E.KeyNineClosed
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyStandWalked.Lots
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open ProofFile.Honest.Term (tableCoins)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (PF QK par_sourced later_sourced)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineSenders matrixReader)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyStandOne (startAt inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (place_p12At noStop_value)
open AtPublicFiles.KeyDepthsClosed (AQ)
open AtPublicFiles.KeyLay (JKU JKO bsOf stOf wtOf rdOf)
open AtPublicFiles.LotField (DoorAsks)
open H2K.Member (piKUFull piKOFull)
open Bind.ForProver (shapeOf oodSh Seed)

variable (Z : VerifierAndGoals.PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- The numbers of the test on Omega's group, at the written places. By evaluation. -/
theorem omega_place : H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (PF.O.getD PF.U) = piKOFull := by
  first
    | decide +kernel
    | rfl

variable {Z d}

/-- **The offline prover's own two halves are the halves of IOP's two jobs at these letters**, in scope. -/
theorem halves_are_jobs {Z' : VerifierAndGoals.PublicFiles} (hs : KeySourced Z' d.source d.numbers d.later)
    (scope : VerifierAndGoals.InScope Z' = true) :
    (offlineValue (files := Z) d).onU =
        proverSideOfProximityTest (JKU (X := Unit) AQ (bsOf (sendersAt Z d)) (stOf (sendersAt Z d))
                           (wtOf (sendersAt Z d)) (rdOf (sendersAt Z d))) ∧
      (offlineValue (files := Z) d).onOmega =
        (proverSideOfProximityTest (JKO (X := Unit) AQ (bsOf (sendersAt Z d)) (wtOf (sendersAt Z d))
                           (rdOf (sendersAt Z d))) : Placed Empty (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit).needsField := by
  have eP : d.later = PF := later_sourced hs scope
  have eQ : parKey d.source d.later = QK := par_sourced hs scope
  have eS : (sendersAt Z d).send = AQ := by
    show (⟨parKey d.source d.later, 0⟩ : SendPub) = ⟨QK, 0⟩
    rw [eQ]
  have eU : H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ d.later.U = piKUFull := by
    rw [eP]
    exact AtPublicFiles.KeyNineClosed.place_full
  have eO : H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (d.later.O.getD d.later.U) = piKOFull := by
    rw [eP]
    exact omega_place
  constructor
  · show proverSideOfProximityTest (AtPublicFiles.KeyLay.jobKU (X := Unit) (sendersAt Z d).send
                       (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ d.later.U) (bsOf (sendersAt Z d)) (stOf (sendersAt Z d))
                       (wtOf (sendersAt Z d)) (rdOf (sendersAt Z d))).toRun.toTest = _
    rw [eS, eU]
  · show (proverSideOfProximityTest (AtPublicFiles.KeyLay.jobKO (X := Unit) (sendersAt Z d).send
                       (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ d.later.U)
                       (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (d.later.O.getD d.later.U)) (bsOf (sendersAt Z d))
                       (wtOf (sendersAt Z d)) (rdOf (sendersAt Z d))).toRun.toTest :
      Placed Empty (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit).needsField = _
    rw [eS, eU, eO]

variable {P₁ Wt : Type} {K₀} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : Xi)

variable (Z d K₀) in
/-- The shared thread at the real value, tt laid. -/
abbrev threadValue :=
  threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk (ttValue Z d K₀) rest
    Kp Vd matrixReader (tableCoins Z) Z₀ w₀ rc x

variable (Z d K₀) in
/-- Its letter. -/
abbrev saidValue :=
  walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk (ttValue Z d K₀)
    rest Kp Vd matrixReader (tableCoins Z) Z₀ w₀ rc x

variable (Z d K₀) in
/-- **What the shared chain opens, at the real value.** -/
def LotOpensSharedAtValue : Prop :=
  ∀ {Z' : VerifierAndGoals.PublicFiles}, KeySourced Z' d.source d.numbers d.later → VerifierAndGoals.InScope Z' = true →
    fullPub = some K₀ →
    OpensShared d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk (ttValue Z d K₀)
      rest Kp Vd matrixReader (tableCoins Z) Z₀ w₀ rc x

theorem lotOpensSharedAtValue : LotOpensSharedAtValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x :=
  fun hs scope hK₀ => lotOpensShared d.source d.numbers d.later K₀ _ ℓ Nm Mg₀ tk rest Kp Vd matrixReader
    (tableCoins Z) Z₀ w₀ rc x _ _ _ _ _ hs scope hK₀

variable (Z d K₀) in
/-- **What the door asks of the shared chain, at the real value**: PlaysS at the two proximity tests is what is left at the members. -/
def LotDoorAsksSharedAtValue : Prop :=
  ∀ {Z' : VerifierAndGoals.PublicFiles}, KeySourced Z' d.source d.numbers d.later → VerifierAndGoals.InScope Z' = true →
    fullPub = some K₀ →
    ∀ sd : Seed (shapeOf (pubKey Z₀ d.source.chains)) × ℕ,
    x = ⟨oodSh (shapeOf (pubKey Z₀ d.source.chains)) (pubKey Z₀ d.source.chains)
      ⟨matrixReader w₀, tableCoins Z rc, sd⟩⟩ →
    Function.Injective Nm.tenant →
    (∀ b ∈ [9, 10], PlaysS (threadValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x)
      (saidValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x) b) →
    DoorAsks (threadValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x)
        (saidValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x) 12 ∧
      ∀ k, saidValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x 0 k
        (startAt (keyOf (pubKey Z₀ d.source.chains) d.source d.later (offlineValue (files := Z) d)
          matrixReader (tableCoins Z)) (some []) (inK w₀ rc x))

theorem lotDoorAsksSharedAtValue :
    LotDoorAsksSharedAtValue Z d K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x :=
  fun hs scope hK₀ sd hx hN h =>
    lotDoorAsksSharedTwo d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk
      (ttValue Z d K₀) rest Kp Vd matrixReader (tableCoins Z) Z₀ w₀ rc x hs scope hK₀ sd hx hN
      (place_p12At _ _) (place_p12At _ _)
      (lotOpensSharedAtValue ℓ Nm Mg₀ tk rest Kp Vd Z₀ w₀ rc x hs scope hK₀)
      (noStop_value _ _ _ _ _ _ _ _ _ _ _ _ _).2.1 h

end AtPublicFiles.KeyStandWalked.Lots

#print axioms AtPublicFiles.KeyStandWalked.Lots.omega_place
#print axioms AtPublicFiles.KeyStandWalked.Lots.halves_are_jobs
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotOpensSharedAtValue
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotDoorAsksSharedAtValue
