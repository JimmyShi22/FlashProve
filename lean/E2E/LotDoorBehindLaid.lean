-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotDoorBehindLaid.lean: THE DOOR AT THE VALUE: DoorBehindS, the eighth clause of AtRunS (E2E/KeyAcceptPairs.lean), at the offline prover's own senders and the written book, at U₁, S₁ := laidFirst, laidSaid
(E2E/LotJoinLaid.lean), U₂, S₂ := valueThread, valueSaid (E2E/LotJoinSharedAtValue.lean), U₃, S₃ := lastThread, lastSaid (E2E/OfflineLastTerms.lean) at these letters: at every tied input, all coins of the run
and whatever «ready» has prepared. NO PREMISE ON ANY MEMBER, ON A STAND OR ON A LETTER.

  lastLaid, lastSaidLaid   U₃, S₃ at the laid letters
  sharedAtParts, sharedSaidAtParts, lastAtParts, lastSaidAtParts, door_at_parts   the same four terms with the key's parts as a letter Kv, and the door there where Kv is the senders' value: so that Lean meets
                         «keyAtValue is offlineValue» once, as one rfl, and not inside every term
  key_fits_laid          at a tied input the key fits the sizes (keyFits_of_tied); for its instances three local ones stand in front: doorBehindLaidPad, doorBehindLaidRun, doorBehindLaidRunDefault
  LotDoorBehindLaid, lotDoorBehindLaid   THE STATEMENT, from: the offline description is returned, in scope, protocolDataWellFormed, fullPub = some K₀

BY WHAT: a call of door_at_Th (E2E/KeyDoorWhole.lean) with: D₁, D₂ (AtPublicFiles.KeyLastChain.DoorAsks): lotDoorAsksFirstLaid, lotDoorAsksSharedLaid · hfit: door_fits, keyFits_of_tied (E2E/KeyDoorFits.lean) · hw₂: rfl · hown, hw: ready_ok · hVd: trivial ·
hdot: hdot_own (E2E/KeyLastNumbers.lean) with firstPublic_atValue, w_public, lotHeardOfFold.

What it does not say. DoorBehindS is a conditional on a pair at each of the two last borders: no stand is shown here (the first chain's: E2E/LotStandLaid.lean; the shared thread's at valueThread and valueSaid: not shown here). It is as strong as
what lies beneath: the first half stands above the side library (through lookupsFive_laid); the shared half on IOP's trial, on no row (through E2E/LotOpensShared.lean), and on trials at members 9 and 10; the door's own files are typed by another
house. tk, rest, Z₀ stay letters. Nothing on the last chain's members. Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
import E2E.LotDoorAsksFirstLaid
import E2E.LotDoorAsksSharedLaid
import E2E.LotHeardOfFold
import E2E.KeyDoorWhole
import E2E.KeyDoorFits
import E2E.KeyLastNumbers
import E2E.OfflineLastTerms
import E2E.FirstHWPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12.AtKey (keepsKey)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader sourced_of_ok valueThread valueSaid TiedAt
  lastThread lastSaid keyAtValue dValue dtValue dTValue dMValue idleDot door_fits keyFits_of_tied)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (inK startAt)
open AtPublicFiles.KeyStandFull (idleNm idleMg)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyStandWalked.Lots (ttValue lotDoorAsksSharedLaid)
open AtPublicFiles.KeyLastChain (door_at_Th hdot_own mlKey val₁Key threadOwn saidOwn)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) doorBehindLaidPad : Nonempty AtPublicFiles.Committed.PadZ :=
  AtPublicFiles.Committed.pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) doorBehindLaidRun : Nonempty AtPublicFiles.AtFiles.HonestTerm.RunValue := ⟨fun _ => 0⟩

local instance (priority := high) doorBehindLaidRunDefault : Inhabited AtPublicFiles.AtFiles.HonestTerm.RunValue :=
  ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

variable
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Words Cb.Gl.E)
  (Z₀ : ProofFile.Pub)

variable (Z d K₀) in
/-- **U₃ at the laid letters.** -/
abbrev lastLaid (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  lastThread WitLens.words idleNm (fun _ => idleMg) tk (ttValue Z d K₀) rest keepsKey (fun _ => True) Z₀ d
    (laterValue Z d K₀) (laidSaid Z d K₀) w x

variable (Z d K₀) in
/-- **S₃ at the laid letters.** -/
abbrev lastSaidLaid (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  lastSaid WitLens.words idleNm (fun _ => idleMg) tk (ttValue Z d K₀) rest keepsKey (fun _ => True) Z₀ d
    (laterValue Z d K₀) (laidSaid Z d K₀) w x

variable (Z d K₀) in
/-- **The door at the value: AtRunS's eighth clause.** -/
def LotDoorBehindLaid : Prop :=
  offlineDescription Z = .ok d → InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → fullPub = some K₀ →
    ∀ (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi), TiedAt Z d w x → ∀ (k : Coins (keyBook K₀)) R,
      ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀) (keyProver (offlineValue (files := Z) d)) w.1 w.2.1
        x k = .ok R →
      DoorBehindS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
        (laidFirst Z d K₀ w x) (valueThread (d := d) tk rest Z₀ w x) (lastLaid Z d K₀ tk rest Z₀ w x)
        (laidSaid Z d K₀ w x) (valueSaid (d := d) tk rest Z₀ w x) (lastSaidLaid Z d K₀ tk rest Z₀ w x) x k R

section Parts
variable (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) (Kv : KeyParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Unit Unit WitK)

variable (Z d K₀) in
/-- The shared thread with the key's parts as a letter. -/
abbrev sharedAtParts :=
  threadKey d.source d.numbers d.later Kv WitLens.words idleNm (fun _ => idleMg)
    (tableKey d.source d.later K₀ Kv tk (ttValue Z d K₀)) rest keepsKey (fun _ => True) (inK w.1 w.2.1 x)

variable (Z d K₀) in
/-- Its letter. -/
abbrev sharedSaidAtParts :=
  WalkedFrom (sharedAtParts Z d K₀ tk rest w x Kv) (fun _ m => m = startAt Kv (some []) (inK w.1 w.2.1 x))

variable (Z d K₀) in
/-- The last thread with the key's parts as a letter, where E2E/OfflineLastTerms.lean has keyAtValue. -/
abbrev lastAtParts :=
  threadOwn d.source d.numbers d.later Kv
    (fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀) x)
    WitLens.words idleNm (fun _ => idleMg) (tableKey d.source d.later K₀ Kv tk (ttValue Z d K₀)) rest keepsKey
    (fun _ => True) (inK w.1 w.2.1 x) w.1 w.2.1 x (keyProver Kv).first
    (tbH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀))
    (laidSaid Z d K₀ w x) (sharedSaidAtParts Z d K₀ tk rest w x Kv) (dValue d x)
    (dtValue d (laterValue Z d K₀) x)
    (mlKey (val₁Key d.source (fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader
      (laterValue Z d K₀) x))) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x)

variable (Z d K₀) in
/-- Its letter. -/
abbrev lastSaidAtParts :=
  saidOwn d.source d.numbers d.later Kv
    (fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀) x)
    WitLens.words idleNm (fun _ => idleMg) (tableKey d.source d.later K₀ Kv tk (ttValue Z d K₀)) rest keepsKey
    (fun _ => True) (inK w.1 w.2.1 x) w.1 w.2.1 x (keyProver Kv).first
    (tbH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀))
    (laidSaid Z d K₀ w x) (sharedSaidAtParts Z d K₀ tk rest w x Kv) (dValue d x)
    (dtValue d (laterValue Z d K₀) x)
    (mlKey (val₁Key d.source (fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader
      (laterValue Z d K₀) x))) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x)

omit tk rest Z₀ Kv in
/-- At a tied input the key fits the sizes. -/
theorem key_fits_laid (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (ht : TiedAt Z d w x) (Z₁ : ProofFile.Pub) :
    VerifiableInference.Desc.Own.keyFits (inK (Rc := (protocolAtFiles Z).EncodingRandomness) w.1 w.2.1 x).key
      AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true :=
  keyFits_of_tied (sourced_of_ok live hd) scope rfl ht Z₁

/-- **The door with the key's parts as a letter that is the senders' value.** -/
theorem door_at_parts (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK : fullPub = some K₀)
    (hfit : VerifiableInference.Desc.Own.keyFits (inK (Rc := (protocolAtFiles Z).EncodingRandomness) w.1 w.2.1 x).key
      AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true)
    (e : Kv = offlineValue (files := Z) d)
    (D₂ : AtPublicFiles.KeyLastChain.DoorAsks (sharedAtParts Z d K₀ tk rest w x Kv)
      (sharedSaidAtParts Z d K₀ tk rest w x Kv) 12)
    (k : Coins (keyBook K₀)) (R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi TableKey Unit Unit Unit)
    (hown : R.own = ⟨w.1, w.2.1, x, ()⟩) :
    DoorBehindS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
      (laidFirst Z d K₀ w x) (sharedAtParts Z d K₀ tk rest w x Kv) (lastAtParts Z d K₀ tk rest w x Kv)
      (laidSaid Z d K₀ w x) (sharedSaidAtParts Z d K₀ tk rest w x Kv)
      (lastSaidAtParts Z d K₀ tk rest w x Kv) x k R := by
  subst e
  have hs := sourced_of_ok live hd
  exact door_at_Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀)
    WitLens.words idleNm (fun _ => idleMg)
    (tableKey d.source d.later K₀ (offlineValue (files := Z) d) tk (ttValue Z d K₀)) rest keepsKey
    (fun _ => True) (inK w.1 w.2.1 x) w.1 w.2.1 x (laidSaid Z d K₀ w x)
    (sharedSaidAtParts Z d K₀ tk rest w x (offlineValue (files := Z) d)) (dValue d x)
    (dtValue d (laterValue Z d K₀) x)
    (mlKey (val₁Key d.source (fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader
      (laterValue Z d K₀) x))) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x) hs scope
    (lotDoorAsksFirstLaid Z d K₀ hd scope live hK w x) D₂
    (door_fits hfit) rfl k R hown hown trivial
    (fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ y ds =>
      hdot_own WitLens.words idleNm (fun _ => idleMg)
        (tableKey d.source d.later K₀ (offlineValue (files := Z) d) tk (ttValue Z d K₀)) rest keepsKey
        (fun _ => True) (inK w.1 w.2.1 x) hs scope hK (firstPublic_atValue hs scope) (w_public hs scope)
        (lotHeardOfFold hs scope) rfl rfl idleDot k u₁.1 u₂.1 y ds)

end Parts

theorem lotDoorBehindLaid : LotDoorBehindLaid Z d K₀ tk rest Z₀ := by
  intro hd scope live hK w x ht k R hR
  obtain ⟨-, ⟨⟩, -, hown, -⟩ := ready_ok hR
  exact door_at_parts tk rest w x (keyAtValue (Z := Z) Z₀ d) hd scope live hK
    (key_fits_laid w x hd scope live ht Z₀) rfl
    (lotDoorAsksSharedLaid tk rest Z₀ hd scope live hK w x ht) k R hown

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.key_fits_laid
#print axioms AtPublicFiles.FirstH.Lots.door_at_parts
#print axioms AtPublicFiles.FirstH.Lots.lotDoorBehindLaid
