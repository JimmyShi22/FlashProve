-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSayAtFolded.lean: THE PREMISE OF TRUTH AT THE TEST ON THE FOLDED ROW's GROUP (the shared chain's sub-protocol number 9), AT THE OFFLINE PROVER's OWN SHARED THREAD: the field
`folded` of `FourSayAtStands` (E2E/OfflineSayAtStand.lean), to the letter, AT EVERY VALUE OF THE JOIN's LETTERS ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀.

  `sendersFront Z d`: the senders under the laying: what `offlineSenders d` hands to `withStoredColumnsAndPlan`.
  `folded_job_is`: at the written places the job `foldedJobAtFiles d` is `AN` (E2E/SaysAtNine.lean) at these senders (`job_is_written`, K12/AtKey/USays.lean).
  **`say_at_folded`**: the field.

By what. `says_in_front_at_key` (Johnson/Desc/ProofFile/Honest/K12/AtKey/USays.lean), which speaks of the thread `TU` at a free table letter tt, and five ties, each
by unfolding once the later places are the written ones (`later_sourced`): offlineSenders d is keyOf (pubKey Z₀ …) … (sendersFront Z d) … · d.later = PF · offlineTestParametersOnU PF,
offlineTestOnOmega PF are pU, pO · the join's table is tbKey at the senders' own readers · `withTests` unfolded: the shared thread reads neither its rng nor its own.

Premises: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀. `TiedAt` stands in the statement, as in the field; the proof does not read it.

Limits. All content is that file's and what lies beneath it. The thread's invariant with its letter (`ThrS` at border 9) is a premise inside: no stand is shown here. The sentence reads the input and
the coins: no later law may take it as a hypothesis on a run and then speak of the coins as sampled anew. At the written sizes. Nothing on any property.
-/
import E2E.OfflineSayAtStand
import Johnson.Desc.ProofFile.Honest.K12.AtKey.USays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (plainMany)
open ProofFile.Honest.K12.Light.ItemLaws (AN)
open ProofFile.Honest.K12.AtKey (says_in_front_at_key job_is_written)
open ProofFile.Honest.Term (matrixInput tableCoins)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace)
open AtPublicFiles.KeySharedThread (parKey plan_key)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyValues (WitK faceAt keyBatt withSendingsAndLookups)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open AtPublicFiles.StandAtNine (K1)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (PF par_sourced later_sourced)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) sayAtFoldedPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) sayAtFoldedRun : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) sayAtFoldedRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable (Z : PublicFiles)

/-- The senders under the laying. -/
abbrev sendersFront (d : OfflineDescription) : KeyParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Unit Unit WitK :=
  withSendingsAndLookups
    (fixedKeyParts (faceAt d.source 0) (keyBatt d.source) matrixInput.dummy () () idleRecord)
    d.source d.numbers matrixReader matrixInput.inRange matrixInput.dummy

/-- **At the written places the job is `AN`, at the offline prover's senders.** -/
theorem folded_job_is (src : VerifiableInference.Desc.Key.Source) (num : H2U.PlaceNums) (Z₀ : ProofFile.Pub)
    (B : Eight (parKey src PF)) :
    foldedJobAtFiles (Z := Z) ⟨src, num, PF⟩ =
      AN (X₀ := Unit) src (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀) B :=
  (job_is_written src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀ B).symm

variable {Z} {d : OfflineDescription} {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **THE FIELD `folded` OF `FourSayAtStands`**, at every value of the join's letters. -/
theorem say_at_folded (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) :
    ∀ w x, TiedAt Z d w x →
      SayAtStand Empty (foldedJobAtFiles (Z := Z) d).toRun.toTest (plainMany (foldedJobAtFiles (Z := Z) d))
        1 foldedTestPlace (ThrS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x)
          (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) 9) := by
  intro w x _
  have hs := sourced_of_ok live hd
  clear hd
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  obtain ⟨B⟩ := hQ.eight
  rw [folded_job_is Z src num Z₀ B]
  intro k st m₀ E₀ c hA hc
  exact says_in_front_at_key K₀ hK₀ src num
    (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀) ℓ Nm Mg₀ tk rest Kp Vd _ B tt
    (par_sourced hs scope) hQ hA.1 c hc

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.folded_job_is
#print axioms AtPublicFiles.OfflineRows.say_at_folded
