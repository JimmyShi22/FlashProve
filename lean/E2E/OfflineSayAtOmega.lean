-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSayAtOmega.lean: THE PREMISE OF TRUTH AT THE TEST ON OMEGA's GROUP (the shared chain's sub-protocol number 10), AT THE OFFLINE PROVER's OWN SHARED THREAD: the field `omega` of
`FourSayAtStands` (E2E/OfflineSayAtStand.lean), to the letter, AT tt := `ttLaid Z d K₀ Z₀ B` AND Kp := `keepsKey`, at every ℓ, Mg₀, tk, rest, Vd, Z₀ and every Nm whose tenant is injective.

  `ttLaid Z d K₀ Z₀ B`: the table's letter: `ttF` (E2E/TableFilled.lean) at the offline prover's senders.
  `omega_job_is`: at the written places the job `omegaJobAtFiles d` is `manyAtTen` (K12/AtKey/OAccepted.lean) at these senders.
  `key_at_tied`: a tied input's instance is the committer's sample at some seed (`validAt_of_tied`, E2E/KeyOodTie.lean, as `shared_at_tied`, E2E/OfflineSharedAtTied.lean, spends it).
  **`say_at_omega`**: the field.

NOT AT EVERY LETTER, unlike the field `folded` (E2E/OfflineSayAtFolded.lean): the law that is called reads the field of opened columns, which is had from the walk at the filled table and at `keepsKey`: so tt and Kp
are these two here. WHOEVER BUILDS A MEMBER OF `FourSayAtStands` MUST LAY THESE SAME tt AND Kp IN `TheLots` TOO.

By what. `say_at_stand_at_laid_ten` (Johnson/Desc/ProofFile/Honest/K12/AtKey/OSayLaid.lean) and the five ties of E2E/OfflineSayAtFolded.lean's head, each by unfolding once the later places are the
written ones. Its premises sd, hx are paid from `TiedAt`; hN stays.

Premises: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀ · Nm.tenant injective. B : Eight (parKey d.source PF) is a letter: in scope there is one (`plan_key`, `Plan2.eight`).

Limits. All content is that file's and what lies beneath it. `ThrS` at border 10 is a premise inside: no stand is shown here. The sentence reads the input and the coins: no later law may take it as a hypothesis on a run and
then speak of the coins as sampled anew. At the written sizes. Nothing on any property.
-/
import E2E.OfflineSayAtFolded
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OSayLaid
import E2E.KeyOodTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (plainMany)
open ProofFile.Honest.K12.AtKey (say_at_stand_at_laid_ten manyAtTen keepsKey)
open ProofFile.Honest.Term (tableCoins)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub omegaTestPlace)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyOodTie (validAt_of_tied)
open AtPublicFiles.KeyLay (bsOf)
open AtPublicFiles.StandAtNine (K1)
open AtPublicFiles.TableFilled (ttF)
open AtPublicFiles.HalvesAreJobs (bs_of)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (PF later_sourced)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open Bind.ForProver (shapeOf oodSh Seed)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) sayAtOmegaPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) sayAtOmegaRun : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) sayAtOmegaRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable (Z : PublicFiles)

/-- **The table's letter**: `ttF`, at the offline prover's senders. -/
abbrev ttLaid (d : OfflineDescription) (K₀ : KeyPub) (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF)) :=
  ttF K₀ d.source (K1 d.source (sendersFront Z d) matrixReader (tableCoins Z) Z₀) B ()

/-- **At the written places the job is `manyAtTen`, at the offline prover's senders.** -/
theorem omega_job_is (src : VerifiableInference.Desc.Key.Source) (num : H2U.PlaceNums) (Z₀ : ProofFile.Pub)
    (B : Eight (parKey src PF)) :
    omegaJobAtFiles (Z := Z) ⟨src, num, PF⟩ =
      manyAtTen (X₀ := Unit) src (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀)
        B := by
  have hb := bs_of src (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀) B rfl
  show AtPublicFiles.KeyLay.jobKO (X := Unit) _ _ _
    (bsOf (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀)) _ _ = _
  rw [hb]
  rfl

variable {Z} {d : OfflineDescription} {K₀ : KeyPub}

/-- **A tied input's instance is the committer's sample at some seed.** -/
theorem key_at_tied (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (Z₀ : ProofFile.Pub) (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : TiedAt Z d w x) :
    ∃ sd : Seed (shapeOf (pubKey Z₀ d.source.chains)) × ℕ,
      x = ⟨oodSh (shapeOf (pubKey Z₀ d.source.chains)) (pubKey Z₀ d.source.chains)
        ⟨matrixReader w.1, tableCoins Z w.2.1, sd⟩⟩ := by
  have sourced := sourced_of_ok live hd
  have hk := AtPublicFiles.AtFiles.sized_sourced sourced scope
  obtain ⟨sd, hsd⟩ := validAt_of_tied Z rfl ht Z₀ d.source.chains hk
  refine ⟨sd, ?_⟩
  cases x with
  | mk key => exact congrArg Xi.mk hsd

variable {P₁ Wt : Type} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF))

/-- **THE FIELD `omega` OF `FourSayAtStands`**, at tt := ttLaid and Kp := keepsKey. -/
theorem say_at_omega (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hN : Function.Injective Nm.tenant) :
    ∀ w x, TiedAt Z d w x →
      SayAtStand Empty (omegaJobAtFiles (Z := Z) d).toRun.toTest (plainMany (omegaJobAtFiles (Z := Z) d))
        1 omegaTestPlace
        (ThrS (sharedThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d w x)
          (sharedSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d w x) 10) := by
  intro w x ht
  obtain ⟨sd, hx⟩ := key_at_tied hd scope live Z₀ w x ht
  have hs := sourced_of_ok live hd
  clear hd ht
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  rw [omega_job_is Z src num Z₀ B]
  exact say_at_stand_at_laid_ten src num K₀ (sendersFront Z ⟨src, num, PF⟩) ℓ Nm Mg₀ tk rest Vd matrixReader
    (tableCoins Z) Z₀ w.1 w.2.1 x B () (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) ⟨src, num, PF⟩).rng
    (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) ⟨src, num, PF⟩).own hs scope hK₀ sd hx hN

/-- A TEST OF THE WORDS, no payment: the two drop into `FourSayAtStands` at these letters as its fields `folded` and `omega`. -/
example {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) (hN : Function.Injective Nm.tenant)
    (F₀ : FourSayAtStands ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d U₁ U₃ S₁ S₃) :
    FourSayAtStands ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d U₁ U₃ S₁ S₃ :=
  { F₀ with
    folded := say_at_folded ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ hd scope live hK₀
    omega := say_at_omega ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live hK₀ hN }

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.omega_job_is
#print axioms AtPublicFiles.OfflineRows.key_at_tied
#print axioms AtPublicFiles.OfflineRows.say_at_omega
