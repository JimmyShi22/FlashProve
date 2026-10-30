-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtNamed.lean: completeness from lists at the named files (VerifierAndGoals.NamedFiles: the two
named sets of public files), and at the stored files storedPublicFiles alone. There the two tests on the public
files are theorems, so the online list asks neither. It states no goal.

  scope_named, live_named   the public facts at the named files
  OnlineDebtsNamed    OnlineDebts without scope and live
  theHonestPart_at_named   both forms at the named files, from lists at those files alone
  CompleteAtFiles, theHonestPart_stored   the body at given files, and at storedPublicFiles, the stored files

By what. VerifierAndGoals.filesRead; headJoins_named (AtFullSide/Top/HeadJoins.lean).

Limits. Side library, through headJoins_named. The lists stay hypotheses.
-/
import E2E.CompleteAsIOPAtTheProvers
import AtFullSide.Top.HeadJoins

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (ProverCoinCounts Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead NamedFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin ofRecs)
open VerifiableInference.Compilation (theProvers)
open P5J

local instance (priority := high) nonemptyPadZ_atNamed : Nonempty PadZ :=
  pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_atNamed : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_atNamed : Inhabited RunValue := ⟨fun _ => 0⟩

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap

/-- The named files are in scope. -/
theorem scope_named {Z : PublicFiles} (hZ : NamedFiles Z) : InScope Z = true := by
  rcases hZ with rfl | rfl
  · exact VerifierAndGoals.filesRead.full.1
  · exact VerifierAndGoals.filesRead.other.1

/-- The named files pass the head's test. -/
theorem live_named {Z : PublicFiles} (hZ : NamedFiles Z) : protocolDataWellFormed (asDescriptionFiles Z) = true :=
  (AtFullSide.Top.headJoins_named Z hZ).1

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- **The online list at the named files**: without the two tests on the files. -/
structure OnlineDebtsNamed (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness
      TableKey _ _ _) (Relation : FullSizeMatrix → XF → Prop) (zB z pF : ℝ≥0∞) : Prop where
  laid : ∃ (D : WholeD) (r : LPFD.Full.RunPF),
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r returned.Z places firstChain
  below : ∀ i x, Relation i x → RyesZ Z i x
  yes : YesZ allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
    returned.H
    (TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H
      Relation fun _ _ => ∅)
  bad : BadSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
    returned.H) zB
  hid : HidSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H)
    (fun n w a => TiedYes Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H Relation n w (instanceAsPlainRecord a)) z
  falls : FallSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H)
    (fallG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H)
    (fun n w a => TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H Relation (fun _ _ => ∅) n w (instanceAsPlainRecord a)) pF

/-- **Both forms at the named files, from the lists.** -/
theorem theHonestPart_at_named (hZ : NamedFiles Z) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM}
    {kB kH kF zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (on : OnlineDebtsNamed returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z pF)
    (hsum : (kB + kH + kF) + 0 + (zB + z + pF) ≤ completenessTarget) :
    CompleteOnServedRequests Z hr (theProvers Z (settingsOfRead pp) P) ∧
      CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) P) (workAtFiles Z)
        (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + pF) := by
  have b := theHonestPart_of_lists P returned places firstChain description hr hM hP hC hD G hG hf
    off ⟨scope_named hZ, live_named hZ, on.laid, on.below, on.yes, on.bad, on.hid, on.falls⟩ hsum
  exact ⟨b.1 (scope_named hZ) (live_named hZ), b.2⟩

/-- **The body of the last line at given files**: completeness as an IOP of the provers there. -/
def CompleteAtFiles (Z : PublicFiles) (P : Parts Z) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) : Prop :=
  CompleteOnServedRequests Z hr (theProvers Z (settingsOfRead pp) P)

/-- **The body at the stored files, from lists at those files alone.** Z is the letter of storedPublicFiles: the
stored files' bytes are not unfolded here. -/
theorem theHonestPart_stored (hZ : Z = VerifierAndGoals.storedPublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM}
    {kB kH kF zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (on : OnlineDebtsNamed returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z pF)
    (hsum : (kB + kH + kF) + 0 + (zB + z + pF) ≤ completenessTarget) :
    CompleteAtFiles Z P hr :=
  (theHonestPart_at_named P returned places firstChain description (Or.inl hZ) hr hM hP hC hD G hG
    hf off on hsum).1

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.theHonestPart_stored
#print axioms AtPublicFiles.AtFiles.HonestTerm.theHonestPart_at_named
