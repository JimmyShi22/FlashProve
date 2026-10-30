-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheCapstone.lean: completeness as an IOP at the stored files, from the statements
that stand open, each by name. The binders of complete_at_the_stored_files are all that is left of
it; what is paid here is paid by theorem.

  complete_at_the_stored_files   CompleteAtFiles at storedPublicFiles, and the same at every coin of the prover

Paid by theorem, here or in theHonestPart_stored. The two tests on the files (scope_named,
live_named); that the work bits are faithful (workFaithful_atFiles); that a served request lies in the object's relation
(servedRequest_below); the sum (rooms_add). The compiled part of honestProversAndSettingsAtFiles is not touched here.

The binders. hM hP hC hD: the public functions return. G, hG: sides whose prover is the return's. off:
the offline list, its three measures within their rooms. laid: the head's return is the online maker's. yes: the verdict at
the run. bad, hid: the online family's two measures, within their rooms. paid, e₁, e₂, e₃: the falls.

Limits. An implication: nothing here says that a binder holds. P is a letter. Nothing on soundness or
hiding.
-/
import E2E.CompleteAsIOPAtNamed
import E2E.CompleteAsIOPAtTheSides
import E2E.CompleteAsIOPServedLaws
import E2E.CompleteAsIOPWorkBits
import E2E.TheRooms

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles readFiles settingsOfRead)
open FlashProve (allZeroDigest committerCoinCountLessOne)
open OnBytes.Prover (CompleteAtEveryCoin)
open VerifiableInference.Compilation (theProvers)
open AtPublicFiles.TheFalls (theFalls₁)
open AtPublicFiles.TheRooms (rooms_add)
open P5J

local instance (priority := high) nonemptyPadZ_capstone : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_capstone : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_capstone : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- **Completeness as an IOP at the stored files, from what stands open.** -/
theorem complete_at_the_stored_files (hZ : Z = VerifierAndGoals.storedPublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : OnlineSides returned places firstChain) (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM} {kB kH kF : ℝ≥0∞}
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (roomKB : kB ≤ AtPublicFiles.TheRooms.offlineBadRoom) (roomKH : kH ≤ AtPublicFiles.TheRooms.offlineHidRoom)
    (roomKF : kF ≤ AtPublicFiles.TheRooms.offlineFallRoom)
    (laid : ∃ (D : WholeD) (r : LPFD.Full.RunPF),
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r returned.Z places firstChain)
    (yes : YesZ allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H
      (TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H
        (ServedRequest committerCoinCountLessOne Z hr) fun _ _ => ∅))
    {zB z : ℝ≥0∞}
    (bad : BadSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H) zB)
    (hid : HidSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
        returned.H)
      (fun n w a => TiedYes Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
        returned.H (ServedRequest committerCoinCountLessOne Z hr) n w (instanceAsPlainRecord a)) z)
    (paid : TheFallsArePaid Z (ServedRequest committerCoinCountLessOne Z hr))
    (e₁ : G.falls₁ = theFalls₁ returned.Z places firstChain returned.G
      (theSlots returned places firstChain))
    (e₂ : G.falls₂ = []) (e₃ : G.falls₃ = [])
    (roomBad : zB ≤ AtPublicFiles.TheRooms.onlineBadRoom) (roomHid : z ≤ AtPublicFiles.TheRooms.onlineHidRoom) :
    CompleteAtFiles Z P hr ∧
      CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) P) (workAtFiles Z)
        (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + fallsRoom) := by
  have named : VerifierAndGoals.NamedFiles Z := Or.inl hZ
  have on : OnlineDebtsNamed returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z
      fallsRoom :=
    ⟨laid, fun _ _ h => servedRequest_below committerCoinCountLessOne Z (scope_named named) hr h, yes, bad, hid,
      falls_of_paid returned places firstChain G hG paid hM hP hC e₁ e₂ e₃⟩
  exact theHonestPart_at_named P returned places firstChain description named hr hM hP hC hD G hG
    (workFaithful_atFiles Z) off on
    (rooms_add roomKB roomKH roomKF roomBad roomHid le_rfl)

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.complete_at_the_stored_files
