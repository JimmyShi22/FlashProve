-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtTheSides.lean: both forms of completeness at the provers under refuseUnserved,
at any sides whose prover is the return's, at fallsRoom, the number that TheFallsArePaid bounds the
falls by. It states no goal.

Limits. As E2E/CompleteAsIOPBothForms.lean.
-/
import E2E.CompleteAsIOPBothForms
import E2E.TheFalls

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (PublicFiles readFiles)
open FlashProve (committerCoinCountLessOne)
open OnBytes.Prover (CompleteAtEveryCoin ofRecs)
open AtPublicFiles.TheFalls (theFalls₁)
open VerifiableInference.Compilation (CompleteInParts)
open P5J

local instance (priority := high) nonemptyPadZ_atTheSides : Nonempty PadZ := pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_atTheSides : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_atTheSides : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- **Both forms, at any sides whose prover is the return's, at the room for the falls.** -/
theorem bothForms_at_sides (G : OnlineSides returned places firstChain)
    (hG : G.prover returned.H = returned.H)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM}
    {kB kH kF zB z : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (on : OnlineDebts returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z fallsRoom) :
    CompleteInParts (protocolAtFiles Z)
        ((ofRecs (honestProvers Z P)).refuseUnserved (ServedRequest committerCoinCountLessOne Z hr))
        (workAtFiles Z) (copyNumberAtFiles Z) (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0
        (zB + z + fallsRoom) ∧
      CompleteAtEveryCoin (protocolAtFiles Z)
        ((ofRecs (honestProvers Z P)).refuseUnserved (ServedRequest committerCoinCountLessOne Z hr))
        (workAtFiles Z) (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + fallsRoom) :=
  bothForms_of_lists P returned places firstChain description hr hM hP hC hD G hG hf off on

/-- **TheFallsArePaid gives the field falls at those sides, where they hold the lists.** -/
theorem falls_of_paid (G : OnlineSides returned places firstChain)
    (hG : G.prover returned.H = returned.H) {Relation : FullSizeMatrix → LPFD.Full.XF → Prop}
    (paid : TheFallsArePaid Z Relation) (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (e₁ : G.falls₁ = theFalls₁ returned.Z places firstChain returned.G
      (theSlots returned places firstChain))
    (e₂ : G.falls₂ = []) (e₃ : G.falls₃ = []) :
    FallSmall
      (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H)
      (fallG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H)
      (fun n w a => TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
        returned.H Relation (fun _ _ => ∅) n w (LPFD.Full.instanceAsPlainRecord a)) fallsRoom :=
  paid returned places firstChain hM hP hC G hG e₁ e₂ e₃

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.bothForms_at_sides
#print axioms AtPublicFiles.AtFiles.HonestTerm.falls_of_paid
