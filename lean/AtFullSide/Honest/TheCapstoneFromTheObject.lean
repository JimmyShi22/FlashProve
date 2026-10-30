-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheCapstoneFromTheObject.lean: CONDITIONAL. Completeness as an IOP of the provers at
`thePartsAt`, at any public files under a head that pass the policy's test, from two things alone: a
value of `TheOneObject` (AtFullSide/Honest/TheOneObject.lean) and the offline list within its rooms.
`theHonestPart_of_lists` (E2E/CompleteAsIOPAtTheProvers.lean) is called with the whole online list
laid in.

  `baseBad_empty`                  where neither test on first stops fires, the public abort set is empty
  `bad_at_the_online_return`       the field bad at 0, at any sides whose prover is the online return's
  `online_debts_from_the_object`   `OnlineDebts` at the sides that completeness is stated with
  `complete_from_the_object`       **the statement**, at one return of the base maker, one head, one value
  `complete_from_the_object_at_every_return`   the same where each return and head has a value: that
                                   there are a return and a head is shown
  `complete_from_the_object_stored`   at the stored full-size files

By what. yes: `yes_of_theOneObject_paid` (AtFullSide/Honest/TheLastLinePaid.lean), its three letters
read off the bound input and coin. bad: `badB_base`, `stop0B_base` (Johnson/P1K8R/CalmAtBase.lean)
through `badSmall_at_base` (E2E/CompleteAsIOPStopsAtBase.lean). hid: `hid_at_the_capstone`,
`hid_in_room` (AtFullSide/K8/HidAtTheCapstone.lean). falls: `falls_of_paid` at `falls_at_live`
(AtFullSide/K8/FallsAtLive.lean). The offline description is there by `description_of_live`
(E2E/KeyK1/KeyK1AtTerm.lean).

Not shown here. No value of the object is made: each of its fields is a hypothesis. The offline list is
a hypothesis. The two Inhabited instances are letters: the end reads neither.

No property is claimed.
-/
import AtFullSide.Honest.TheCapstone
import AtFullSide.Honest.TheLastLinePaid
import AtFullSide.K1.HeadAtBaseMaker
import AtFullSide.K8.FallsAtLive
import AtFullSide.K8.HidAtTheCapstone
import E2E.CompleteAsIOPStopsAtBase
import E2E.KeyArgumentsAt
import E2E.KeyK1.KeyK1AtTerm
import Johnson.P1K8R.CalmAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells onlineProverFromPublicFiles Prover badB stop0B key_of_atPure)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput matrixFilling tableCoins)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin)
open VerifiableInference.Compilation (theProvers)
open AtPublicFiles.TheRooms (rooms_add)
open AtFullSide.Honest (TheOneObject onlineReturn onlineMaker_returns yes_of_theOneObject_paid
  theSides theSides_fit)
open P5J

local instance (priority := high) nonemptyPadZ_fromTheObject : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_fromTheObject : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_fromTheObject : Inhabited RunValue :=
  ⟨fun _ => 0⟩

/-- Where neither test on first stops fires, the public abort set at the prover is empty. -/
theorem baseBad_empty {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type} (C : _root_.Run.PQ.CK) (D : WholeD)
    (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (hb : ∀ ds, badB F H ds = false)
    (hs : ∀ ds, stop0B F H ds = false) : baseBad C D tF tJ t3 F silent H = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => ?_
  obtain g | g := (show _ ∨ _ from hρ)
  · rw [hb] at g
    cases g
  · rw [hs] at g
    cases g

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {pp : Inst.Model.ScalesAndPolicy}

/-- **The field bad, at 0**, at any sides whose prover is the online return's. -/
theorem bad_at_the_online_return
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) (G : OnlineSides (onlineReturn Z A) places firstChain)
    (hG : G.prover (onlineReturn Z A).H = (onlineReturn Z A).H) :
    BadSmall (famG Z (onlineReturn Z A).Z places firstChain runValueBytes runValueBytes
      (onlineReturn Z A).B G (onlineReturn Z A).H) 0 := by
  refine badSmall_at_base Z (onlineReturn Z A).Z places firstChain runValueBytes runValueBytes
    (onlineReturn Z A).B G id (tableCoins Z) matrixInput.dummy A.H hG (key_of_atPure made).symm ?_
  rw [baseBad_empty _ _ _ _ _ _ _ A.H (P1K8.badB_base made _) (P1K8.stop0B_base made _)]
  unfold prRho
  rw [pr_empty]

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- CONDITIONAL: on the object's value. **The online list, from a value of the one object.** -/
theorem online_debts_from_the_object (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (h : HeadAtReturn Z A)
    (O : TheOneObject h hr) :
    OnlineDebts (onlineReturn Z A) h.places h.firstChain (theSides h)
      (ServedRequest committerCoinCountLessOne Z hr) 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) fallsRoom where
  scope := h.head.scope
  live := live
  laid := ⟨_, _, h.head.toAtMg.laid⟩
  below := fun _ _ g => servedRequest_below committerCoinCountLessOne Z h.head.scope hr g
  yes := fun n w x c hx => yes_of_theOneObject_paid live made O w.2.1 w.2.2 c n w x c hx
  bad := bad_at_the_online_return made _ _ _ (theSides_fit (h := h)).prover
  hid := hid_at_the_capstone h.head.scope hr live (onlineMaker_returns made)
    h.head.toAtMg.laid.places h.head.toAtMg.laid.chain _ (theSides_fit (h := h)).prover
  falls := falls_of_paid (onlineReturn Z A) h.places h.firstChain (theSides h)
    (theSides_fit (h := h)).prover (falls_at_live h.head.scope hr live _)
    (onlineMaker_returns made) h.head.toAtMg.laid.places h.head.toAtMg.laid.chain
    (theSides_fit (h := h)).falls₁ (theSides_fit (h := h)).falls₂ (theSides_fit (h := h)).falls₃

/-- CONDITIONAL: on the object's value and the offline list. **Completeness as an IOP at any public
files under a head that pass the policy's test.** -/
theorem complete_from_the_object (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (h : HeadAtReturn Z A)
    (O : TheOneObject h hr)
    (off : ∀ description : OfflineDescription, offlineDescription Z = .ok description →
      ∃ (FT : AtPublicFiles.KeyBridge.FallT (offlineAt (thePartsAt Z) description))
        (Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)) (kB kH kF : ℝ≥0∞),
        OfflineDebts Z (keyFileDescription description.source description.numbers description.later)
          (thePartsAt Z).book ((thePartsAt Z).prover description) runValueBytes runValueBytes
          (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF ∧
        kB ≤ AtPublicFiles.TheRooms.offlineBadRoom ∧ kH ≤ AtPublicFiles.TheRooms.offlineHidRoom ∧
          kF ≤ AtPublicFiles.TheRooms.offlineFallRoom) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c := by
  obtain ⟨d, hd, -⟩ := AtPublicFiles.KeyK1.description_of_live live
  obtain ⟨FT, Tied, TiedM, kB, kH, kF, D, r₁, r₂, r₃⟩ := off d hd
  have sum := rooms_add r₁ r₂ r₃ (zero_le _) hid_in_room (le_refl fallsRoom)
  have b := theHonestPart_of_lists (thePartsAt Z) (onlineReturn Z A) h.places h.firstChain d hr
    (onlineMaker_returns made) h.head.toAtMg.laid.places h.head.toAtMg.laid.chain hd (theSides h)
    (theSides_fit (h := h)).prover (workFaithful_atFiles Z) D
    (online_debts_from_the_object live hr made h O) sum
  exact ⟨b.1 h.head.scope live, _, _, sum, b.2⟩

/-- CONDITIONAL. **The same where each return of the base maker and each head there has a value of
the object.** That there are such a return and such a head is shown. -/
theorem complete_from_the_object_at_every_return (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hr : readFiles Z = .ok pp)
    (object : ∀ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A →
      ∀ h : HeadAtReturn Z A, Nonempty (TheOneObject h hr))
    (off : ∀ description : OfflineDescription, offlineDescription Z = .ok description →
      ∃ (FT : AtPublicFiles.KeyBridge.FallT (offlineAt (thePartsAt Z) description))
        (Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)) (kB kH kF : ℝ≥0∞),
        OfflineDebts Z (keyFileDescription description.source description.numbers description.later)
          (thePartsAt Z).book ((thePartsAt Z).prover description) runValueBytes runValueBytes
          (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF ∧
        kB ≤ AtPublicFiles.TheRooms.offlineBadRoom ∧ kH ≤ AtPublicFiles.TheRooms.offlineHidRoom ∧
          kF ≤ AtPublicFiles.TheRooms.offlineFallRoom) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c := by
  obtain ⟨A, made⟩ := ProofFile.Honest.K1.baseMaker_returns Z scope live
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker Z scope live made
  obtain ⟨O⟩ := object A made h
  exact complete_from_the_object live hr made h O off

/-- CONDITIONAL. **At the stored full-size files.** -/
theorem complete_from_the_object_stored (hZ : Z = VerifierAndGoals.storedPublicFiles) (hr : readFiles Z = .ok pp)
    (object : ∀ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A →
      ∀ h : HeadAtReturn Z A, Nonempty (TheOneObject h hr))
    (off : ∀ description : OfflineDescription, offlineDescription Z = .ok description →
      ∃ (FT : AtPublicFiles.KeyBridge.FallT (offlineAt (thePartsAt Z) description))
        (Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)) (kB kH kF : ℝ≥0∞),
        OfflineDebts Z (keyFileDescription description.source description.numbers description.later)
          (thePartsAt Z).book ((thePartsAt Z).prover description) runValueBytes runValueBytes
          (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF ∧
        kB ≤ AtPublicFiles.TheRooms.offlineBadRoom ∧ kH ≤ AtPublicFiles.TheRooms.offlineHidRoom ∧
          kF ≤ AtPublicFiles.TheRooms.offlineFallRoom) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c :=
  complete_from_the_object_at_every_return (scope_named (Or.inl hZ)) (live_named (Or.inl hZ)) hr
    object off

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.baseBad_empty
#print axioms AtPublicFiles.AtFiles.HonestTerm.bad_at_the_online_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.online_debts_from_the_object
#print axioms AtPublicFiles.AtFiles.HonestTerm.complete_from_the_object
#print axioms AtPublicFiles.AtFiles.HonestTerm.complete_from_the_object_at_every_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.complete_from_the_object_stored
