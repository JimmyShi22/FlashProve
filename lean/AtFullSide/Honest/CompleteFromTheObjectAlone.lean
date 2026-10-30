-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CompleteFromTheObjectAlone.lean

This file proves the premise on the offline prover that complete_from_the_object
(TheCapstoneFromTheObject.lean of this folder) asks for, and restates that theorem without it. The
header of CompleteAtTheFiles.lean explains the terms.

Main statements.
  * off_at_the_files. Premises: InScope Z = true, protocolDataWellFormed (asDescriptionFiles Z) = true and readFiles Z = .ok
    pp. Conclusion: for every offline description of Z there are FT, Tied, TiedM and three numbers
    within the bounds of E2E/TheRooms.lean such that OfflineDebts (E2E/CompleteAsIOPOffline.lean)
    holds for the offline prover at thePartsAt Z. The proof chooses the empty family of
    default-branch events and the numbers 0, 0 and 0, but the statement does not expose that choice.
    The statement has exactly the form of the premise off of complete_from_the_object.
  * complete_from_a_value_of_the_object. Premises: protocolDataWellFormed (asDescriptionFiles Z) = true; readFiles Z = .ok pp;
    the base construction returns A (made); h : HeadAtReturn Z A; and a value O of TheOneObject h
    hr, the structure in TheOneObject.lean that collects the facts on the online prover that the
    proof of completeness uses. It also assumes the two instances Inhabited P5J.TS and Inhabited
    Desc.K14.St, as TheOneObject.lean does; under h both types have a member (the_two_states_exist,
    TheTwoStatesExist.lean). Conclusion: CompleteAtFiles Z (thePartsAt Z) hr, together with errors a
    and c such that a + 0 + c ≤ completenessTarget and CompleteAtEveryCoin holds with offline error
    a, link error 0 and online error c.

Limits.
  * complete_from_a_value_of_the_object is an implication, not completeness. No value of
    TheOneObject is built here: each of its fields is a hypothesis, and most of them are themselves
    implications whose premise is the invariant of one of the description's chains. Nothing in this
    file shows that such an invariant holds at a run.
  * The statements are at the level of the interactive oracle proof: before any hashing or
    compilation. They say nothing about the C++ programs.
  * off_at_the_files is worth what the files beneath E2E/LotKeyAcceptsAtTheFiles.lean are worth, and
    no more.
  * The conclusion is about served requests alone. What the relation ServedRequest excludes is not
    examined here.
  * They hold for the full-size layout and for the format's second hash function, OnBytes.secondHashFunction,
    alone.
  * The proofs in this file only combine theorems of other files.
  * Nothing on soundness or hiding.

Built on.
  * complete_from_the_object (TheCapstoneFromTheObject.lean of this folder).
  * offlineDebts_at_the_files (E2E/LotKeyAcceptsAtTheFiles.lean).
  * fullPub_some (E2E/KeyK1/KeyK1AtTerm.lean), which shows that fullPub returns a value.
-/
import AtFullSide.Honest.TheCapstoneFromTheObject
import E2E.LotKeyAcceptsAtTheFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- The default instance Inst.Model.Scl.ref is removed, so that every statement that uses a table of
scales names that table explicitly. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.Honest
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes.Slice (frS)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells onlineProverFromPublicFiles)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixFilling)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin)
open VerifiableInference.Compilation (theProvers)

local instance (priority := high) nonemptyPadZ_objectAlone : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_objectAlone : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_objectAlone : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {pp : Inst.Model.ScalesAndPolicy}

/-- The properties of the offline prover, within their three bounds, in exactly the form of the
premise off of complete_from_the_object. -/
theorem off_at_the_files (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hr : readFiles Z = .ok pp) :
    ∀ description : OfflineDescription, offlineDescription Z = .ok description →
      ∃ (FT : AtPublicFiles.KeyBridge.FallT (offlineAt (thePartsAt Z) description))
        (Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)) (kB kH kF : ℝ≥0∞),
        OfflineDebts Z (keyFileDescription description.source description.numbers description.later)
          (thePartsAt Z).book ((thePartsAt Z).prover description) runValueBytes runValueBytes
          (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF ∧
        kB ≤ AtPublicFiles.TheRooms.offlineBadRoom ∧ kH ≤ AtPublicFiles.TheRooms.offlineHidRoom ∧
          kF ≤ AtPublicFiles.TheRooms.offlineFallRoom := by
  intro description described
  obtain ⟨K₀, keyPublic⟩ := AtPublicFiles.KeyK1.fullPub_some
  obtain ⟨Tied, TiedM, debts⟩ :=
    TheKeyLetters.offlineDebts_at_the_files hr described scope live keyPublic
  exact ⟨fun _ _ _ => ∅, Tied, TiedM, 0, 0, 0, debts, zero_le _, zero_le _, zero_le _⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- Conditional on a value of TheOneObject. The conclusion of complete_from_the_object, with no
premise on the offline prover. -/
theorem complete_from_a_value_of_the_object (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (h : HeadAtReturn Z A)
    (O : TheOneObject h hr) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c :=
  complete_from_the_object live hr made h O (off_at_the_files h.head.scope live hr)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.off_at_the_files
#print axioms AtFullSide.Honest.complete_from_a_value_of_the_object
