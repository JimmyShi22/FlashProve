-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CompleteFromTheUnion.lean

This file proves one conditional step towards complete_in_scope (CompleteAtTheFiles.lean of this
folder): the conclusion of that theorem, from a premise on the offline prover. The header of
CompleteAtTheFiles.lean explains the terms.

Main statement.
  * complete_from_the_union. Premises: protocolDataWellFormed (asDescriptionFiles Z) = true; readFiles Z = .ok pp; the base
    construction returns A (made); h : HeadAtReturn Z A; and off. The premise off says that for
    every offline description of Z there are a family FT of events at which the prover uses a
    default branch, two relations Tied and TiedM, and three numbers kB, kH and kF such that
    OfflineDebts holds for the offline prover at thePartsAt Z, with each number at most its bound in
    E2E/TheRooms.lean (each bound is 2^(-100)). OfflineDebts (E2E/CompleteAsIOPOffline.lean) lists
    the properties of the offline prover from which its share of completeness follows: the verifier
    accepts outside the abort set and outside FT, and the probabilities of these events are bounded
    by the three numbers. Conclusion: CompleteAtFiles Z (thePartsAt Z) hr, together with errors a
    and c such that a + 0 + c ≤ completenessTarget and CompleteAtEveryCoin holds with offline error
    a, link error 0 and online error c.
  * The proof calls complete_from_the_object at theOneObjectValue, a value of the structure
    TheOneObject, so no value of that structure is a premise here. In that value the auxiliary
    parameter open₂ is set to zeros (open₂_filled, OpenSharedFilled.lean); the conclusion does not
    mention it, and this file does not show that another choice would serve as well. The two
    Inhabited instances that TheOneObject.lean assumes are not premises either: under h both types
    have a member (the_two_states_exist), and the conclusion mentions neither type.

Limits.
  * This is an implication, not completeness: off is a premise, and it is not proved in this file.
  * The statement is at the level of the interactive oracle proof: before any hashing or
    compilation. It says nothing about the C++ programs.
  * Every limit of the two files called, TheCapstoneFromTheObject.lean and TheOneObjectValue.lean,
    and of each file that proves a field of theOneObjectValue, holds here too. Some hundreds of
    closed facts beneath are checked by evaluation in Lean's kernel, and no independent checker has
    replayed them.
  * The return of the base construction (made) and h are premises. That they can be met is shown in
    TheCapstoneFromTheObject.lean (complete_from_the_object_at_every_return), not here.
  * The conclusion is about served requests alone. What the relation ServedRequest excludes is not
    examined here.
  * It holds for the full-size layout and for the format's second hash function, OnBytes.secondHashFunction,
    alone.
  * Nothing on soundness or hiding.

Built on.
  * complete_from_the_object (TheCapstoneFromTheObject.lean), theOneObjectValue
    (TheOneObjectValue.lean) and the_two_states_exist (TheTwoStatesExist.lean), all in this folder.
-/
import AtFullSide.Honest.TheCapstoneFromTheObject
import AtFullSide.Honest.TheTwoStatesExist
import AtFullSide.Honest.TheOneObjectValue

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

local instance (priority := high) nonemptyPadZ_fromTheUnion : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_fromTheUnion : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_fromTheUnion : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {pp : Inst.Model.ScalesAndPolicy}

/-- Conditional on the premise off about the offline prover. Completeness, at the level of the
interactive oracle proof, of the provers at thePartsAt Z, at public files that pass the verifier's
test and have a HeadAtReturn. -/
theorem complete_from_the_union (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (h : HeadAtReturn Z A)
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
  obtain ⟨⟨first⟩, ⟨shared⟩⟩ := the_two_states_exist h
  haveI : Inhabited P5J.TS := ⟨first⟩
  haveI : Inhabited Desc.K14.St := ⟨shared⟩
  exact complete_from_the_object live hr made h (theOneObjectValue made live) off

end AtFullSide.Honest

#print axioms AtFullSide.Honest.complete_from_the_union
