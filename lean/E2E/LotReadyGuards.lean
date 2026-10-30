-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyGuards.lean: tests for emptiness, and one control, for the offline part (LotReadyDebts, LotReadyReturns:
«ready returns at the offline prover and the written book»). It proves nothing of them, imports none of their files.

  premises_met     THE FIVE PREMISES OF LotReadyReturns HAVE A MEMBER: at the library's written full-size files VerifierAndGoals.storedPublicFiles the
                   test on the public files says yes, offlineDescription returns, the files are in scope, fullPub returns, and
                   an index is in range. protocolDataWellFormed at storedPublicFiles is the SIDE library's theorem (AtFullSide/Top/LiveAtFull.lean).
  dummy_inRange    the named member of the range is in range
  owed, data_written   in scope, off the five returns alone (Made5, E2E/LotPlanServesGround.lean), WITHOUT protocolDataWellFormed: the
                   description's third test passes, and its rounds' data are the written ones
  live_of_named    KeyNamed GIVES protocolDataWellFormed: where the test says no, the object's data are the dead ones, of depth 0, and the
                   field depth is false. So no law that takes KeyNamed or KeySourced can be spent without protocolDataWellFormed.
  word_of_tests, no_ready_of_word   where a test on the book fails, readyTests and ready refuse
  bent_word, bent_refuses   A CONTROL THAT THE LINE CAN FAIL: at the written book with the index-mask message's sending bent to
                   84 coins (as in full_small_no, full_lends_no) a test on the book fails, at the written rows and either answer
                   of the third test; so ready refuses there, at every prover, index, instance and coin.

Limits. VerifierAndGoals.storedPublicFiles is three terms written in Lean; no theorem ties them to files in a folder. The control bends one row.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotPlanServesMeets
import E2E.KeyBookPassesNamed
import E2E.KeyProtocolOverDescription
import AtFullSide.Top.LiveAtFull
import Johnson.Goal.Files.ScopeExample
import Johnson.Goal.Conditions.LiveAtThe
import Johnson.IMR.KeyOwedFull
import Johnson.HB.LLHARD.KB8.FitsTheLedger
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.LotReadyGuards
open VerifiableInference VerifiableInference.Desc
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.LotPlanGround (Made5 pins plan offlineDescriptionNamed)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull wordAt word_rows fullFirst fullShared fullSecond
  of_atFull full_made)
open AtPublicFiles.AtFiles (KeyNamed FullSizeMatrix)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription)
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)

/-! ## 1 The premises have a member -/

/-- The named member of the range is in range. (The text of dummy_in_range, E2E/OfflineRowsAtFiles.lean.) -/
theorem dummy_inRange : matrixInput.inRange matrixInput.dummy = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf
    (VerifiableInference.OnPublicFiles.Flat.matrixOf fullIn.dummy)).isSome = true
  rw [VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf fullIn.dummy)]
  rfl

/-- **The five premises of LotReadyReturns hold together somewhere.** -/
theorem premises_met : ∃ (Z : PublicFiles) (description : OfflineDescription) (K₀ : KeyPub) (w₀ : FullSizeMatrix),
    protocolDataWellFormed (asDescriptionFiles Z) = true ∧ offlineDescription Z = .ok description ∧ InScope Z = true ∧
      fullPub = some K₀ ∧ matrixInput.inRange w₀ = true := by
  obtain ⟨d, hd, -⟩ := offlineDescriptionNamed VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK⟩ := full_made
  exact ⟨VerifierAndGoals.storedPublicFiles, d, K₀, matrixInput.dummy, AtFullSide.Top.theLive_zFull, hd,
    VerifierAndGoals.inScope_full, hK, dummy_inRange⟩

/-! ## 2 What is had without protocolDataWellFormed, and what cannot be -/

section Scope
variable {Z : PublicFiles} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- In scope, off the returns: the description's third test passes. -/
theorem owed (scope : InScope Z = true) (h : Made5 Z X N P) : (Key.descriptionFromSource X N P).owedOk = true :=
  IM.key_owedOk_of_planOk (pins scope h).1 (pins scope h).2 (plan scope h)

/-- In scope, off the returns: the description's rounds' data are the written ones. -/
theorem data_written (scope : InScope Z = true) (h : Made5 Z X N P) :
    (Key.descriptionFromSource X N P).data "key file" = .ok Johnson.G.writtenKFull := by
  obtain ⟨X₀, m, h0, hm, r1, r2, r3⟩ := h
  have hN : N = Johnson.KB8.rangesNumsFull :=
    Except.ok.inj (r2.symm.trans (Johnson.AtFull.KeyBack.rangesNumbers_in_scope scope h0 hm))
  have hP : P = Johnson.KB8.laterPlacesFull :=
    Except.ok.inj (r3.symm.trans (Johnson.AtFull.KeyBack.laterPlaces_in_scope scope h0 hm))
  have hk := (IM.keyPins_at_made scope h0 hm).2.2.2.1
  exact PlanWritten.data_of_pinnedKey hk (IM.pinned_of_rows hk
    (Johnson.KB8.r8_of_returns scope h0 hm Key.fixedDigest_size r1
      (Johnson.KB8.pinsNP_of_eq hN hP))
    (Johnson.KB8.r8'_of_returns scope h0 hm Key.fixedDigest_size r1 N P))

/-- **KeyNamed gives protocolDataWellFormed.** No other premise. -/
theorem live_of_named (h : KeyNamed Z X N P) : protocolDataWellFormed (asDescriptionFiles Z) = true := by
  by_contra hl
  have e : (dataAtFiles flashProveData Z).DK = FlashProve.emptyRoundsData := by
    show flashProveData.keyRoundsOrEmpty (asDescriptionFiles Z) = _
    unfold FlashProve.DescriptionData.keyRoundsOrEmpty
    exact if_neg hl
  have d : ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a = (dataAtFiles flashProveData Z).DK.a := congrArg (·.a) h.depth
  rw [e] at d
  exact absurd d (by decide)

end Scope

/-! ## 3 A control: the line can fail -/

section Refuses
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {w₀ : W₀}

/-- Where the run's first tests pass, no test on the book fails. -/
theorem word_of_tests (h : readyTests F B H w₀ = .ok ()) : B.word F = none := by
  unfold readyTests at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · assumption

/-- Where a test on the book fails, ready refuses. -/
theorem no_ready_of_word (hw : (B.word F).isSome = true) (rc : Rc) (x : Xi) (c : Coins B)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : ready F B H w₀ rc x c ≠ .ok R := by
  intro h
  rw [word_of_tests (ready_ok h).1] at hw
  cases hw

end Refuses

/-- **At the written rows a test fails at the bent book**, at either answer of the third test. A closed question to Lean's
kernel, twice. -/
theorem bent_word (masks : Bool) : atFull (fun K =>
    (wordAt fullFirst fullShared fullSecond masks
      (keyBook { K with sIdx := [⟨0, 0, 84, 0⟩] })).isSome) = true := by
  cases masks
  · decide +kernel
  · decide +kernel

/-- **So ready refuses at the bent book**, at every description with the written rows. -/
theorem bent_refuses {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi}
    (r1 : rowsOf F.first.blocksInOrder = fullFirst) (r2 : rowsOf F.shared.blocksInOrder = fullShared)
    (r3 : rowsOf F.second.blocksInOrder = fullSecond) {K : KeyPub} (hK : fullPub = some K)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins (keyBook { K with sIdx := [⟨0, 0, 84, 0⟩] })) (R : Ready W₀ Rc Xi Ky Tr X₀ X) :
    ready F (keyBook { K with sIdx := [⟨0, 0, 84, 0⟩] }) H w₀ rc x c ≠ .ok R := by
  refine no_ready_of_word ?_ rc x c R
  rw [word_rows, r1, r2, r3]
  exact of_atFull (bent_word _) hK

end AtPublicFiles.LotReadyGuards

#print axioms AtPublicFiles.LotReadyGuards.dummy_inRange
#print axioms AtPublicFiles.LotReadyGuards.premises_met
#print axioms AtPublicFiles.LotReadyGuards.owed
#print axioms AtPublicFiles.LotReadyGuards.data_written
#print axioms AtPublicFiles.LotReadyGuards.live_of_named
#print axioms AtPublicFiles.LotReadyGuards.word_of_tests
#print axioms AtPublicFiles.LotReadyGuards.no_ready_of_word
#print axioms AtPublicFiles.LotReadyGuards.bent_word
#print axioms AtPublicFiles.LotReadyGuards.bent_refuses
