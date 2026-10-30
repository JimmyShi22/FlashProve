-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotStandLaid.lean: THE FIRST CHAIN STANDS, WITH NO PREMISE ON ANY MEMBER AND NO «ready returns»: at the offline prover's own senders, the written book, the laid thread
and letter (laidFirst, laidSaid, E2E/LotJoinLaid.lean): at every input that meets the committer's relation at the range, at all coins of the run, at EVERY border from 0
to 19 and at EVERY list of challenges that fits the rounds in front of it, there is a state at which the pair stands; the run has heard that list, at the run's own
input.

  `acceptedS_none`: acceptance at a fall that never speaks is acceptance at the fall "none". General.
  `fiveLaid`: the five debts at every member of the first chain, at the laid thread and letter, at no fall.
  `noStop_laid`: no part of the offline prover's first chain ever stops.
  **`standLaid`**: the statement.
  **`standLaid_guarded`**: with its guard in one breath: at every border some list fits (some_list_fits, E2E/LotStandFirst.lean).

By what. standFirst_of_five (E2E/LotStandFirst.lean) · firstLaid (E2E/LotJoinLaid.lean) · «ready returns»: lotReadyReturnsWhole (E2E/LotReadyWhole.lean) · the range:
rel_passes (E2E/LotLaterValue.lean), rangeTie_atValue (E2E/LotEntersFirstTie.lean) · no stop: noStopAll_keyProver (E2E/KeyNoStop.lean). Calls.

WHY IT MATTERS. Every debt of the first chain has "the pair stands in front" as its premise: until a stand is shown each can be met emptily. Here the stands are shown.

Limits. A stand is a sentence "there is": it names no state, and nothing here says that the frame's own run passes through it (one state for each run: OneState, another
file's). The premises: the test on the public files says yes; offlineDescription returns d; in scope; fullPub = some K₀; the relation at the input. At no fall: so the
honest first chain is accepted at EVERY fitting list: that sentence is as strong as the lots beneath it are right.
pinT and "unmarked" are idle at this thread. Nothing on the shared or the last chain. No measure. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinLaid
import E2E.LotStandFirst
import E2E.LotEntersFirstAtTerm
import E2E.LotReadyWhole
import E2E.KeyNoStop
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Stops (NoStop)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest

/-- Acceptance at a fall that never speaks is acceptance at the fall "none". -/
theorem acceptedS_none {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb}
    {Said : Nat → Coins Bk → Mid W X → Prop} {fall : Nat → S → List Fmt.Drawn → Option String}
    (hf : ∀ b s ds, fall b s ds = none) {b : Nat} (h : AcceptedS T Said fall b) :
    AcceptedS T Said (fun _ _ _ => none) b :=
  fun blk hblk k s m E ds y cols hA hd hst _ hM => h blk hblk k s m E ds y cols hA hd hst (hf b s ds) hM

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- The five debts at every member, at the laid thread and letter, at no fall. -/
theorem fiveLaid (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK : fullPub = some K₀)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :
    ∀ b, b < 19 → FiveAt (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) (fun _ _ _ => none) b := by
  obtain ⟨o, -, y⟩ := firstLaid hd scope live hK w x
  have hlen : (laidFirst Z d K₀ w x).bs.length = 19 :=
    (AtPublicFiles.KeyThread.lengths scope (sourced_of_description hd live).named).1
  intro b hb
  have ob := o b (hlen ▸ hb)
  exact ⟨ob.1, ob.2.1, ob.2.2.1, ob.2.2.2, acceptedS_none (noFall _) (y b (hlen ▸ hb))⟩

/-- No part of the offline prover's first chain ever stops. -/
theorem noStop_laid : NoStop (keyProver (offlineValue (files := Z) d)).first :=
  (AtPublicFiles.KeyFile.noStopAll_keyProver (offlineValue (files := Z) d) (AtPublicFiles.KeyValueHolds.quietHalf_test _)
    (AtPublicFiles.KeyValueHolds.quietHalf_test _)
    (AtPublicFiles.KeyValueHolds.quietHalf_needs (AtPublicFiles.KeyValueHolds.quietHalf_test _))
    (AtPublicFiles.KeyValueHolds.quietHalf_needs (AtPublicFiles.KeyValueHolds.quietHalf_test _))).1

/-- **THE FIRST CHAIN STANDS AT EVERY BORDER, AT EVERY LIST THAT FITS.** -/
theorem standLaid (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK : fullPub = some K₀)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) (rel : (laterValue Z d K₀).Rel w.1 w.2.1 x)
    (k : Coins (keyBook K₀)) :
    ∀ b, b ≤ 19 → ∀ ds, drawsFit (declsTo (laidFirst Z d K₀ w x).bs b) ds = true →
      ∃ s m E, ThrS (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) b k s m E ∧ m.st.heard = ds ∧
        m.st.input = inFirst w.1 w.2.1 x := by
  have hs := sourced_of_description hd live
  obtain ⟨R, hR⟩ := AtPublicFiles.OfflineRows.Lots.lotReadyReturnsWhole live hd scope hK w.1 w.2.1 x k
    (rel_passes rel)
  exact standFirst_of_five hs scope
    (rangeTie_atValue hs scope _ (offlineValue_inRange d) w.1) rel noStop_laid (Nat.le_refl 19)
    (fiveLaid hd scope live hK w x) k R hR

/-- **The same with its guard in one breath**: at every border some list fits, and at every list that fits the pair stands. -/
theorem standLaid_guarded (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK : fullPub = some K₀)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) (rel : (laterValue Z d K₀).Rel w.1 w.2.1 x)
    (k : Coins (keyBook K₀)) :
    ∀ b, b ≤ 19 → (∃ ds, drawsFit (declsTo (laidFirst Z d K₀ w x).bs b) ds = true) ∧
      ∀ ds, drawsFit (declsTo (laidFirst Z d K₀ w x).bs b) ds = true →
        ∃ s m E, ThrS (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) b k s m E ∧ m.st.heard = ds ∧
          m.st.input = inFirst w.1 w.2.1 x :=
  fun b hb => ⟨some_list_fits (sourced_of_description hd live) b,
    standLaid hd scope live hK w x rel k b hb⟩

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.standLaid_guarded
#print axioms AtPublicFiles.FirstH.Lots.acceptedS_none
#print axioms AtPublicFiles.FirstH.Lots.fiveLaid
#print axioms AtPublicFiles.FirstH.Lots.noStop_laid
#print axioms AtPublicFiles.FirstH.Lots.standLaid
