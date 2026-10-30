-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRowsJoin.lean: THE JOIN: these sixteen rows and this book give T3's offline clause:
OwedRest (E2E/OfflineClauses.lean) at the laid simulators and the laid letters, from the ten other
rows' named premises; and so T3's three offline lines from these premises alone.

  owedRest_of_rows          OwedRest d (laidSimulators …) (laidConditions …) H from TenRowsOwed at the
                            relation KeyRel files.
  offline_clauses_of_rows   T3's three offline lines at the offline prover's own value, under the
                            premises of offline_clauses, with TenRowsOwed in OwedRest's place.

CONDITIONAL: TenRowsOwed is a premise: twenty-one named propositions: ten rows' good, ten rows' owed,
and runs whole (the rows that are not paid here: the test on the ranges; the shared chain's eight; the
last chain's one). It is a premise here: tenRowsOwed_of_four (E2E/OfflineFourRowsLeft.lean) gives a member from FourRowsOwed. So this file proves no zero knowledge of
any protocol: it says what is left to prove, row by row. The limits of the six rows' files stand:
their «exact» is the spender's half, with «fresh» at the owners under the kernel's lines on the book.
-/
import E2E.OfflineRowsGathered
import E2E.OfflineClauses
import E2E.KeyOfflineSides
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open LPFD.Full (XF)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)

variable {files : PublicFiles} (d : OfflineDescription) (T : TheirSimulators)
  (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit)

/-- **OwedRest FROM THE TEN ROWS.** -/
theorem owedRest_of_rows (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)
    (ten : TenRowsOwed (files := files) d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) (KeyRel files) H) :
    OwedRest d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) H where
  good := goodWhole_of_rows d T t (KeyRel files) H hs scope ten
  runs := ten.runs
  owed := owedWhole_of_rows d T t (KeyRel files) H hs scope ten

/-- **T3's THREE OFFLINE LINES FROM THE TEN ROWS.** -/
theorem offline_clauses_of_rows (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (x₀ : XF)
    (ten : TenRowsOwed (files := files) d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) (KeyRel files)
      ((partsOfDescription (files := files) d).prover d)) :
    (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d)).ext
        (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
        (offlineSimulatorAt d (partsOfDescription (files := files) d)
          (offlineRowsAt (files := files) d offlineProverCoinCounts
            (laidSimulators (senderValue (files := files) d) T)
            (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t))) ∧
      PrivateStopsAtMost (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 :=
  offline_clauses d _ _ live scope hd hs x₀ (owedRest_of_rows d T t hs scope _ ten)

/-- **THE SAME AT THE NAMED VALUE**: where the public files' test says yes, in scope and read: there is the files'
description d, thePartsAt files is partsOfDescription d, no offline side is missing there (the guard
OfflineSidesAreWhole, paid by offlineSides_whole, E2E/KeyOfflineSides.lean), and at every ten lists of simulators and every
ten letters the ten rows' premises give T3's three offline lines. -/
theorem offline_clauses_of_rows_at_files (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      thePartsAt files = partsOfDescription d ∧ OfflineSidesAreWhole (thePartsAt files) ∧
      ∀ (T : TheirSimulators)
        (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit
          Unit),
        TenRowsOwed (files := files) d (laidSimulators (senderValue (files := files) d) T)
          (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) (KeyRel files)
          ((partsOfDescription (files := files) d).prover d) →
        (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver
            (partsOfDescription (files := files) d)).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
          ExactOutsideStops
            (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline.cleared
            (offlineSimulatorAt d (partsOfDescription (files := files) d)
              (offlineRowsAt (files := files) d offlineProverCoinCounts
                (laidSimulators (senderValue (files := files) d) T)
                (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t))) ∧
          PrivateStopsAtMost
            (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named files live
  obtain ⟨-, x₀, -, -⟩ := VerifiableInference.Compilation.someRequestIsServed_holds files scope hr
  exact ⟨d, hd, thePartsAt_ok hd, offlineSides_whole scope live,
    fun T t ten => offline_clauses_of_rows d T t live scope hd hs x₀ ten⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_rows_at_files
#print axioms AtPublicFiles.OfflineRows.owedRest_of_rows
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_rows
