-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HonestAtDescriptionDataAtFiles.lean: TWO OF THE FOUR PREMISES OF THE HONEST PROVER's COUNT
(queryBound_proveForm, Johnson/Prover/Home/CountF.lean), FirstIs AND PassFits, PROVED AT THE TOLD
RECORD OF D* (DescriptionDataAtFiles.layoutsByPublicReading, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean), at the letters S of one set of public
files: at all data; that the public reading asks at most 8 times (hP) and the bound n (hn) stay
premises. Calls:
it adds no strength.

Main names.
  firstBlockTestAtDescriptionData S       the one test: passAt (Johnson/Prover/Law/PassAt.lean) at the bits of work of S's
    three files' rounds (workFrame, Johnson/Prover/Law/FirstBlockAt.lean).
  firstIs_layoutsByPublicReading     FirstIs at the record's coding, at every d.
  passFits_layoutsByPublicReading    PassFits (Johnson/Prover/All/CountF.lean) at the record's wiring and the record's
    wire of the seeds, at every d: NO PREMISE.
  honestProverQueryBound_layoutsByPublicReading  so the honest prover's program over the told record, carried by the first-block
    exit, asks the hash function at most 8 + n times on every path, where n bounds allF at all that
    may be drawn.

Limits. n IS A LETTER: no numeral. The strategies, the caps, the draws and the printer are letters.
Nothing here says that the prover's outcome is accepted.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Home.CountF
import Johnson.Prover.Law.FirstBlockAt
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (KF)
open PV.EntryFive (dsF xsF)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- The one test on first blocks at S's letters. -/
abbrev firstBlockTestAtDescriptionData : Pass 256 (typedOracleCarrier (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol
                           (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
                           (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits) :=
  passAt _ (workFrame frS.P.T.a S.DK dsF S.DP)

/-- The wiring has a block 0. -/
theorem k_pos : 0 < (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.K := Nat.succ_pos (KF S.DK S.DP)

/-- **FirstIs at the record's coding.** -/
theorem firstIs_layoutsByPublicReading (d : (S.layoutsByPublicReading c₀ m₀).D) : FirstIs (k_pos S c₀ m₀) ((S.layoutsByPublicReading c₀ m₀).m d) :=
  firstIs_of _ _ (fun _ => rfl) fun _ _ _ => rfl

/-- **PassFits at the record.** -/
theorem passFits_layoutsByPublicReading (d : (S.layoutsByPublicReading c₀ m₀).D) :
    PassFits (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout ((S.layoutsByPublicReading c₀ m₀).Sd d) (k_pos S c₀ m₀)
      (firstBlockTestAtDescriptionData S c₀ m₀) where
  testsT := by
    exact testsAt_wqWhole (typedOracleCarrier (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits) (workFrame frS.P.T.a S.DK dsF S.DP) Tag.test (ckP .two)
      (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀)
      (join₀ S.G.rec₀) ByteArray.empty silK S.runK id (fun _ => rfl) fun _ => rfl
  testsL := by
    exact testsAt_wqW (typedOracleCarrier (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits) (workFrame frS.P.T.a S.DK dsF S.DP) Tag.link (ckP .two)
      (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) dsF frS.P.T.a xsF S.dec id (fun _ => rfl)
      fun _ => rfl
  testsB := by
    exact testsAt_wqWhole (typedOracleCarrier (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits) (workFrame frS.P.T.a S.DK dsF S.DP) Tag.onl (ckP .two)
      (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2)
      (join₀ S.G.z₀.2) ByteArray.empty silP S.runP id (fun _ => rfl) fun _ => rfl
  seed0 := askedWhole_seedQ0 _ _ _ rfl
  seed1 := askedWhole_seedQ1 _ _ _ rfl

variable {Kap Form : Type} (b₀ : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody)
  (st : Strats (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol Kap) (capT capL capB : ℕ → ℕ)

/-- **The honest prover's program over the told record asks at most 8 + n times.** -/
theorem honestProverQueryBound_layoutsByPublicReading
    (iskOf : (S.layoutsByPublicReading c₀ m₀).D → (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).Index ×
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.EncodingRandomness × (ℕ → Bits))
    (x : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).Instance)
    (drawOf : (S.layoutsByPublicReading c₀ m₀).D → Draw 256 (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits Kap)
    (print : (S.layoutsByPublicReading c₀ m₀).D → Raw 256 (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits → Form)
    (n : ℕ) (hP : (S.layoutsByPublicReading c₀ m₀).Pub.QueryBound 8)
    (hn : ∀ d, allF (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout capT capL capB (drawOf d) ≤ n) :
    (proveForm (S.layoutsByPublicReading c₀ m₀) b₀ st capT capL capB
      (fun d => carryF (S.layoutsByPublicReading c₀ m₀) (fun _ => firstBlockTestAtDescriptionData S c₀ m₀) d) iskOf x drawOf
      print).QueryBound (8 + n) :=
  queryBound_proveForm (S.layoutsByPublicReading c₀ m₀) b₀ st capT capL capB iskOf x drawOf print 8 n hP
    (firstIs_layoutsByPublicReading S c₀ m₀) (passFits_layoutsByPublicReading S c₀ m₀) hn

end FlashProve

#print axioms FlashProve.k_pos
#print axioms FlashProve.firstIs_layoutsByPublicReading
#print axioms FlashProve.passFits_layoutsByPublicReading
#print axioms FlashProve.honestProverQueryBound_layoutsByPublicReading
