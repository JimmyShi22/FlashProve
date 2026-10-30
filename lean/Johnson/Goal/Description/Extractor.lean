-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Extractor.lean: the extractor. One named part of `VerifierAndGoals.theDescription`
(Description.lean), in a file of its own.
State: the true one. `starAt₀`: the family at `flashProveDataNoExtractor` (Lay0.lean). `theExtractor`: the told
record's extractor over that family (`LayoutsByPublicReading.extractor`, Johnson/Top/InnerCompiledVerifierByPublicReading.lean, at
`DescriptionDataAtFiles.layoutsByPublicReading`), then `phiO` at valid settings: an index's weights where the matrix holds an index;
none else. `starAt₀At o`, `theExtractorAt o`: the same two texts at `flashProveDataNoExtractorAtHash o`, the told record
taken at the parameter bytes `VerifierAndGoals.par7O o` (`DescriptionDataAtFiles.layoutsByPublicReadingWithParameterBytes`, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean: the
extractor does not read them); that they are one at the format's second hash function is
`theLayAt_older` (Lay.lean), by `rfl`. No circle: the told
record reads no extractor (`DescriptionDataAtFiles.layoutsByPublicReading_ignoresExtractor`, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFilesIgnoreExtractor.lean).
Limit. It says nothing of what the extractor finds.

-/
import Johnson.Goal.Description.Lay0
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFilesIgnoreExtractor
import Johnson.PV.DescribeO
import Johnson.Goal.Reads.ReadAtSecondHashFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- flashProveDataNoExtractor's family at one set of public files: dataAtFiles flashProveDataNoExtractor Z is this at asDescriptionFiles Z, by rfl. -/
def starAt₀ (Zk : OnBytes.K.Pub) : DescriptionDataAtFiles Zk :=
  dataAtFilesFromRounds flashProveDataNoExtractor Zk (flashProveDataNoExtractor.filesParametersOrDefault Zk) (flashProveDataNoExtractor.keyRoundsOrEmpty Zk) (flashProveDataNoExtractor.proofRoundsOrEmpty Zk) (flashProveDataNoExtractor.fit_of Zk)

def theExtractor (Zk : OnBytes.K.Pub) (s : IntegerTransformer.Settings) : Commitment → QueryLog →
    Option (ModelWeights s) :=
  fun commitment queryLog =>
    (((starAt₀ Zk).layoutsByPublicReading (fun _ => false) []).extractor commitment queryLog).bind fun M =>
      if hv : settingsAreValid s = true then phiO hv M else none

/-- The same family at a function o in the second hash function's place. -/
def starAt₀At (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : DescriptionDataAtFiles Zk :=
  dataAtFilesFromRounds (flashProveDataNoExtractorAtHash o) Zk ((flashProveDataNoExtractorAtHash o).filesParametersOrDefault Zk) ((flashProveDataNoExtractorAtHash o).keyRoundsOrEmpty Zk) ((flashProveDataNoExtractorAtHash o).proofRoundsOrEmpty Zk)
    ((flashProveDataNoExtractorAtHash o).fit_of Zk)

def theExtractorAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (s : IntegerTransformer.Settings) :
    Commitment → QueryLog → Option (ModelWeights s) :=
  fun commitment queryLog =>
    (((starAt₀At o Zk).layoutsByPublicReadingWithParameterBytes (fun _ => false) []
      (VerifierAndGoals.par7O o OnBytes.Tie.recordGround Zk.pol Zk.KL Zk.lay)).extractor commitment
        queryLog).bind fun M =>
      if hv : settingsAreValid s = true then phiO hv M else none

end FlashProve
