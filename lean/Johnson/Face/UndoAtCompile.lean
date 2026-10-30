-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/UndoAtCompile.lean: at FlashProve's names: the byte format's parser undoes the writer
on what compile's committer and prover make, outside the coins at which one of the six run values
is 32 zero bytes.

Main names (namespace VerifiableInference.Compilation).
  undoOn_compile   UndoOnBut (Johnson/Face/UndoOfFits.lean) at flashProveDescription, the family layoutsOfBuiltDescription, the honest
    side honestSide at each reading, the index of the weights, the parser flashProveDescription.parse and the writer
    bytesWriter. Premises, sorted.
      PUBLIC, paid here: PublicS, the numbers, the coding, the widths, the salt's length: from scope
        and the test on the files.
      THE COMPILER'S OWN HONEST SETTINGS: SideBytes at each reading.
      THE IOP PROVER'S: StratsPrint at each reading.
    THE MODEL'S TIE: none: the relation Tr is free.

Not shown here: that a premise is met.
-/
import Johnson.Face.BytesOfSide
import Johnson.Face.FinalStatement
import Johnson.Goal.Meaning.PublicSAt
import Johnson.Goal.Meaning.WordsFitAtThe
import Johnson.Prover.At.DrawHome

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve VerifiableInference.OnPublicFiles OnBytes.FrontRoad OnBytes.WholeKey
open TypedOracleCompiler.Compile.Batch.Cms
open Johnson.Face
open IntegerTransformer (Settings)

/-- compile's honest side at a reading. -/
abbrev sideAt (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings)
    (d : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) :=
  (honestSide ((flashProveWiring files settings honest.fallbackInstance).layoutAtReading d)
    honest.provers (honest.compiledSettings d)).side

set_option maxRecDepth 100000 in
/-- **The writer is formOf on whole typed proofs.** -/
theorem bytesWriter_whole (files : PublicFiles) (q : Johnson.Prover.Print.Typed (dataAtFiles flashProveData files))
    (hq : q.aux = []) :
    bytesWriter files ([], (⟨q.cm, q.rcd⟩,
        ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩)) =
      Johnson.Prover.Print.formOf (dataAtFiles flashProveData files) q := by
  obtain ⟨aux, cm, rcd, copy, piT, cm', rcd', piL, piB⟩ := q
  cases hq
  rfl

set_option maxRecDepth 100000 in
/-- **THE PARSER UNDOES THE WRITER ON WHAT compile's HONEST SIDE MAKES**, outside the exception. -/
theorem undoOn_compile (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (sL : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D → OnBytes.Params.LinBindingShape)
    (runsT : ∀ d, (sideAt files settings honest d).KT → ByteArray × ByteArray)
    (runsB : ∀ d, (sideAt files settings honest d).KB → ByteArray × ByteArray)
    (hB : ∀ d, SideBytes (dataAtFiles flashProveData files) allZeroDigest [] (sideAt files settings honest d)
      (_root_.Run.digToBytes d.1) (sL d) (runsT d) (runsB d))
    (ok : (flashProveDescription.input files allZeroDigest []).Index → Prop) (hok : ∀ i x, Tr i x → ok i)
    (hP : ∀ d, StratsPrint (dataAtFiles flashProveData files) allZeroDigest [] (sideAt files settings honest d)
      (runsT d) (runsB d) ok Tr) :
    UndoOnBut flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (sideAt files settings honest)
      (backThe files settings) Tr (flashProveDescription.parse files) (bytesWriter files)
      (ZeroRun (dataAtFiles flashProveData files) allZeroDigest []) := by
  have say := Meaning.sizesSay_the files scope live
  exact undoOn_of_fitsAt (dataAtFiles flashProveData) flashProveData.f₀ flashProveData.honest allZeroDigest [] files _
    (backThe files settings) Tr (ZeroRun (dataAtFiles flashProveData files) allZeroDigest []) (bytesWriter files)
    (Meaning.publicS_built files live (Meaning.wordsFitAt_the files scope live)).1
    (fitsAtCoins_of_side (dataAtFiles flashProveData) allZeroDigest [] files _ sL runsT runsB hB ok Tr hok hP
      (Meaning.numbersFit_the files) say.salt (Meaning.honestEnc_the files) say.widthsK
      say.widthsP)
    (bytesWriter_whole files)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.bytesWriter_whole
#print axioms VerifiableInference.Compilation.undoOn_compile
