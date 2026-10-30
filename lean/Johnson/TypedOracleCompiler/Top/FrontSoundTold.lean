-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/FrontSoundTold.lean: soundness in this library's own sense (`Sound`,
VerifiableInference/Statements.lean: the extractor reads the commitment and the committer's log
alone), under named hypotheses, at an input whose typed key holds a part of the value of the public
reading (a computation that queries the hash function), of a verifier that parses the files, builds
the instance and the key's code, compares the commitment ID once, and then runs three checks; it has
no other test (`frontOf`, Johnson/Top/FrontOnlyLaws.lean; `PortArmsC.only_yes_iff`,
Johnson/Top/FrontOnly.lean). The parser and the three checks are parameters.

What this file states. `frontOf_sound_told`, the main statement: at such an input (`ArmFam.told`,
Johnson/Top/ArmsTwoSpellings.lean), `EntryPaid b'` and the hypotheses `FrontOfFieldsTold R b' part
wordC ε nK nE nP` give `Sound` of the system whose verifier is `frontOf prove R (nK + (nE + nP))`,
at the error ε (t + (nK + (nE + nP))) + 0. `front_sound_D_left`: at every input, `EntryPaid b'` and
`FrontFieldsDLeft p b' part wordC ε` (`FrontFieldsD` without `EntryPaid b'`) give `Sound
(systemPortC p)` at the error ε (t + p.n) + p.δ t. `front_sound_told`: at an input of the form
above, for every front verifier p, `EntryPaid b'` and `FrontFieldsTold p b' part wordC ε` give
`Sound (systemPortC p)` at the same error. Against the form in FrontPlainOfD.lean (`FrontFieldsD`:
`parts`, `arms`, `word`, `tests`, `code`, `meaning`, `error`): `tests` is exchanged for the new
field `reads`, from which it follows because at such an input each check tests the key's public part
by its own text (`armsTestC_told`, ArmsToldTests.lean); and, at `frontOf`, `parts`, and with it the
exception, follows from the parser's three counts of queries (`frontParts_frontOf`). Nothing new is
proved: each proof is an application of theorems of the files named.

Under which hypotheses. `EntryPaid b'` (Johnson/Top/FrontPaid.lean): the entry file's check's bound
over a drawn function; the public reading's budget, which serves all three checks (the field
`reading`: it tosses no coin and keeps that budget); the entry file's check tosses no coin. The
fields of `FrontFieldsTold p b' part wordC ε`: `parts` (in `FrontOfFieldsTold R b' part wordC ε nK
nE nP`: the parser's three counts in the place of `parts`); `arms` (`ArmsLeft b'`: the key file's
and the proof file's checks' bounds; neither tosses a coin); `reads` (the bounds' reading gives the
family's part); `word` ((W): the word under a root hangs on what the reading gives through its part
in the key alone); `code` (no two keys have one code); `meaning`; `error`.

What it does not show.
- IT HAS THE SHAPE OF AN UNCONDITIONAL STATEMENT, NOT ITS STRENGTH: its weight is in the named
  fields, and most of them are open.
- FOR ARBITRARY PARAMETERS: NOTHING HERE CAN BE RUN.
- EVERY FIELD IS A HYPOTHESIS, and so is `EntryPaid b'`; a conditional theorem holds vacuously where
  one is false: it claims nothing there. None is proved here.
- F, the two codes, c₀, p or R, b', part, wordC, ε and the counts are parameters: no family of
  checks, parser, code, reading, word or number is given.
- NO FIELD ASKS THAT THE FRONT VERIFIER EVER SAYS YES: at checks that never say yes, or a parser
  that returns what the checks refuse, all fields can hold and `Sound` holds vacuously, claiming
  nothing there: the test is a run at a stored example, and none has been made.
- The parser's three counts are added to the adversary's bound on queries: the error is read at t +
  (nK + (nE + nP)).
- R's READINGS ARE INTENDED TO ASK THE HASH FUNCTION WHEREVER THE FORMAT HASHES. A converter that
  computes the format's hash as a fixed function is an R by its type too, and of it the theorem says
  nothing at that function. That a converter that runs is, at the programs' hash function, the value
  of an asking R is an equation that is owed, for each file; it is not here.
- `word` requires much where the checks' coding is made of more answers of the hash function than
  the key holds.
- `code` requires that the key's code spells all of the key, the record's seed too.
- `meaning` can be false.
- The checks' bounds hold the soundness of the three protocols.
- That the checks are a compiler's output, that the parser reads the programs' files, and that any
  program runs this front verifier is not said.
- The input, and with it all that is made of the public files, is fixed before the hash function is
  drawn: public files are no part of the experiment.
- One way. Soundness alone.
- All limits of the heads of the files named stand.
- For proofs only; no program imports this file.


-/
import Johnson.Top.FrontPaid
import Johnson.Top.FrontOnlyLaws
import Johnson.TypedOracleCompiler.Top.FrontPlainOfD
import Johnson.TypedOracleCompiler.Top.ArmsToldTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Any
variable {r : InputArmsC}

/-- `FrontFieldsD` (FrontPlainOfD.lean) without `EntryPaid b'` (Johnson/Top/FrontPaid.lean). -/
structure FrontFieldsDLeft (p : PortArmsC r) (b' : BesideArmsCD r) (part : b'.D → r.C)
    (wordC : r.C → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol) (ε : ℕ → ℝ≥0∞) :
    Prop where
  /-- the four parts, the request, the parser's budget, the bound on the exception's probability -/
  parts : FrontParts p
  /-- the key file's and the proof file's checks -/
  arms : ArmsLeft b'
  /-- the word under a root hangs on what the reading gives through its part in the key alone -/
  word : WordReadsPart b' part wordC
  /-- each check tests the key's c against what the reading gives -/
  tests : ArmsTestC b' part
  /-- the commitment: no two keys have one code -/
  code : ZKCP.CodeIsOneToOne r.enc
  /-- the meaning: what is true of the extracted index is "the output tokens are the model's" -/
  meaning : HoleArmsCD.soundFor b' (systemArmsC r).IsModelOutput
  /-- the error's name -/
  error : ∀ tC tP, b'.εK tC tP + (b'.εE tC tP + b'.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)

variable {p : PortArmsC r} {b' : BesideArmsCD r} {part : b'.D → r.C}
  {wordC : r.C → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol} {ε : ℕ → ℝ≥0∞}

/-- Under named hypotheses (`EntryPaid b'` and the fields of `FrontFieldsDLeft`): this library's own
`Sound` (VerifiableInference/Statements.lean) for the system whose verifier is the front verifier p.
-/
theorem front_sound_D_left (e : EntryPaid b') (h : FrontFieldsDLeft p b' part wordC ε) :
    Sound (systemPortC p) fun t => ε (t + p.n) + p.δ t :=
  front_sound_D
    ⟨h.parts, coreArmsCD_of e h.arms, h.word, h.tests, h.code, h.meaning, h.error⟩

end Any

section Told
variable {F : ArmFam} {encT : Dig 256 × KeyRoot 256 F.L → Option ZKCP.Str} {c₀ : Dig 256}

/-- What is left at a told input, for a front verifier p, beside `EntryPaid b'`. -/
structure FrontFieldsTold (p : PortArmsC (F.told encT c₀)) (b' : BesideArmsCD (F.told encT c₀))
    (part : b'.D → Dig 256)
    (wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol) (ε : ℕ → ℝ≥0∞) :
    Prop where
  /-- the four parts, the request, the parser's budget, the bound on the exception's probability -/
  parts : FrontParts p
  /-- the key file's and the proof file's checks -/
  arms : ArmsLeft b'
  /-- the part of what the bounds' reading gives is the family's part of what its reading gives -/
  reads : ∀ k (f : Fam (rom 256)), part ((b'.rd k).det f) = F.part (F.Pub.det f)
  /-- the word under a root hangs on what the reading gives through its part in the key alone -/
  word : WordReadsPart b' part wordC
  /-- the commitment: no two keys have one code -/
  code : ZKCP.CodeIsOneToOne encT
  /-- the meaning: what is true of the extracted index is "the output tokens are the model's" -/
  meaning : HoleArmsCD.soundFor b' (systemArmsC (F.told encT c₀)).IsModelOutput
  /-- the error's name -/
  error : ∀ tC tP, b'.εK tC tP + (b'.εE tC tP + b'.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)

variable {p : PortArmsC (F.told encT c₀)} {b' : BesideArmsCD (F.told encT c₀)}
  {part : b'.D → Dig 256}
  {wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol} {ε : ℕ → ℝ≥0∞}

/-- The same at a told input, under named hypotheses (`EntryPaid b'` and the fields of
`FrontFieldsTold`): there the checks' test of the key's public part stands in their text and is no
hypothesis. -/
theorem front_sound_told (e : EntryPaid b') (h : FrontFieldsTold p b' part wordC ε) :
    Sound (systemPortC p) fun t => ε (t + p.n) + p.δ t :=
  front_sound_D_left e
    ⟨h.parts, h.arms, h.word, armsTestC_told encT c₀ b' part h.reads, h.code, h.meaning, h.error⟩

variable {Files : Type}

/-- What is left at a told input, at the front verifier "a parser, the commitment ID's one test,
then the three checks", beside `EntryPaid b'`. -/
structure FrontOfFieldsTold (R : ParseParts (F.told encT c₀) Files)
    (b' : BesideArmsCD (F.told encT c₀)) (part : b'.D → Dig 256)
    (wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol) (ε : ℕ → ℝ≥0∞)
    (nK nE nP : ℕ) : Prop where
  /-- the key file's reading asks at most nK queries, at all files -/
  countK : ∀ prompt output Fl, (R.key prompt output Fl).QueryBound nK
  /-- the entry file's reading asks at most nE queries, at all files -/
  countE : ∀ prompt output Fl, (R.ent prompt output Fl).QueryBound nE
  /-- the proof file's reading asks at most nP queries, at all files -/
  countP : ∀ prompt output Fl, (R.prf prompt output Fl).QueryBound nP
  /-- the key file's and the proof file's checks -/
  arms : ArmsLeft b'
  /-- the part of what the bounds' reading gives is the family's part of what its reading gives -/
  reads : ∀ k (f : Fam (rom 256)), part ((b'.rd k).det f) = F.part (F.Pub.det f)
  /-- the word under a root hangs on what the reading gives through its part in the key alone -/
  word : WordReadsPart b' part wordC
  /-- the commitment: no two keys have one code -/
  code : ZKCP.CodeIsOneToOne encT
  /-- the meaning: what is true of the extracted index is "the output tokens are the model's" -/
  meaning : HoleArmsCD.soundFor b' (systemArmsC (F.told encT c₀)).IsModelOutput
  /-- the error's name -/
  error : ∀ tC tP, b'.εK tC tP + (b'.εE tC tP + b'.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)

variable {R : ParseParts (F.told encT c₀) Files} {nK nE nP : ℕ}

/-- **`front_sound`'s form in this library's own `Sound`, under named hypotheses** (`EntryPaid b'`
and the fields of `FrontOfFieldsTold`): soundness of the system whose verifier is "a parser, the
commitment ID's one test, then the three checks" (`frontOf`), at a told input. No hypothesis ties
that verifier to the three checks, and there is no exception: it is made of them. -/
theorem frontOf_sound_told
    (prove : (systemArmsC (F.told encT c₀)).Weights →
      (systemArmsC (F.told encT c₀)).CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm Files)
    (e : EntryPaid b') (h : FrontOfFieldsTold R b' part wordC ε nK nE nP) :
    Sound (systemPortC (frontOf prove R (nK + (nE + nP)))) fun t =>
      ε (t + (nK + (nE + nP))) + 0 :=
  front_sound_told e
    ⟨frontParts_frontOf prove R h.countK h.countE h.countP, h.arms, h.reads, h.word, h.code,
      h.meaning, h.error⟩

end Told

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.front_sound_D_left
#print axioms VerifiableInference.OnPublicFiles.front_sound_told
#print axioms VerifiableInference.OnPublicFiles.frontOf_sound_told
