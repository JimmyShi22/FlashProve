-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/Form.lean: FROM A WHOLE TYPED PROOF (further tokens; the key's root and record;
the copy's number; the key file's, the entry file's and the proof file's proof strings; the copy's
root and record) TO THE FORM THAT THE GOALS' VERIFIER TAKES (FormBytes,
Johnson/Goal/Tie/DescriptionOnBytes.lean): five parsed files as bytes. Definitions only, each with code.

Why. The goals' verifier parses a form; the honest side makes typed proofs.

Main names.
  QT S, QL S, QB S   the three batch protocols at the letters S of one set of public files: the
    types of the three proof strings, written out (piTE, piLE, piBE,
    Johnson/Top/Fire/Code/VerifyVFastD.lean, end in these).
  seedsOf ρ          a typed record's seeds as the seeds' file holds them: spellSeedL
    (OnBytes/K/IdSeedSpell.lean), each element as three words.
  Typed S            the nine parts.
  formOf S q         THE FORM: a pure function of the nine parts: it asks no oracle and does not see
    the configuration's digest.

Limits. DEFINITIONS ONLY. That the goals' parser lays q again of formOf S q:
Johnson/Prover/Print/FormBack.lean (decodeD_formOf). The roots of the two tables are written as the
bytes of the typed digests; the answers as trAns (OnBytes/Flat/LinkSib.lean) of the typed records'
answers. Nothing on soundness or completeness. It names no goal's form.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Tie.DescriptionOnBytes
import Johnson.Prover.Print.Entry
import OnBytes.Prover.Print.Bytes
import OnBytes.K.IdSeedSpell
import OnBytes.Flat.LinkSib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open LPFD.Full (sBG sTG)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover.Print (carrierOf wrFile wrSeeds)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk)

/-- The key file's batch protocol at S. -/
abbrev QT := (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
  ByteArray.empty silK S.runK).batch

/-- The proof file's. -/
abbrev QB := (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
  ByteArray.empty silP S.runP).batch

/-- The entry file's. -/
abbrev QL := (linkSkeletonOfRoundData (ckP .two) dsF frS.P.T.a xsF S.dec).up

/-- A typed record's seeds, as the seeds' file holds them. -/
def seedsOf (rcd : RecFull) : List (List _root_.Fmt.Ext × _root_.Fmt.Ext) :=
  (OnBytes.K.IdTable.spellSeedL 29 1 rcd.1).map fun y => (y.1.map OnBytes.E.triple, y.2.triple)

/-- The nine parts of a whole typed proof. -/
structure Typed where
  aux : List Token
  cm : Dig 256
  rcd : RecFull
  copy : ℕ
  piT : OneProtocolProof 256 (QT S)
  cm' : Dig 256
  rcd' : RecFull
  piL : OneProtocolProof 256 (QL S)
  piB : OneProtocolProof 256 (QB S)

/-- **The form.** -/
def formOf (q : Typed S) : FormBytes where
  aux := q.aux
  kb := wrFile Carrier.magicKey
    (carrierOf (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
      silK S.runK (digToBytes q.cm) q.piT)
  sb := wrSeeds (seedsOf q.rcd)
  leaf := wrLeaf (entryOf (ckP .two) dsF frS.P.T.a xsF S.dec (digToBytes q.cm) (trAns q.rcd.2)
    (digToBytes q.cm') (trAns q.rcd'.2) q.piL)
  seeds := wrSeeds (seedsOf q.rcd')
  pb := wrFile Carrier.magicProof
    (carrierOf (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
      silP S.runP (digToBytes q.cm') q.piB)

end Johnson.Prover.Print
