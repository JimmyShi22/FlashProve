-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/AtFiles.lean: the object with records that OnBytes/Flat/Object.lean makes of three
files' protocols (`Files.withProvers`), where the key file's and the proof file's are those of values of
OnBytes/Maker/Whole.lean's `reductionOfWholeFile` (`IOR.toInteractiveOracleProof`) and the entry file's is a letter, at
verifier's messages as hash blocks.

  `filesOf`: such a value of `OnBytes.Flat.Files`, over a configuration with words of length 2 ^ a
    over `SgX` (`ConfLetters.conf`, OnBytes/Maker/ConfLetters.lean); the key's and the proof's
    annotations are those of a file with three joined chains (`Chains.ann`); the entry file's
    protocol and marks are the entry's part's (`LinkProtocolWithLeafCoding`, Johnson/EntryRec/OkcFiles.lean). The files'
    data, the tests on what the silent rounds send and the two decisions are letters.
  `lettersOf`: what the object holds beside its three protocols.
  `obj_objF`: the object `(filesOf ..).withProvers P` is Johnson/EntryRec/OkcFiles.lean's `objF`, by
    unfolding.

Limits: those of Johnson/EntryRec/OkcFiles.lean's head. Not shown: the same at a configuration whose
word length and alphabet equal 2 ^ a and `SgX` by a proof only.


-/
import Johnson.EntryRec.OkcFiles
import OnBytes.Maker.ConfLetters
import OnBytes.Flat.Object

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Hiop OnBytes.Maker OnBytes.Flat
open TypedOracleCompiler.Compile.Batch.Cms (Bodies wireOf2 typedOracleCarrier)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → View → View → View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)

/-- **Three files' protocols**: the key file's and the proof file's made by the makers; the entry
file's, with its marks, a letter. -/
@[reducible] def filesOf : Files Kc.conf where
  key := (reductionOfWholeFile (ckP f) (DK.at a) tFk tJk t3k silK runK).toInteractiveOracleProof
  entry := eL.QL
  proof := (reductionOfWholeFile (ckP f) (DP.at a) tFp tJp t3p silP runP).toInteractiveOracleProof
  N := N
  annT := (chainsOf (ckP f) (DK.at a) tFk tJk t3k).ann
  annL := eL.aL
  ann := (chainsOf (ckP f) (DP.at a) tFp tJp t3p).ann
  early := early
  late := late

variable (P : (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
  late).Provers)

/-- What the object holds beside its three protocols. -/
noncomputable def lettersOf :
    Letters Kc.conf.I Kc.conf.X (Kc.conf.Pad × Kc.conf.Rnd) Kc.conf.Seed Kc.conf.Ans a
      (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
      (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch :=
  ⟨fun i r => Kc.conf.enc (Kc.conf.hold i r.1) r.2, fun i r s => Kc.conf.smp s (Kc.conf.hold i r.1),
    Kc.conf.coll, Kc.conf.D, N, P.hT, P.hL, P.hB, early, late⟩

/-- **The object of the three files is `objF`**, by unfolding. -/
theorem obj_objF :
    (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early late).withProvers P =
      objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL
        (lettersOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early late P) := rfl

end OnBytes.RunA
