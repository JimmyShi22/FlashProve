-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/KeyGlue.lean: the cut of the page to the key file's part, at the test of
OnBytes/K/Arm/FileInj.lean; and that three of the laws which the encoding of
OnBytes/K/Arm/KeyInj.lean asks follow from the laws of that file.

OnBytes/K/Arm/KeyCut.lean cuts the page's strings to one file and to queries that fit, with the two
tests as letters. OnBytes/K/Arm/KeyInj.lean makes an encoding of all typed oracles of it (`mKey`),
under `KeyLaws`. Here the two letters are the tests `fitFb` and `fitG` at the key file's data.

1. What the file contains.
    `keyCutOf P Φ`: the cut at the page P and the data Φ of the test.
    `mKeyOf`: the encoding at that cut.

2. What is checked when the file compiles. The proofs.

3. Theorems.
    `keyLaws_of`: `KeyLaws` at that cut, from `LawsJ` at the key file's data, the laws on the
      spellings that are taken as they are (`TakenCalls`), the size of the configuration's digest,
      and that none of the three labels is the seeds'.

4. What is not claimed.
   That these premises, `LawsJ` among them, hold at any page. That a total code `back` exists at any
   interface. `mKeyOf` has no program: its parser is had by choice (OnBytes/TypedOracleCompiler/Run/PageOf.lean).
   That a verifier's queries fit: the head of OnBytes/K/Arm/FileInj.lean names a case in which they
   cannot fit at this very test, and laws that cannot hold at a test which lets them through; it
   also says what the laws are worth at a test that lets nothing through: `mKeyOf` then writes no
   chain query but what the page's field `seeds` writes. Nothing on any hash. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyInj
import OnBytes.K.Arm.FileInj

set_option autoImplicit false

namespace OnBytes.K.Arm.KeyGlue

open OnBytes.Maker.Page TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.K.Arm.FileInj
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The cut at the test of OnBytes/K/Arm/FileInj.lean.** -/
def keyCutOf (P : PageJ L K) (Φ : FitJ L .test) : KeyCut L K :=
  ⟨P, fun x => fitFb Φ P.key K x.1 x.2, fitG Φ P.key⟩

/-- **The laws that the encoding asks, at that cut.** -/
theorem keyLaws_of (P : PageJ L K) (Φ : FitJ L .test) (h : LawsJ P.key Φ K)
    (T : TakenCalls (keyCutOf P Φ)) (hc : P.cfg.size = digBytes)
    (l1 : P.key.lab₁ ≠ Fmt.recordLabel) (l2 : P.key.lab₂ ≠ Fmt.recordLabel)
    (l3 : P.key.lab₃ ≠ Fmt.recordLabel) : KeyLaws (keyCutOf P Φ) where
  taken := T
  cfg := hc
  lab1 := l1
  lab2 := l2
  lab3 := l3
  fb := fun _ _ _ hf hf' e e' =>
    Prod.ext (fbCallJ_inj h hf hf' e e').1 (fbCallJ_inj h hf hf' e e').2
  g := fun _ _ _ hf hf' e e' => gCallJ_inj h hf hf' e e'
  fbg := fun _ _ _ hf _ e e' => fb_g_apart h hf e e'

/-- **The encoding at that cut.** -/
noncomputable def mKeyOf (P : PageJ L K) (Φ : FitJ L .test) (h : LawsJ P.key Φ K)
    (T : TakenCalls (keyCutOf P Φ)) (hc : P.cfg.size = digBytes)
    (l1 : P.key.lab₁ ≠ Fmt.recordLabel) (l2 : P.key.lab₂ ≠ Fmt.recordLabel)
    (l3 : P.key.lab₃ ≠ Fmt.recordLabel) (back : StrCode (AllPts 256 K L)) :
    OracleCoding (typedOracleFamily 256 K L) 256 :=
  mKey (keyCutOf P Φ) (keyLaws_of P Φ h T hc l1 l2 l3) back

end OnBytes.K.Arm.KeyGlue
