-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofGlue.lean: the cut of the page to the proof file's part, at the test of
OnBytes/K/Arm/FileInj.lean; and that three of the laws which the encoding of
OnBytes/K/Arm/ProofInj.lean asks follow from the laws of that file.

The twin of OnBytes/K/Arm/KeyGlue.lean under the proof file's tag. OnBytes/K/Arm/ProofCut.lean cuts
the page's strings to the proof file and to queries that fit, with the two tests as letters.
OnBytes/K/Arm/ProofInj.lean makes an encoding of all typed oracles of it (`mProof`), under
`ProofLaws`. Here the two letters are the tests `fitFb` and `fitG` at the proof file's data.

1. What the file contains.
    `proofCutOf P Φ`: the cut at the page P and the data Φ of the test.
    `mProofOf`: the encoding at that cut.

2. What is checked when the file compiles. The proofs.

3. Theorems.
    `proofLaws_of`: `ProofLaws` at that cut, from `LawsJ` at the proof file's data, the laws on the
      spellings that are taken as they are (`TakenCallsP`), the size of the configuration's digest,
      and that none of the three labels is the seeds'.

4. What is not claimed.
   That these premises hold at any page. That a verifier's queries fit. Nothing on any hash. Nothing
   on soundness.
   Where the page's first statement holds a request through the format's item, which is made of
   digests of the request, `ProofLaws` cannot hold at a test of fitness that lets the first query of
   every request through: there are more requests than items, so two such queries would have one
   call. Nothing here shows that it holds at any test; what this cause leaves open is a test that
   lets through a set of instances on which the item is one to one. That it is so on a given set is
   a hypothesis on the hash that makes the digests. The set stands in the encoding. Whoever lays it
   has to name it without knowledge of the hash function and before any run; nothing here enforces
   that. For a request outside the set nothing is tied here.
   A chain query of the format f2 that holds an instance never fits. A verifier that hands its
   chains an instance asks such a query where the interface's field `late` names a written round of
   the first or the third chain (OnBytes/K/Arm/FileInj.lean). That `late` names no such round is not
   shown here.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.ProofInj
import OnBytes.K.Arm.FileInj

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofGlue

open OnBytes.Maker.Page TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.K.Arm.FileInj
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The cut at the test of OnBytes/K/Arm/FileInj.lean.** -/
def proofCutOf (P : PageJ L K) (Φ : FitJ L .onl) : ProofCut L K :=
  ⟨P, fun x => fitFb Φ P.proof K x.1 x.2, fitG Φ P.proof⟩

/-- **The laws that the encoding asks, at that cut.** -/
theorem proofLaws_of (P : PageJ L K) (Φ : FitJ L .onl) (h : LawsJ P.proof Φ K)
    (T : TakenCallsP (proofCutOf P Φ)) (hc : P.cfg.size = digBytes)
    (l1 : P.proof.lab₁ ≠ Fmt.recordLabel) (l2 : P.proof.lab₂ ≠ Fmt.recordLabel)
    (l3 : P.proof.lab₃ ≠ Fmt.recordLabel) : ProofLaws (proofCutOf P Φ) where
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
noncomputable def mProofOf (P : PageJ L K) (Φ : FitJ L .onl) (h : LawsJ P.proof Φ K)
    (T : TakenCallsP (proofCutOf P Φ)) (hc : P.cfg.size = digBytes)
    (l1 : P.proof.lab₁ ≠ Fmt.recordLabel) (l2 : P.proof.lab₂ ≠ Fmt.recordLabel)
    (l3 : P.proof.lab₃ ≠ Fmt.recordLabel) (back : StrCode (AllPts 256 K L)) :
    OracleCoding (typedOracleFamily 256 K L) 256 :=
  mProof (proofCutOf P Φ) (proofLaws_of P Φ h T hc l1 l2 l3) back

end OnBytes.K.Arm.ProofGlue
