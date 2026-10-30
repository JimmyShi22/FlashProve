-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParserHashProofs.lean: the proofs of the statements of Run/ParserHash.lean.

Main names (statements and hypotheses: Run/ParserHash.lean):
  `ph_oStr`: this library's extension against the format's oracle at the strings `Fmt.oStr`.
  `ph_hI`: the parser's hash `hI (oBits ())` against `Fmt.HO Fmt.oracle`.
  `ph_run`: `run_fam_page` with the parser's text at `Fmt.HO Fmt.oracle`.

`ph_run`: Run/ParserHash.lean: what the run of lenient parser, then compiled verifier, is at
`oBits ()` (Run/OracleBits.lean). `Fmt.oracle`: the format's single oracle on all byte strings, 32
bytes an answer, realised by BLAKE2b; Fmt/Rules23.lean.

Three lemmas of its own, for two facts: the bits of a string of the format's oracle with the half 0
or 1 are "plain" (whole bytes, not beginning with the byte 4) (`take8_oStr`, `plain_oStr`); 32 bytes
come back from their 256 bits (`digToBytes_bytesToDig`).
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ParserHash
import Run.RunIsThinFamProofs
import Run.CodingPage160
import Run.Toy1TieTree

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- the first eight bits of a string of the format's oracle are its half's -/
theorem take8_oStr (half : UInt8) (n t i : Nat) (st bs : ByteArray) :
    (bytesToBits (_root_.Fmt.oStr half n t i st bs)).take 8 = bitsOfByte half := by
  unfold _root_.Fmt.oStr
  rw [bytesToBits_append, bytesToBits_append, bytesToBits_append,
    List.append_assoc, List.append_assoc]
  have e : bytesToBits ⟨#[half]⟩ = bitsOfByte half := List.append_nil _
  rw [e, List.take_append_of_le_length (by rw [length_bitsOfByte]),
    List.take_of_length_le (by rw [length_bitsOfByte])]

theorem plain_oStr (half : UInt8) (n t i : Nat) (st bs : ByteArray) (h : half = 0 ∨ half = 1) :
    plainB (bytesToBits (_root_.Fmt.oStr half n t i st bs)) = true := by
  unfold plainB
  rw [whole_bytesToBits, take8_oStr, Bool.true_and]
  rcases h with rfl | rfl <;> decide

/-- 32 bytes come back from their 256 bits -/
theorem digToBytes_bytesToDig (b : ByteArray) (h : b.size = 32) :
    digToBytes (bytesToDig b) = b := by
  rw [TieTree.bytesToDig_eq, digToBytes_digOf b h]

theorem ph_oStr : Spec.ph_oStr := by
  intro half n t i st bs h
  show digToBytes (oBits () (bytesToBits (_root_.Fmt.oStr half n t i st bs))) = _
  rw [oBits_bytes _ (plain_oStr half n t i st bs h),
    digToBytes_bytesToDig _ (_root_.Fmt.size_oracle _)]

theorem ph_hI : Spec.ph_hI := by
  funext n t i st bs
  show _root_.Fmt.HO (oB (oBits ())) n t i st bs = _root_.Fmt.HO _root_.Fmt.oracle n t i st bs
  unfold _root_.Fmt.HO
  rw [ph_oStr 0 n t i st bs (Or.inl rfl), ph_oStr 1 n t i st bs (Or.inr rfl)]

theorem ph_run :
    Spec.ph_run := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN ivk x b =>
  (run_fam_page I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN ivk x b).trans
    (congrArg (fun h =>
        PMF.pure (famVerdict L sMT sFS t P wq embS embP xin embE depthReq m oBy ivk x
            (keep ivk (parseLaxW (m := Id) h (sp x) T b)))) ph_hI)

end Run
