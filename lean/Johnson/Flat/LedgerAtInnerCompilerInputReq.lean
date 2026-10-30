-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/LedgerAtInnerCompilerInputReq.lean: the named hypothesis "sound" of Johnson/Top/InnerCompiledVerifier.lean at the
full-size input of Johnson/Flat/TwoSizes.lean, where the instances are the requests that the
program's reader takes.

Two theorems, by CompilerSoundnessConditionStatements.sound_of_cells (Johnson/Flat/LedgerAtInnerCompilerInput.lean).
  meaningConditionFromDryRunAtFullSize_paid_on: at A := claimsLedgerOn … N s req, if what T's builder builds is what
    requestOfTokens builds, read by req, and T's model is nextTok s. Its premise on the builder is
    met by a builder that refuses everything: a step, not a form to cite.
  meaningConditionFromDryRunAtFullSize_paid_req: at A := claimsReq … N s, if T's builder is buildReq and T's model is
    nextTok s.
Both at a lawful table of scales and a shape within the reference's. The theorem on innerCompiledVerifier
with three named hypotheses: Johnson/Flat/ThreeFull.lean. That buildReq does not look at a model:
Johnson/Flat/BuiltOK.lean.

Limits: the full size alone. "sound" is traded for three public premises on two letters (a lawful s;
N within the reference shape: two bounds) and for two of T's letters, which are fixed. The meaning
is moved, not shrunk: what "proofSound" then asks of the proof file's protocol is the claim RelL s
at the requests of Req, and what "keySound" then asks of the key file's protocol is InRange: that a
decoded matrix holds a well-formed table of digits. Nothing of either is proved here.

-/
import Johnson.Flat.LedgerAtInnerCompilerInput
import Johnson.Flat.ClaimsReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles

open Inst.Model OnBytes.Flat OnBytes.Slice
open Inst.Model.Layout (kRef hRef)

section
variable {X : Type} (N : MatrixNums) (s : Cm.Scales) (req : X → Instance ppref)
  (E : Coding (claimsLedgerOn (frS.toDecR frZ 402653181) N s req)) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsLedgerOn (frS.toDecR frZ 402653181) N s req) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- "sound" at the full size, for instances that say requests. -/
theorem meaningConditionFromDryRunAtFullSize_paid_on (lawful : s.Lawful) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsLedgerOn (frS.toDecR frZ 402653181) N s req) E G P)
    (hb : ∀ x' a x, T.build x' a = some x → requestOfTokens x' a = some (req x))
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T) :=
  CompilerSoundnessConditionStatements.sound_of_cells (soundnessAnalysisDataFromDryRunAtFullSize T) lawful hr hc
    { cells := fun M => M
      req := req
      build := hb
      next := hn
      rel := fun _ _ _ h => h.2 }

end

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) N s)) (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **"sound" at the full size, at the requests that the reader takes.** -/
theorem meaningConditionFromDryRunAtFullSize_paid_req (lawful : s.Lawful) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T) :=
  meaningConditionFromDryRunAtFullSize_paid_on N s Subtype.val E G P lawful hr hc T
    (fun x' a _ h => Flat.buildReq_some ((hb x' a).symm.trans h)) hn

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.meaningConditionFromDryRunAtFullSize_paid_on
#print axioms VerifiableInference.OnPublicFiles.meaningConditionFromDryRunAtFullSize_paid_req
