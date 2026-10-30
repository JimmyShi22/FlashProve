-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/LedgerAtInnerCompilerInput.lean: the named hypothesis "sound" of Johnson/Top/InnerCompiledVerifier.lean at the
full-size input of Johnson/Flat/TwoSizes.lean, with the claim on a decoded table written.

One structure, two theorems. The twin, for `InnerCompilerInput`, of Johnson/Flat/LedgerAt.lean; it rests on
`claimsLedger` (Johnson/Flat/ClaimsLedger.lean) and on `Flat.RelL`, `Flat.nextTok` and
`Flat.sound_core` (Johnson/Flat/LedgerClaim.lean).

Main names:
  `InnerInputIndicesReadAsMatrices b s rows cols`: an input's indices are read as matrices, its instances as requests
    of the model, its builder is `requestOfTokens`, its model the integer model at the index that
    the matrix holds, and its relaxed relation gives the claim `Flat.RelL s`.
  `CompilerSoundnessConditionStatements.sound_of_cells`: then `CompilerSoundnessConditionStatements.sound b`, at a lawful table of scales and a shape within
    the reference's.
  `meaningConditionFromDryRunAtFullSize_paid`: `CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T)` at `A := claimsLedger … N s`, if T's builder
    and model are these two.

Limits: the full size alone. What `proofSound` then asks of the proof file's protocol is the claim
`Flat.RelL s`: nothing of that is proved here. At all of `Instance ppref` "proofSound" asks the
proof file's protocol to refuse requests that the program's reader refuses before it: use the form
at `Req` (Johnson/Flat/LedgerAtInnerCompilerInputReq.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TwoSizes
import Johnson.Flat.ClaimsLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles

open Inst.Model OnBytes.Flat OnBytes.Slice
open Inst.Model.Layout (kRef hRef)

/-- An input's indices are read as matrices, and its relation gives the claim on them. -/
structure InnerInputIndicesReadAsMatrices {r : InnerCompilerInput} (b : SoundnessAnalysisData r) (s : Cm.Scales) (rows cols : ℕ) where
  /-- the matrix of an index -/
  cells : r.Index → Fin rows → Fin cols → Flat.GE
  /-- an instance is a request of the model -/
  req : r.Instance → Instance ppref
  /-- what the input's builder builds is what "requestOfTokens" builds -/
  build : ∀ x' a x, r.buildInstance x' a = some x → requestOfTokens x' a = some (req x)
  /-- the input's model is the integer model at the index that the matrix holds -/
  next : ∀ i l, r.nextToken i l = Flat.nextTok s (cells i) l
  /-- the relaxed relation gives the claim -/
  rel : ∀ i x w, b.Rno i x w → Flat.RelL s (cells i) (req x)

/-- The meaning, at an input on matrices. -/
theorem CompilerSoundnessConditionStatements.sound_of_cells {r : InnerCompilerInput} (b : SoundnessAnalysisData r) {s : Cm.Scales}
    (lawful : s.Lawful) {rows cols : ℕ} (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef)
    (R : InnerInputIndicesReadAsMatrices b s rows cols) : CompilerSoundnessConditionStatements.sound b := by
  intro i x' a x hb hw position h
  obtain ⟨w, hw⟩ := hw
  show r.nextToken i (x'.1 ++ x'.2.take position) = some x'.2[position]
  rw [R.next]
  exact Flat.sound_core lawful hr hc (R.build x' a x hb) (R.rel i x w hw) position h

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsLedger (frS.toDecR frZ 402653181) N s)) (G : FilesParameters (Instance' ppref) RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsLedger (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- "sound" at the full size. -/
theorem meaningConditionFromDryRunAtFullSize_paid (lawful : s.Lawful) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsLedger (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = requestOfTokens x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T) :=
  CompilerSoundnessConditionStatements.sound_of_cells (soundnessAnalysisDataFromDryRunAtFullSize T) lawful hr hc
    { cells := fun M => M
      req := fun x => x
      build := fun x' a _ h => (hb x' a).symm.trans h
      next := hn
      rel := fun _ _ _ h => h.2 }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.sound_of_cells
#print axioms VerifiableInference.OnPublicFiles.meaningConditionFromDryRunAtFullSize_paid
