-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ThreeFull.lean: at the full-size input of Johnson/Flat/TwoSizes.lean, with the claim on
a decoded table written (claimsReq, Johnson/Flat/ClaimsReq.lean), three named hypotheses are left,
not four: "sound" is proved (meaningConditionFromDryRunAtFullSize_paid_req, Johnson/Flat/LedgerAtInnerCompilerInputReq.lean).
It is proved by a trade: five premises that fix parameters stand in its place: T's builder is
buildReq, T's model is nextTok s, s is lawful, and the two bounds on N (at numsRef these two are
theorems). keySound, proofSound and commitment are named hypotheses: none is proved here.

One structure, two definitions, five theorems.
  LeftThreeFull T: keySound, proofSound, commitment.
  soundThreeFull_req: the theorem on innerCompiledVerifier at the full size (innerCompiledVerifierSoundFromDryRunAtFullSize,
    Johnson/Flat/TwoSizes.lean) under LeftThreeFull T and the theorem on codes, at
    A := claimsReq … N s, a lawful table of scales s, numbers N of the matrix within the reference
    shape, T's builder buildReq and T's model nextTok s.
  numsRef, numsRef_fits: the numbers 3,076,096 rows and k_lo = 7: both bounds hold, with equality.
  soundThreeFull_ref: soundThreeFull_req at N := numsRef: the two bounds are no premises there.
  holds_matrixOf: the casts of the entries of an index hold that index.
  relL_met: the claim is not empty: at every lawful table of scales some matrix of the reference
    shape and some request of Req have RelL (all weights and tokens 0, r = 1,023, e = 1,024, y = 0:
    a request with no counted position; Policy.TrueGuards.some_true). That buildReq builds that
    request is not shown. It shows that the claim is not empty, and no more.

WHAT IS MOVED. innerCompiledVerifierSoundFromDryRunAtFullSize speaks of every A. This form speaks of one A, with two letters more, N
and s. The meaning is moved, it is not shrunk. At this A "proofSound" asks that the proof file's
protocol be knowledge sound for RelL s: the committed matrix holds a well-formed table of digits at
which some trace meets the library's relaxed relation with the cost ledger at exact match.
"keySound" asks that what the key file's protocol accepts decodes to a matrix with InRange: one that
holds a well-formed table of digits. Both are hypotheses here.

THE BUILDER. A builder that refused everything would meet "sound" whatever the relation is. Here T's
builder is fixed to buildReq, which returns a request for every prompt and every output of tokens of
the vocabulary of the right lengths, reads back to them, and accepts outputs that are no model's
(Johnson/Flat/BuiltOK.lean: buildReq_total, buildReq_reads, buildReq_asks_no_model).

THREE, NOT FOUR, COUNTS A CHOICE. "wires" is not among the three because the description stands
at one wiring of our own choice (AtOurWiringFull, Johnson/Flat/TwoSizes.lean), in place of every
lawful one: the theorem is narrower there, not stronger; that the programs are wired so is no
statement of Lean. AND THE DATA FAIL CLOSED, by a reading of the makers (no theorem here):
where a guard of the makers of the key file's or the proof file's protocol fails at G, the verifier
refuses every file; "keySound" and "proofSound" are then true and say nothing. That the guards pass
at the shipped files is shown neither in this file nor in a file that it imports, at any G.
Cite soundThreeFull_ref: at other numbers N than numsRef soundThreeFull_req says nothing of the
shipped files.

Limits: the full size alone: the small size keeps four (the library has no such relation there). s
is a letter: nothing here ties it to the scale file from which the letter G is made; at every other
table "proofSound" cannot be expected to hold, so the theorem speaks at one s at most, and this file
does not name it. That numsRef's two numbers are those of the full-size parameter file is not shown.
E, G, P and the rest of T are letters, and the bound holds T.εId and the number of queries of
the compiled verifier at the written wiring, which hangs on the letter G: no number is given
(Johnson/Flat/TwoSizes.lean, Limits). That a table of scales is lawful is shown, in the files that
this one imports, for the library's reference table alone (lawful_sRef, Cm/Rel2Guards.lean). That
the key file's item "ranges" is the planner's at the shipped layout is a public premise that no file
writes (Johnson/Flat/LedgerClaim.lean, "what enforces which clause").

-/
import Policy.Rel.TrueGuards
import Johnson.Flat.LedgerAtInnerCompilerInputReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model
open Inst.Model.Layout (kRef hRef)

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {G : FilesParameters X RecFull}
  {P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- The named hypotheses that are left at the full size where "sound" is proved: three, beside the
theorem on codes. -/
structure LeftThreeFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtFullSize T)

end

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) N s)) (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **Under the three named hypotheses LeftThreeFull T and the theorem on codes** (hypotheses of the
theorem: Lean's list of axioms does not show them): the theorem on innerCompiledVerifier at the full size, at
the claim claimsReq, a lawful s, numbers N within the reference shape, T's builder buildReq and T's
model nextTok s. -/
theorem soundThreeFull_req (hA : BCHKS46At GF GE) (lawful : s.Lawful) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) (h : LeftThreeFull T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtFullSize hA ⟨h.keySound, h.proofSound, h.commitment,
                                      meaningConditionFromDryRunAtFullSize_paid_req N s E G P lawful hr hc T hb hn⟩

end

/-- The committed matrix's numbers at the reference shape: 3,076,096 rows; k_lo = 7. -/
def numsRef : MatrixNums := ⟨3076096, 7⟩

/-- At these numbers the matrix has the reference shape: both bounds hold, with equality. -/
theorem numsRef_fits : numsRef.rows ≤ hRef ∧
    2 ^ (numsRef.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef :=
  ⟨le_refl _, le_of_eq (congrArg (fun k => 2 ^ k)
    (show numsRef.kLo + (frS.toDecR frZ 402653181).v = kRef from rfl))⟩

section
variable (s : Cm.Scales) (E : Coding (claimsReq (frS.toDecR frZ 402653181) numsRef s))
  (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **The same at the numbers of the reference shape.** -/
theorem soundThreeFull_ref (hA : BCHKS46At GF GE) (lawful : s.Lawful)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) (h : LeftThreeFull T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  soundThreeFull_req numsRef s E G P hA lawful numsRef_fits.1 numsRef_fits.2 T hb hn h

end

/-! ## The claim is not empty -/

/-- The casts of the entries of an index, as a matrix of the reference shape. -/
def Flat.matrixOf (i : Cm.Idx) : Fin hRef → Fin (2 ^ kRef) → Flat.GE :=
  fun y c => ((i.mat y.val c.val : ℤ) : Flat.GE)

/-- It holds that index. -/
theorem Flat.holds_matrixOf (i : Cm.Idx) : Flat.Holds (Flat.matrixOf i) i :=
  ⟨fun _ _ => rfl, fun _ _ h => Cm.ext_out i.val h⟩

/-- **The claim is not empty**, at every lawful table of scales. -/
theorem Flat.relL_met {s : Cm.Scales} (hs : s.Lawful) :
    ∃ (M : Fin hRef → Fin (2 ^ kRef) → Flat.GE) (x : Flat.Req), Flat.RelL s M x.val :=
  ⟨Flat.matrixOf (Cm.Idx.ofIndex ScalesSanity.iZero),
    ⟨RequestGuards2.xz ⟨1023, by decide⟩ ⟨1024, by decide⟩, by
      unfold Flat.WellFormed
      exact ⟨by decide, fun _ => rfl⟩⟩,
    (Flat.relL_iff hs _ _).2 ⟨_, Flat.holds_matrixOf _, Policy.TrueGuards.some_true hs AcceptancePolicy.exact⟩⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.soundThreeFull_req
#print axioms VerifiableInference.OnPublicFiles.soundThreeFull_ref
#print axioms VerifiableInference.OnPublicFiles.numsRef_fits
#print axioms VerifiableInference.OnPublicFiles.Flat.holds_matrixOf
#print axioms VerifiableInference.OnPublicFiles.Flat.relL_met
