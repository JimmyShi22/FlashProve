-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/AtWeights.lean: if eight fields hold at the built description (FlashProve.flashProveDescription), at
the library's own map from weights to the committed matrix and on the range of all matrices that
hold an index, then the four clauses about one and the same scheme, the shell frontAt (MeetsRoad,
Bundle.lean), hold there, given the hypothesis Spec.frontPrivacyAt. Conditional, no member known, of
a shell. Not one of the release's goal statements. The premise "every weight's index is in the
range" is proved, so the clause on index privacy, where it holds, speaks of all weights.
Terms and the limits that go with any quote: Spec.lean.

What this file has.
  okThe   the range Flat.InRange: the matrices that hold an index.
  LeftAtWeights   what is left to require at the family layoutsOfBuiltDescription flashProveData allZeroDigest [] Z
      (AtBuiltNamed.lean): LeftToAsk (AtDescription.lean) without its field range: eight fields.
  meetsRoad_weights   At flashProveDescription, all public files Z in scope and all settings s, with idx :=
      FlashProve.backThe Z s and ok := okThe Z: LeftAtWeights gives MeetsRoad, from the hypothesis
      Spec.frontPrivacyAt, a named proposition (proved as frontPrivacyAt in FrontProof.lean; without
      the hypothesis: Joined.lean). By inRange_backThe (RangeOf.lean) and familyLaws_the.

Limits. Here the clause on index privacy rests on the hypothesis.
No honest side with the protocol's three provers is written in Lean. No member of HonAll is known,
and none of PremAll and HonAll together: the theorem may apply to nothing. Of PremAll by itself a
member with two placeholder provers, which send fixed messages, is known, on the range of all
indices; it is stated at flashProveDescription with the number of the committer's coins set to any number b
(premAll_laid, LaidAll.lean).
The wider the range, the more the premises require: here PremAll is required at every matrix that
holds an index.
The theorem is at the built description, whose own committer and prover are placeholders: a
commitment of zeros, and a prover that returns empty files (Johnson/Goal/Description/Honest.lean).
The step to the description that the release's goal statements use is not taken here (the library
proves VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription = flashProveDescription: the_description_is,
Johnson/Goal/TopOfThreeBinding.lean).
At settings that are not valid, backThe sends all weights to one fixed matrix.
Yes is a variable here too, and Rel is required to imply it, not the converse: a Rel that holds of
nothing satisfies that, and then "at all weights" speaks of the key only.
All limits of AtDescription.lean hold.
-/
import Johnson.FrontRoad.AtDescription
import Johnson.FrontRoad.AtBuiltNamed
import Johnson.FrontRoad.RangeOf

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead FlashProve
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The range of indices: the matrices that hold an index (Flat.InRange). -/
def okThe (Z : VerifierAndGoals.PublicFiles) : (flashProveDescription.input Z allZeroDigest []).Index → Prop := fun M => Flat.InRange M

/-- What is left to require at the built description and the library's own map from weights
(backThe): the fields of LeftToAsk without range. -/
structure LeftAtWeights (Z : VerifierAndGoals.PublicFiles) (F : SidesAt (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z)) (G : FallsAt F)
    (s : IntegerTransformer.Settings) (back : (flashProveDescription.input Z allZeroDigest []).Instance → List Token × List Token)
    {Form : Type} (parse : VerifierAndGoals.Parser flashProveDescription Z Form)
    (encF : VerifierAndGoals.TypedProof (flashProveDescription.F Z) (flashProveDescription.P Z) → Form) {PP' : Type}
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Yes : (flashProveDescription.input Z allZeroDigest []).Index → (flashProveDescription.input Z allZeroDigest []).Instance → Prop) (α : ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ) : Prop where
  prem : PremAll F (okThe Z) Yes fun _ => True
  zeta : ZetaLe F (fun _ => True) ζ
  hon : HonAll G Yes fun _ => True
  alpha : AlphaLe G (fun _ => True) α
  undo : UndoOn flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) F.side (backThe Z s) Yes parse encF
  tie : ∀ w x', Rel.rel w x' () →
    ∃ x, (flashProveDescription.input Z allZeroDigest []).buildInstance x' [] = some x ∧ Yes (backThe Z s w) x ∧ back x = x'
  commits : ∀ d, commitN (flashProveDescription.input Z allZeroDigest []).queryLayout (F.side d) ≤ NC
  proves : ∀ d, proveN (flashProveDescription.input Z allZeroDigest []).queryLayout (F.side d) ≤ NP

/-- At the built description, all public files in scope and all settings, LeftAtWeights gives
MeetsRoad at the library's own map from weights, so at all weights, from the hypothesis H
(Spec.frontPrivacyAt), which is not proved here (without it: meetsRoad_weights_joined, Joined.lean).
Conditional, no member known, of a shell. -/
theorem meetsRoad_weights (H : Spec.frontPrivacyAt) (Z : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (F : SidesAt (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z)) (G : FallsAt F)
    (s : IntegerTransformer.Settings) (x₀ : (flashProveDescription.input Z allZeroDigest []).Instance)
    (back : (flashProveDescription.input Z allZeroDigest []).Instance → List Token × List Token) (Form : Type)
    (parse : VerifierAndGoals.Parser flashProveDescription Z Form) (encF : VerifierAndGoals.TypedProof (flashProveDescription.F Z) (flashProveDescription.P Z) → Form)
    (PP' : Type) (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Yes : (flashProveDescription.input Z allZeroDigest []).Index → (flashProveDescription.input Z allZeroDigest []).Instance → Prop) (α : ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ)
    (h : LeftAtWeights Z F G s back parse encF Rel Yes α ζ NC NP) :
    MeetsRoad flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) F s (backThe Z s) x₀ back Form parse encF
      Rel α (8 + NC * ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1) + 1)
      (NP * ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1)) ζ :=
  meetsRoad_of_laws H flashProveDescription Z scope allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) Prod.mk (familyLaws_the Z) F
    G s (backThe Z s) x₀ back Form parse encF PP' Rel Yes (okThe Z) α ζ NC NP
    ⟨h.prem, h.zeta, h.hon, h.alpha, h.undo, fun w => inRange_backThe Z s w, h.tie, h.commits,
      h.proves⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.meetsRoad_weights
