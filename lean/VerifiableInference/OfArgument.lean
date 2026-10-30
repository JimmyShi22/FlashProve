-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/OfArgument.lean

From a scheme (`ZKCP.Arg`, ZKCP/Defs.lean) to an argument system of
VerifiableInference/Statements.lean.
`ArgumentSystem.ofArgument A commit nextToken` is the argument system of a scheme A
  * whose verifier's keys are 256-bit values and whose instances are a prompt with output tokens,
  * whose relation has no witness,
  * whose committer samples one number and then computes the key by `commit`, with the index and
    that number as the prover's key (`A.CommitsFromCoins commit`, ZKCP/CommitsFromCoins.lean), and
  * whose verifier samples nothing.
Its weights are the indices of A, its model is `nextToken`, and it has no public parameters.
Under the last two conditions the argument system, read back as a scheme, is A
(`ArgumentSystem.uploadArgument_ofArgument`). What holds of A then holds of the argument system:
  `soundForWith_ofArgument`, `sound_ofArgument`     from index binding
  `completeOn_ofArgument_of_relationOn`             from completeness
  `zeroKnowledgeOn_ofArgument_of_relationOn`        from the stronger form of index privacy
  `extracts_ofArgument`                             from "the extracted index is the committed one"
  `queryBound_verify_ofArgument`, `queryBound_commit_ofArgument`    bounds on queries
  `soundAfterHonestCommitmentFor_ofArgument`        from index binding and extraction together
The extractor is the first part of the scheme's extractor E. No bound grows, but: soundness takes a
bound in tC + tP that is at least the scheme's bound in tC and tP, and soundness after an honest
commitment adds two bounds.
What the file does not say. It is about no particular scheme, and it does not say that a scheme of
this form exists. It gives no soundness and no binding at a value of the committer's number that
somebody has chosen: `SoundAndBinding` and `SoundOpened` are not reached in this file. The second
clause of `SoundAndBinding`, for a given extractor, is proved in another file:
`bindsWith_ofArgument` (VerifiableInference/OfArgumentBinds.lean), under the hypotheses of its
statement. A bound on a probability that is 1 or more says nothing.
-/
import VerifiableInference.AgreementWith
import VerifiableInference.Deterministic
import VerifiableInference.ZeroKnowledgeOn
import ZKCP.CommitsFromCoins
import ZKCP.LanguageRelation
import ZKCP.SameV

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

open RandomizedAlgorithm

variable {I Pf : Type} {bound : ℕ}
  (A : ZKCP.Arg 256 I (List Token × List Token) Unit (ZKCP.Digest 256) (I × Fin (bound + 1)) Pf)
  (commit : I → Fin (bound + 1) → ZKCP.OComp 256 (ZKCP.Digest 256))
  (nextToken : I → List Token → Option Token)

/-! ## 1. The argument system -/

/-- The argument system of a scheme whose verifier's keys are 256-bit values and whose instances are
a prompt with output tokens. The weights are the scheme's indices; the model is `nextToken`; there
are no public parameters. The committer samples one number from 0, …, `bound` and makes the queries
of `commit`; the prover is the scheme's, with the weights and that number as its key; the verifier
makes the queries of the scheme's verifier.
Where `commit` or the scheme's verifier samples a number, the algorithm here continues with 0
(`deterministicOf`). The theorems of this file that need it ask that they sample nothing. -/
def ArgumentSystem.ofArgument : ArgumentSystem where
  Weights := I
  PublicParameters := Unit
  publicParameters := fun _ => ()
  CommitmentRandomness := Fin (bound + 1)
  Proof := Pf
  nextToken := nextToken
  sampleCommitmentRandomness := .sample bound fun coins => .done coins
  commit := fun weights coins => deterministicOf (commit weights coins)
  prove := fun weights coins prompt output => ofUpload (A.P (weights, coins) (prompt, output) ())
  verify := fun commitment prompt output proof =>
    deterministicOf (A.V commitment (prompt, output) proof)

/-- "The output tokens are the model's", for this argument system, written out: each output token is
`nextToken` at the index, after the prompt and the output tokens before it. -/
theorem isModelOutput_ofArgument (i : I) (prompt output : List Token) :
    (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i prompt output ↔
      ∀ position (h : position < output.length),
        nextToken i (prompt ++ output.take position) = some output[position] :=
  Iff.rfl

/-- The relation of this argument system is "the output tokens are the model's", without a witness
and with no public parameters. -/
theorem uploadRelation_ofArgument :
    (ArgumentSystem.ofArgument A commit nextToken).uploadRelation
      = ZKCP.languageRelation fun i (x : List Token × List Token) =>
          (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i x.1 x.2 :=
  rfl

/-- The relation of this argument system on a set of instances is "`domain` holds and the output
tokens are the model's", without a witness and with no public parameters. -/
theorem uploadRelationOn_ofArgument (domain : I → List Token → List Token → Prop) :
    (ArgumentSystem.ofArgument A commit nextToken).uploadRelationOn domain
      = ZKCP.languageRelation fun i (x : List Token × List Token) => domain i x.1 x.2 ∧
          (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i x.1 x.2 :=
  rfl

/-! ## 2. The argument system, read back as a scheme -/

/-- The committer of the argument system, in the form of ZKCP/Defs.lean, is the scheme's committer,
if that one samples one number and then computes the key by `commit` (`A.CommitsFromCoins commit`).
-/
theorem ArgumentSystem.uploadArgument_ofArgument_C (hC : A.CommitsFromCoins commit) :
    (ArgumentSystem.ofArgument A commit nextToken).uploadArgument.C = A.C := by
  refine funext fun (i : I) => ?_
  rw [hC.committer i]
  show ZKCP.OComp.sample bound (fun coins =>
      ((deterministicOf (commit i coins)).toRandomized.bind fun commitment =>
        RandomizedAlgorithm.done (commitment, (i, coins))).toUpload)
    = ZKCP.OComp.sample bound fun coins => (commit i coins).mapO fun key => (key, (i, coins))
  refine congrArg _ (funext fun coins => ?_)
  rw [toUpload_bind, toUpload_deterministicOf (commit i coins) (hC.noCoin i coins)]
  rfl

/-- The prover of the argument system, in the form of ZKCP/Defs.lean, is the scheme's prover. -/
theorem ArgumentSystem.uploadArgument_ofArgument_P :
    (ArgumentSystem.ofArgument A commit nextToken).uploadArgument.P = A.P :=
  funext fun secret => funext fun x => funext fun _ => toUpload_ofUpload (A.P secret x ())

/-- The verifier of the argument system, in the form of ZKCP/Defs.lean, is the scheme's verifier, if
that one samples nothing. -/
theorem ArgumentSystem.uploadArgument_ofArgument_V
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin) :
    (ArgumentSystem.ofArgument A commit nextToken).uploadArgument.V = A.V :=
  funext fun key => funext fun x => funext fun proof =>
    toUpload_deterministicOf (A.V key x proof) (hV key x proof)

/-- If the scheme's committer samples one number and then computes the key by `commit`, and its
verifier samples nothing, then the three algorithms of the argument system, in the form of
ZKCP/Defs.lean, are the scheme. -/
theorem ArgumentSystem.uploadArgument_ofArgument (hC : A.CommitsFromCoins commit)
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin) :
    (ArgumentSystem.ofArgument A commit nextToken).uploadArgument = A :=
  ZKCP.Arg.eq_of_parts (ArgumentSystem.uploadArgument_ofArgument_C A commit nextToken hC)
    (ArgumentSystem.uploadArgument_ofArgument_P A commit nextToken)
    (ArgumentSystem.uploadArgument_ofArgument_V A commit nextToken hV)

/-! ## 3. Soundness -/

/-- Soundness for a claim, with the extractor named. Let the scheme's verifier sample nothing. If
the scheme has index binding with the extractor E and the bound ε₂, for the relation "the claim
holds at the index for the prompt and the output tokens", and ε₂ tC tP is at most ε (tC + tP), then
soundness for the claim holds for the argument system with the extractor `E.Ei` and the bound ε.
Nothing is asked of the committer: the experiment of index binding runs only the scheme's verifier.
-/
theorem soundForWith_ofArgument (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (claim : I → List Token → List Token → Prop)
    (E : ZKCP.Extractor 256 I (List Token × List Token) Unit (ZKCP.Digest 256) Pf)
    (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hE : ZKCP.HasIndexBindingWith
      (ZKCP.languageRelation fun i (x : List Token × List Token) => claim i x.1 x.2) A E ε₂)
    (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) :
    SoundForWith (ArgumentSystem.ofArgument A commit nextToken) E.Ei claim ε :=
  soundForWith_of_indexBindingWith (ArgumentSystem.ofArgument A commit nextToken)
    (ZKCP.languageRelation fun i (x : List Token × List Token) => claim i x.1 x.2) claim
    (fun _ _ h => h) E ε₂ ε
    ((ZKCP.SameV.hasIndexBindingWith_iff
      (ArgumentSystem.uploadArgument_ofArgument_V A commit nextToken hV) _ E ε₂).2 hE) hε

/-- `Sound`. Let the scheme's verifier sample nothing. If the scheme has index binding with an
extractor E and the bound ε₂, for the relation "the output tokens are the model's", and ε₂ tC tP is
at most ε (tC + tP), then the argument system is sound with the bound ε. -/
theorem sound_ofArgument (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (E : ZKCP.Extractor 256 I (List Token × List Token) Unit (ZKCP.Digest 256) Pf)
    (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hE : ZKCP.HasIndexBindingWith
      (ZKCP.languageRelation fun i (x : List Token × List Token) =>
        (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i x.1 x.2) A E ε₂)
    (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) :
    Sound (ArgumentSystem.ofArgument A commit nextToken) ε :=
  ⟨E.Ei, soundForWith_ofArgument A commit nextToken hV
    (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput E ε₂ ε hE hε⟩

/-! ## 4. Completeness, zero-knowledge, extraction -/

/-- Completeness on a set of instances. Let the scheme's committer sample one number and then
compute the key by `commit`, and let its verifier sample nothing. If the scheme has completeness
error α for the relation "`domain` holds at the index for the prompt and the output tokens, and the
output tokens are the model's", then the argument system is complete on `domain` with the bound α.
-/
theorem completeOn_ofArgument_of_relationOn (hC : A.CommitsFromCoins commit)
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (domain : I → List Token → List Token → Prop) (α : ℝ≥0∞)
    (h : ZKCP.HasCompletenessError
      (ZKCP.languageRelation fun i (x : List Token × List Token) => domain i x.1 x.2 ∧
        (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i x.1 x.2) A α) :
    CompleteOn (ArgumentSystem.ofArgument A commit nextToken) domain α := by
  refine completeOn_of_completenessError (ArgumentSystem.ofArgument A commit nextToken)
    (ZKCP.languageRelation fun i (x : List Token × List Token) => domain i x.1 x.2 ∧
      (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i x.1 x.2) domain
    (fun _ _ _ hDomain hOutput => ⟨hDomain, hOutput⟩) α ?_
  rw [ArgumentSystem.uploadArgument_ofArgument A commit nextToken hC hV]
  exact h

/-- In particular, under the hypotheses below, from completeness error α for the relation "`domain`
holds at the index for the prompt and the output tokens" alone. That premise asks more: it speaks
also of requests whose output tokens are not the model's. -/
theorem completeOn_ofArgument (hC : A.CommitsFromCoins commit)
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (domain : I → List Token → List Token → Prop) (α : ℝ≥0∞)
    (h : ZKCP.HasCompletenessError
      (ZKCP.languageRelation fun i (x : List Token × List Token) => domain i x.1 x.2) A α) :
    CompleteOn (ArgumentSystem.ofArgument A commit nextToken) domain α :=
  completeOn_ofArgument_of_relationOn A commit nextToken hC hV domain α
    fun i x w hx => h i x w (And.left hx)

/-- Zero-knowledge on a set of requests. Let the scheme's committer sample one number and then
compute the key by `commit`, and let its verifier sample nothing. If the scheme has the stronger
form of index privacy (ZKCP/Defs.lean: HasStrongIndexPrivacyWith) with the simulator S and the bound
ζ, for the relation "`domain` holds at the index for the prompt and the output tokens, and the
output tokens are the model's", then the argument system is zero-knowledge on `domain` with the
bound ζ (`ZeroKnowledgeOn`; its limits: the head of VerifiableInference/ZeroKnowledgeOn.lean). The
argument system has no public parameters: the simulator is given the number of proofs, each query of
the verifier to the hash function, which it answers in the hash function's place, and, for each
proof, the prompt and the output tokens; nothing else. -/
theorem zeroKnowledgeOn_ofArgument_of_relationOn (hC : A.CommitsFromCoins commit)
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (domain : I → List Token → List Token → Prop) (ζ : ℕ → ℕ → ℝ≥0∞)
    (S : ZKCP.Simulator 256 Unit (ZKCP.Digest 256) (List Token × List Token) Pf)
    (h : ZKCP.HasStrongIndexPrivacyWith
      (ZKCP.languageRelation fun i (x : List Token × List Token) => domain i x.1 x.2 ∧
        (ArgumentSystem.ofArgument A commit nextToken).IsModelOutput i x.1 x.2) A S ζ) :
    ZeroKnowledgeOn (ArgumentSystem.ofArgument A commit nextToken) domain ζ := by
  refine zeroKnowledgeOn_of_privacy (ArgumentSystem.ofArgument A commit nextToken) domain ζ S ?_
  rw [ArgumentSystem.uploadArgument_ofArgument A commit nextToken hC hV]
  intro i Z hZ
  exact h i Z hZ

/-- In particular, under the hypotheses below, from the stronger form of index privacy for the
relation "`domain` holds at the index for the prompt and the output tokens" alone. That premise asks
more: it speaks also of requests whose output tokens are not the model's. -/
theorem zeroKnowledgeOn_ofArgument (hC : A.CommitsFromCoins commit)
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (domain : I → List Token → List Token → Prop) (ζ : ℕ → ℕ → ℝ≥0∞)
    (S : ZKCP.Simulator 256 Unit (ZKCP.Digest 256) (List Token × List Token) Pf)
    (h : ZKCP.HasStrongIndexPrivacyWith
      (ZKCP.languageRelation fun i (x : List Token × List Token) => domain i x.1 x.2) A S ζ) :
    ZeroKnowledgeOn (ArgumentSystem.ofArgument A commit nextToken) domain ζ :=
  zeroKnowledgeOn_ofArgument_of_relationOn A commit nextToken hC hV domain ζ S
    fun i Z hZ => h i Z fun view x w hChoice => And.left (hZ view x w hChoice)

/-- Extraction of the honest committer's weights. Let the scheme's committer sample one number and
then compute the key by `commit`. If the extractor E returns the honest committer's index except
with probability at most δ (ZKCP/Optional.lean: HasExtractionError), then `E.Ei` gives back the
honest committer's weights except with probability at most δ. -/
theorem extracts_ofArgument (hC : A.CommitsFromCoins commit)
    (E : ZKCP.Extractor 256 I (List Token × List Token) Unit (ZKCP.Digest 256) Pf) (δ : ℝ≥0∞)
    (h : ZKCP.HasExtractionError A E δ) :
    ExtractsCommittedWeights (ArgumentSystem.ofArgument A commit nextToken) E.Ei δ := by
  refine extracts_of_extractionError (ArgumentSystem.ofArgument A commit nextToken) E δ ?_
  intro i
  rw [ArgumentSystem.uploadArgument_ofArgument_C A commit nextToken hC]
  exact h i

/-! ## 5. Queries -/

/-- A bound on the queries of the scheme's verifier, at a commitment, a prompt, output tokens and a
proof, holds for the verifier of the argument system. -/
theorem queryBound_verify_ofArgument (commitment : Commitment) (prompt output : List Token)
    (proof : Pf) (queries : ℕ)
    (h : (A.V commitment (prompt, output) proof).QueryBound queries) :
    ((ArgumentSystem.ofArgument A commit nextToken).verify commitment prompt output
      proof).toRandomized.QueryBound queries :=
  queryBound_deterministicOf _ queries h

/-- Let the scheme's committer sample one number and then compute the key by `commit`. A bound on
its queries at the index i holds for the honest committer of the argument system at i. -/
theorem queryBound_commit_ofArgument (hC : A.CommitsFromCoins commit) (i : I) (queries : ℕ)
    (h : (A.C i).QueryBound queries) :
    ((ArgumentSystem.ofArgument A commit nextToken).sampleCommitmentRandomness.bind
      fun randomness => ((ArgumentSystem.ofArgument A commit nextToken).commit i
        randomness).toRandomized).QueryBound queries :=
  show ∀ coins : Fin (bound + 1), (deterministicOf (commit i coins)).toRandomized.QueryBound queries
  from fun coins => queryBound_deterministicOf _ queries (hC.queryBound_commit i queries h coins)

/-! ## 6. Soundness after an honest commitment -/

/-- Soundness after an honest commitment, from index binding and extraction. Let the scheme's
committer sample one number and then compute the key by `commit`, and let its verifier sample
nothing. Let the scheme have index binding with the extractor E and a bound ε₂ with
ε₂ tC tP ≤ ε (tC + tP), for the relation "the claim holds at the index for the prompt and the output
tokens", and let E return the honest committer's index except with probability at most δ. Then
`SoundAfterHonestCommitmentFor` holds for the argument system and the claim, with the bound
ε (committerQueries + proverQueries) + δ: the honest committer's own queries count as if the prover
had made them. -/
theorem soundAfterHonestCommitmentFor_ofArgument (hC : A.CommitsFromCoins commit)
    (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (claim : I → List Token → List Token → Prop)
    (E : ZKCP.Extractor 256 I (List Token × List Token) Unit (ZKCP.Digest 256) Pf)
    (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hE : ZKCP.HasIndexBindingWith
      (ZKCP.languageRelation fun i (x : List Token × List Token) => claim i x.1 x.2) A E ε₂)
    (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) (hδ : ZKCP.HasExtractionError A E δ) :
    SoundAfterHonestCommitmentFor (ArgumentSystem.ofArgument A commit nextToken) claim
      fun committerQueries proverQueries => ε (committerQueries + proverQueries) + δ :=
  SoundForWith.soundAfterHonestCommitmentFor (ArgumentSystem.ofArgument A commit nextToken) E.Ei
    claim ε δ (soundForWith_ofArgument A commit nextToken hV claim E ε₂ ε hE hε)
    (extracts_ofArgument A commit nextToken hC E δ hδ)

end VerifiableInference

#print axioms VerifiableInference.ArgumentSystem.uploadArgument_ofArgument
#print axioms VerifiableInference.soundForWith_ofArgument
#print axioms VerifiableInference.sound_ofArgument
#print axioms VerifiableInference.completeOn_ofArgument_of_relationOn
#print axioms VerifiableInference.completeOn_ofArgument
#print axioms VerifiableInference.zeroKnowledgeOn_ofArgument_of_relationOn
#print axioms VerifiableInference.zeroKnowledgeOn_ofArgument
#print axioms VerifiableInference.extracts_ofArgument
#print axioms VerifiableInference.queryBound_verify_ofArgument
#print axioms VerifiableInference.queryBound_commit_ofArgument
#print axioms VerifiableInference.soundAfterHonestCommitmentFor_ofArgument
#print axioms VerifiableInference.isModelOutput_ofArgument
#print axioms VerifiableInference.uploadRelation_ofArgument
#print axioms VerifiableInference.uploadRelationOn_ofArgument
#print axioms VerifiableInference.ArgumentSystem.uploadArgument_ofArgument_C
#print axioms VerifiableInference.ArgumentSystem.uploadArgument_ofArgument_P
#print axioms VerifiableInference.ArgumentSystem.uploadArgument_ofArgument_V
