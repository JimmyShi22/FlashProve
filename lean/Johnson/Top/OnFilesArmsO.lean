-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesArmsO.lean: the main soundness statement arm by arm
(Johnson/Top/OnFilesArms.lean) with an extractor that may query the hash function behind the
commitment.

One definition and one theorem with its proof.
  `HoleArms.commitmentO b extO q εO`: the hypothesis on the commitment in the game of
    Johnson/Top/GameO.lean: index binding of the scheme whose verifier holds the key itself, in
    `bindingExp`'s own game, gives index binding behind the hash function's answer at the key's
    code with the extractor `extO`, which asks the hash function at most q times and draws no coin.
  `verify_sound_arms_O`: `SoundForWithO` (Johnson/Top/SoundO.lean) of `systemArms r`, from index
    binding of the scheme whose verifier holds the key itself, "no arm draws a coin", that
    hypothesis and the meaning.
Limits: those of Johnson/Top/OnFilesArms.lean, Johnson/Top/GameO.lean and Johnson/Top/SoundO.lean.
All five premises are hypotheses of the theorem: Lean's list of axioms does not show them. The
extractor, its budget and its bound are letters. The error of the conclusion is the letter εO of
the hypothesis on the commitment: the three arms' errors enter the statement only as that
hypothesis's premise. "The bound is the sum of three" is not what this theorem states: whoever
proves `HoleArms.commitmentO` has to carry the sum inside εO.

-/
import Johnson.Top.OnFilesArms
import Johnson.Top.SoundO

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArms} (b : BesideArms r)

/-- The commitment, in the game where the extractor may query the hash function. -/
def HoleArms.commitmentO
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞) : Prop :=
  Rec.CommitmentBindsO (schemeArms r) b.E r.enc extO q (IsTrueArms b)
    (fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)) εO

variable {b}

/-- Under its five premises (hypotheses of the theorem: Lean's list of axioms does not show them):
for every committer and every prover whose bounds on queries to the hash function add up to t, the
probability that `verifyArms r` accepts while the extractor, which reads the commitment and the
committer's log and asks the hash function at most q times, gives no index, or an index at which the
claim fails, is at most ε t. -/
theorem verify_sound_arms_O (claim : r.I → List Token → List Token → Prop)
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hb : ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueArms b)))
      (schemeArms r) b.E fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP))
    (hn : HoleArms.noCoin (r := r)) (hc : HoleArms.commitmentO b extO q εO)
    (hs : HoleArms.soundFor b claim) (hε : ∀ tC tP, εO tC tP ≤ ε (tC + tP)) :
    SoundForWithO (systemArms r) (fun c l => deterministicOf (extO.Ei c l)) q claim ε :=
  Rec.soundForWithO_systemE (schemeArms r) b.E r.enc extO q r.bound r.π₀ r.nextToken hb
    (noCoin_schemeArms hn) hc claim b.x₀ hs hε

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_O
