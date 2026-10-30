-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean: the main soundness statement arm by arm with the public data
in the typed key (Johnson/Top/OnFilesArmsC.lean) IN THE PLAIN NOTION: the extractor reads the
commitment and the committer's log alone and asks the hash function nothing; and the step from the
key to the commitment paid by one hypothesis on the input: no two keys have one code.

Why. Johnson/Top/OnFilesArmsC.lean has that step in one form alone, `HoleArmsC.commitmentO`, for an
extractor that may query, and concludes `SoundForWithO`. Where the key's code is one to one, the
step is the library's own `commitmentBinds_of_code` (Johnson/Top/FrontCommit.lean), which is general
in the key's type, and the conclusion is `SoundForWith` (VerifiableInference/MoreStatements.lean) at
a claim that is a letter: its game is that of `Sound` (VerifiableInference/Statements.lean).

Two definitions (a third, `epsCode`, stands in Johnson/Top/FrontGeneral.lean); statements and
proofs. Nothing new is proved: each proof is one application. The input r is a letter, and so is its
code `r.enc`: no code is written here. The hash function is drawn in every statement.


Main names (namespace `VerifiableInference.OnPublicFiles`):
  `HoleArmsC.commitment b ext εId`: the hypothesis on the commitment in the plain notion:
    `Rec.CommitmentBinds` at `schemeArmsC r`: index binding of the scheme whose verifier holds the
    key itself, at the sum of the three arms' errors, gives index binding of the scheme whose
    verifier holds the hash function's answer at the key's code, with the extractor ext, at the cost
    εId more. After `HoleArms.commitment` (Johnson/Top/OnFilesArms.lean), with ext and εId as
    arguments.
  `extCodeC b`, `epsCode` [Johnson/Top/FrontGeneral.lean]: the library's extractor (find in the log
    the query that was answered by the commitment; read the key back off its string; run b.E at that
    key and the log) and the library's cost, (t + 2)² / 2^256.
  `HoleArmsC.commitment_of_code`: if no two keys have one code, the hypothesis holds at these two.
  `verify_sound_arms_C_ext`: `SoundForWith` of `systemArmsC r` under `CoreArmsC b`, the hypothesis
    on the commitment, the meaning, and a bound on the sum of the errors. After
    `verify_sound_arms_C`.
  `verify_sound_arms_C_plain`: the same with "no two keys have one code" for the hypothesis on the
    commitment.

Limits.
  * "THE COMMITMENT" HERE IS THE PLAIN NOTION's: `Rec.CommitmentBinds` over `BesideArmsC`. It is
    another proposition than the hypotheses on the commitment for an extractor that may query
    (`HoleArmsC.commitmentO`; the like over a public reading): no theorem here leads from one to
    another, and what is paid for one statement of soundness does not count for the other.
  * ONE STEP OF THE TOP IS PAID, UNDER ONE HYPOTHESIS: that `r.enc` is one to one is shown of no
    code here. A code that leaves a part of the key out does not meet it.
  * THAT HYPOTHESIS HOLDS FOR NOTHING AT A CODE THAT GIVES NO KEY A CODE (`fun _ => none`). There
    the verifier refuses every proof and `SoundForWith` is free. It says something only where keys
    have codes; nothing here asks that. (A tie's clause "the key that a parser returns has a code"
    does not shut the empty code out either: it speaks only where the verifier says yes.)
  * THAT STEP ALONE DOES NOT BRING A TOP TO THE PLAIN NOTION. `CoreArmsC b` stays a hypothesis, and
    its shape asks much: `CoreArmsC.binds` is index binding with an inner extractor b.E that reads
    the key and the log ALONE, at keys whose c a committer names after its queries. At arms that ASK
    the hash function for their public digests the bounds that are meant are those with the reading
    drawn in the experiment (`ZKCP.Gen.ArmBoundD`, Johnson/Top/ArmsD.lean), and there the inner
    extractor queries. This file serves only where the three arms' bounds are had in the shape of
    `CoreArmsC`: by the bridge from the arm that reads to the arm that is told
    (Johnson/Top/ArmsTold.lean), which tells the key the WHOLE of what the arm reads. Where an arm
    reads more than c (a second public digest), that bridge does not reach.
  * `HoleArmsC.commitment` IS AN ARROW; its left side is `CoreArmsC.binds`.
  * That the arms test c, or a record's seed, is asked by no hypothesis here; this step does not
    need it; the arms' own promises do.
  * `extCodeC b` reads a key back off a string by choice: it is a function, no program.
  * THE PREMISES CAN BE MET TOGETHER FOR NOTHING, cheaply: arms that always say no; a relation that
    nothing meets; a builder that makes no instance; errors of 0 at such arms, or infinite ones (no
    premise asks that ε t is below 1). No premise asks that the verifier ever says yes.
  * All premises are hypotheses of the theorems: Lean's list of axioms does not show them. No input
    is given. All limits of the heads of Johnson/Top/OnFilesArmsC.lean and
    Johnson/Top/FrontCommit.lean stand. Soundness alone. For proofs only; no program imports this
    file.
-/
import Johnson.Top.OnFilesArmsC
import Johnson.Top.FrontCommit
import Johnson.Top.FrontGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC} (b : BesideArmsC r)

/-- The commitment, in the plain notion: the extractor ext reads the commitment and the committer's
log alone. -/
def HoleArmsC.commitment
    (ext : ZKCP.Extractor 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (εId : ℕ → ℝ≥0∞) : Prop :=
  Rec.CommitmentBinds (schemeArmsC r) b.E r.enc ext (IsTrueArmsC b)
    (fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)) εId

/-- The library's extractor behind the hash function's answer at a key's code. -/
def extCodeC : ZKCP.Extractor 256 r.I r.X Unit (ZKCP.Digest 256)
    ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL) :=
  (ZKCP.Special.extOf b.E).digestKey r.enc

/-- **If no two keys have one code, the hypothesis on the commitment holds in the plain notion**, at
the library's extractor and cost. One application of `commitmentBinds_of_code`
(Johnson/Top/FrontCommit.lean) at the wider key. -/
theorem HoleArmsC.commitment_of_code (h : ZKCP.CodeIsOneToOne r.enc) :
    HoleArmsC.commitment b (extCodeC b) epsCode :=
  Rec.commitmentBinds_of_code (schemeArmsC r) b.E r.enc h (IsTrueArmsC b)
    fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)

variable {b}

/-- Under `CoreArmsC b` (five named hypotheses), `HoleArmsC.commitment b ext εId`,
`HoleArmsC.soundFor b claim` and a bound ε on the sum of the errors (hypotheses of the theorem:
Lean's list of axioms does not show them): for every committer and every prover whose bounds on
queries to the hash function add up to t, the probability that the verifier of `systemArmsC r`
accepts while the extractor, which reads the commitment and the committer's log alone, gives no
index, or an index at which the claim fails, is at most ε t. -/
theorem verify_sound_arms_C_ext (claim : r.I → List Token → List Token → Prop)
    (ext : ZKCP.Extractor 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (εId ε : ℕ → ℝ≥0∞)
    (h : CoreArmsC b) (hc : HoleArmsC.commitment b ext εId) (hs : HoleArmsC.soundFor b claim)
    (hε : ∀ tC tP, b.εK tC tP + (b.εE tC tP + b.εP tC tP) + εId (tC + tP) ≤ ε (tC + tP)) :
    SoundForWith (systemArmsC r)
      (ext.buildInstance : ZKCP.Extractor 256 r.I (List Token × List Token) Unit (ZKCP.Digest 256)
        (List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL))).Ei claim ε :=
  Rec.soundForWith_systemE_ext (schemeArmsC r) b.E r.enc ext r.bound r.π₀ r.nextToken h.binds
    h.noCoin_scheme hc claim b.x₀ hs hε

/-- **The same with "no two keys have one code" for the hypothesis on the commitment.** -/
theorem verify_sound_arms_C_plain (claim : r.I → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (h : CoreArmsC b) (hcode : ZKCP.CodeIsOneToOne r.enc) (hs : HoleArmsC.soundFor b claim)
    (hε : ∀ tC tP, b.εK tC tP + (b.εE tC tP + b.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)) :
    SoundForWith (systemArmsC r)
      ((extCodeC b).buildInstance : ZKCP.Extractor 256 r.I (List Token × List Token) Unit
        (ZKCP.Digest 256)
        (List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL))).Ei claim ε :=
  verify_sound_arms_C_ext claim (extCodeC b) epsCode ε h (HoleArmsC.commitment_of_code b hcode) hs
    hε

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.HoleArmsC.commitment_of_code
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_C_ext
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_C_plain
