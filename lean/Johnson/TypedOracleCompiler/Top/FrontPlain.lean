-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/FrontPlain.lean: THE FRONT VERIFIER's SOUNDNESS IN `Sound`'s OWN TEXT, UNDER THE
NAMED FIELDS OF ONE STRUCTURE: `Sound` (VerifiableInference/Statements.lean), whose extractor reads
the commitment and the committer's log alone, of the system whose verifier is the front verifier of
Johnson/Top/FrontParts.lean.

IT HAS THE SHAPE OF AN UNCONDITIONAL STATEMENT, NOT ITS STRENGTH: one verifier, a function of
(files, hash); one theorem that ends in `Sound` over a drawn hash function. Its weight stands in the
fields, and most of them are open.

Why. Johnson/Top/FrontParts.lean has one structure of named hypotheses, `FrontFields`, for the game
whose extractor may query (`front_sound`). Its `front_sound_text` ends in `Sound` and takes one bare
premise: `SoundForWith` of the three arms' system. What pays that premise (OnFilesArmsCPlain.lean)
stood in no structure. Here it does, and Lean says that the two files meet.

One structure; statements and proofs. Nothing new is proved: each proof is one or two applications.
The hash function is drawn in every statement; what fixed functions a front verifier's own text
holds beside it is p's matter: p is a letter here.


Main names (namespace `VerifiableInference.OnPublicFiles`):
  `FrontFieldsPlain p b ε`: ALL NAMED HYPOTHESES: `parts` (`FrontParts p`: the request; the four
    parts `idPart`, `keyPart`, `entryPart`, `proofPart`; the parser's budget; the way out's price);
    `arms` (`CoreArmsC b`: the three arms' bounds over a drawn function, the inner extractor's form,
    no coin); `code` (the top's step "the commitment": no two keys have one code); `meaning` (what
    is true of the extracted index is "the output tokens are the model's"); `error` (ε bounds the
    three arms' errors and (t + 2)² / 2^256).
  `front_sound_plain`: THE TOP: under these: `Sound (systemPortC p)` at the error ε (t + n) + δ t.

WHICH FIELDS ARE OPEN. All: none is paid here.

Limits.
  * EVERY FIELD IS A HYPOTHESIS; a conditional theorem holds for nothing where a field is false.
  * NO FIELD ASKS THAT THE FRONT VERIFIER EVER SAYS YES. A parser that returns a key without a code,
    or strings that the arms refuse, gives a front verifier that never says yes: every field of
    `parts` holds, and `Sound` holds of nothing. With every part that holds by definition more of
    the weight moves onto the parser: that what it returns is accepted wherever the programs' own
    proofs are. The test of emptiness stands beside this file, not in it: completeness of the front
    verifier's system, or one run at a stored example.
  * `arms` ASKS MUCH: index binding with an inner extractor that reads the key and the log ALONE, at
    keys whose c a committer names after its queries. The bridge that tells the key the WHOLE of
    what the arms read (Johnson/Top/ArmsTold.lean) gives it from bounds with the public reading
    drawn in the experiment; where an arm reads more public digests than the key holds, that bridge
    does not reach. b is another "beside" than that of `FrontFields` (`BesideArmsC`, not
    `BesideArmsCD`): this is a second top, not that one with a field turned.
  * `code` holds for nothing at a code that gives no key a code; `idPart` shuts that out only where
    the front verifier says yes.
  * `code` AND "IT SAYS YES SOMEWHERE" CAN BE AT ODDS at a front verifier that compares the ID by a
    hand-written text of its own and also runs the check of FrontIdPart.lean [not in this library].
    The hand-written text forms the commitment ID itself and compares; the check laid in asks the
    hash function at `r.enc`'s string. If `r.enc` writes another string than the hand-written text
    hashes, a yes needs two strings with one answer, for every parser: the top is then soundness of
    a verifier that all but never says yes. If `r.enc` writes the hand-written text's own string and
    that string leaves a part of the key out, `code` is false. Both fields can hold with a yes only
    where the hand-written text hashes a string that spells the whole key.
  * A FIELD OF `parts` THAT IS HAD BY LAYING A CHECK INTO THE VERIFIER IS HAD OF THE CHANGED
    VERIFIER ALONE (the limits of FrontIdPart.lean [not in this library]).
  * THE FIELDS CAN BE MET TOGETHER FOR NOTHING, cheaply: arms or a port that always say no; a
    relation that nothing meets; a builder that makes no instance; infinite errors (no field asks
    that ε t is below 1); a parser that is honest but for the link's string, or but for the key's
    code: just the parts that are had by definition.
  * THE SYSTEM IS NEITHER A PROGRAM THAT RUNS NOR THE COMPILER's OUTPUT: its verifier is `p.port`,
    its model `r.nextToken`: letters.
  * r, p, b and ε are letters: no written input, parser, way out or number is given. That the arms
    are a compiler's output is not said here.
  * One way: the front verifier accepts only what the protocol's arms accept, outside a way out with
    a price.
  * All limits of the heads of Johnson/Top/FrontParts.lean and OnFilesArmsCPlain.lean stand.
    Soundness alone. For proofs only; no program imports this file.
-/
import Johnson.Top.FrontParts
import Johnson.TypedOracleCompiler.Top.OnFilesArmsCPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC}

/-- ALL NAMED HYPOTHESES of the top in the plain notion. -/
structure FrontFieldsPlain (p : PortArmsC r) (b : BesideArmsC r) (ε : ℕ → ℝ≥0∞) : Prop where
  /-- the four parts, the request, the parser's budget, the way out's price -/
  parts : FrontParts p
  /-- the three arms' bounds over a drawn function, the inner extractor's form and "no coin" -/
  arms : CoreArmsC b
  /-- the commitment: no two keys have one code -/
  code : ZKCP.CodeIsOneToOne r.enc
  /-- the meaning: what is true of the extracted index is "the output tokens are the model's" -/
  meaning : HoleArmsC.soundFor b (systemArmsC r).IsModelOutput
  /-- the error's name -/
  error : ∀ tC tP, b.εK tC tP + (b.εE tC tP + b.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)

variable {p : PortArmsC r} {b : BesideArmsC r} {ε : ℕ → ℝ≥0∞}

/-- **The top, in the text of `Sound`.** Under the named fields: soundness of the system whose
verifier is the front verifier, over a drawn hash function, for an extractor that reads the
commitment and the committer's log alone. -/
theorem front_sound_plain (h : FrontFieldsPlain p b ε) :
    Sound (systemPortC p) fun t => ε (t + p.n) + p.δ t :=
  front_sound_text h.parts
    (verify_sound_arms_C_plain (systemArmsC r).IsModelOutput ε h.arms h.code h.meaning h.error)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.front_sound_plain
