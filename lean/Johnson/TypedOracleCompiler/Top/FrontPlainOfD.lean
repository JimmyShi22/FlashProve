-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/FrontPlainOfD.lean: THE FRONT VERIFIER's SOUNDNESS IN `Sound`'s OWN TEXT
(`Sound`, VerifiableInference/Statements.lean: the extractor reads the commitment and the
committer's log alone) FROM THE ARMS' BOUNDS IN THE SHAPE IN WHICH THEY ARE MEANT TO BE HAD: with
the public reading drawn in the experiment (`CoreArmsCD`, Johnson/Top/OnFilesArmsCD.lean).

IT HAS THE SHAPE OF AN UNCONDITIONAL STATEMENT, NOT ITS STRENGTH: its weight stands in the named
fields of one structure, and most of them are open.

Why. Johnson/Top/FrontParts.lean has `FrontFields` (parts, arms : `CoreArmsCD`, commitment, meaning,
error) for the game whose extractor may query. FrontPlain.lean has `FrontFieldsPlain` for the plain
game, with arms : `CoreArmsC` at another "beside": so a field paid for the one top did not count for
the other. ArmsPlainOfD.lean passes from `CoreArmsCD` to `CoreArmsC` under two named hypotheses.
Here the plain top is stated over THE SAME parts and arms as `FrontFields`, and the same meaning at
the system's own claim (there spelled at `systemPortC p`, here at `systemArmsC r`: one thing by
unfolding). In the place of its field `commitment` stand three: `code`, `word`, `tests`; and its
field `error` is another: it names the three arms' errors and (t + 2)² / 2^256.

One structure; statements and proofs. Nothing new is proved: each proof is an application.


Main names (namespace `VerifiableInference.OnPublicFiles`):
  `FrontFieldsD p b' part wordC ε`: ALL NAMED HYPOTHESES: `parts` (`FrontParts p`); `arms`
    (`CoreArmsCD b'`); `word` ((W): the word under a root hangs on what the public reading gives
    through its part in the key alone); `tests` ((T): each arm tests the key's c against the
    reading); `code` (the top's step "the commitment": no two keys have one code); `meaning`;
    `error`.
  `FrontFieldsD.plain`: they give `FrontFieldsPlain p (besidePlain b' wordC) ε`.
  `front_sound_D`: THE TOP: `Sound (systemPortC p)` at the error ε (t + n) + δ t.

Limits.
  * EVERY FIELD IS A HYPOTHESIS; a conditional theorem holds for nothing where a field is false.
    None is paid here.
  * `tests`: THE ARMS MUST TEST c AGAINST THE HASH FUNCTION's OWN DIGEST OF THE PUBLIC FILES, SINCE
    THE PROVER NAMES c. Shown of no arm in this library. IT IS FREE AT A READING THAT RETURNS THE
    KEY's OWN c: `arms` is then as hard as the plain bounds, and nothing is gained (the limits of
    ArmsPlainOfD.lean): the field has content only where `b'.rd` asks the hash function at public
    strings that are fixed before it is drawn.
  * `code` SPEAKS OF THE STRING THAT `r.enc` WRITES. It is false at a code that leaves a part of the
    key out, as a commitment ID's string without the record's seed does; it is meant at the string
    that holds the seed (OnBytes/Tie/IdKeySeed.lean), with c read off the same string.
  * AT A FRONT VERIFIER THAT KEEPS A HAND-WRITTEN COMPARISON OF THE ID, `r.enc` MUST WRITE THE
    STRING THAT THAT TEXT HASHES: ELSE THE TWO TESTS AGREE ONLY AT A COLLISION OF THE HASH FUNCTION,
    AND THE VERIFIER ALL BUT NEVER SAYS YES.
  * `arms` IS READ AT ONE WORD, `b'.wordOf`, FOR ALL THREE ARMS. `word` can be a theorem only where
    that word is read through a written family of codings; the key file's and the proof file's
    bounds must then be proved against THAT word: their own codings must write every leaf query and
    every node query as that family does. Until they are, `arms` has no payer at these two arms.
  * NO FIELD ASKS THAT THE FRONT VERIFIER EVER SAYS YES (the limits of FrontPlain.lean).
  * r, p, b', part, wordC and ε are letters: no written input, parser, way out, reading or number is
    given.
  * All limits of the heads of FrontPlain.lean, ArmsPlainOfD.lean, OnFilesArmsCPlain.lean,
    Johnson/Top/FrontParts.lean and Johnson/Top/OnFilesArmsCD.lean stand. Soundness alone. For
    proofs only; no program imports this file.
-/
import Johnson.TypedOracleCompiler.Top.FrontPlain
import Johnson.TypedOracleCompiler.Top.ArmsPlainOfD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC}

/-- ALL NAMED HYPOTHESES of the top in the plain notion, with the arms' bounds in the shape with the
public reading drawn in the experiment. -/
structure FrontFieldsD (p : PortArmsC r) (b' : BesideArmsCD r) (part : b'.D → r.C)
    (wordC : r.C → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol) (ε : ℕ → ℝ≥0∞) :
    Prop where
  /-- the four parts, the request, the parser's budget, the way out's price -/
  parts : FrontParts p
  /-- the three arms' bounds over a drawn function, the public reading and "no coin" -/
  arms : CoreArmsCD b'
  /-- the word under a root hangs on what the reading gives through its part in the key alone -/
  word : WordReadsPart b' part wordC
  /-- each arm tests the key's c against what the reading gives -/
  tests : ArmsTestC b' part
  /-- the commitment: no two keys have one code -/
  code : ZKCP.CodeIsOneToOne r.enc
  /-- the meaning: what is true of the extracted index is "the output tokens are the model's" -/
  meaning : HoleArmsCD.soundFor b' (systemArmsC r).IsModelOutput
  /-- the error's name -/
  error : ∀ tC tP, b'.εK tC tP + (b'.εE tC tP + b'.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)

variable {p : PortArmsC r} {b' : BesideArmsCD r} {part : b'.D → r.C}
  {wordC : r.C → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol} {ε : ℕ → ℝ≥0∞}

/-- They give the named hypotheses of FrontPlain.lean, at the "beside" whose extractor is written.
-/
theorem FrontFieldsD.plain (h : FrontFieldsD p b' part wordC ε) :
    FrontFieldsPlain p (besidePlain b' wordC) ε :=
  ⟨h.parts, coreArmsC_of_CD h.arms h.word h.tests, h.code, soundFor_besidePlain h.meaning, h.error⟩

/-- **The top, in the text of `Sound`, from the arms' bounds with the public reading drawn in the
experiment.** -/
theorem front_sound_D (h : FrontFieldsD p b' part wordC ε) :
    Sound (systemPortC p) fun t => ε (t + p.n) + p.δ t :=
  front_sound_plain h.plain

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.FrontFieldsD.plain
#print axioms VerifiableInference.OnPublicFiles.front_sound_D
