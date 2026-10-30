-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontOnlyLaws.lean: laws on the front verifier with nothing by hand outside the parser
and the arms (Johnson/Top/FrontOnly.lean), and that verifier made of a parser's four parts
(Johnson/Top/FrontParse.lean).

At letters: it cannot be run: it says something only at a written r and a written parser, and none
is given here.

  `OnBytes.K.front_yes_only` [Johnson/Top/FrontGeneral.lean]: the converse of `front_yes` (the same
    file).
  `afterParse_accepts`: at every hash function g, what is done behind the parser decides as the
    verifier of `systemArmsC r` itself decides (`ArgumentSystem.accepts`).
  `PortArmsC.only_is`: so at every g the front verifier `p.only` says yes exactly if the verifier of
    the system that the arms' soundness theorem speaks of says yes on what the parser returns at g:
    that system's own verifier, behind a parser.
  `exceptionBound_never` [Johnson/Top/FrontGeneral.lean]: the way out that never says yes has the
    price 0.
  `frontOf prove R n`: `PortArmsC.only` at: the files' type of R, the parser `R.reader`, the budget
    n, the way out that never says yes, the price 0. An honest prover is still a letter of the
    frame's type; the front verifier does not read it.
  `frontParts_frontOf`: `FrontParts` of it from the three readings' counts of queries alone: each a
    bound at every prompt, output and files, an adversary's files too.
  `frontOf_sound`: the top at it: from these three counts, the three arms' bounds, the commitment,
    the meaning and the error's name: the error is ε (t + (nK + (nE + nP))) + 0.

Who brings what, by the types. The commitment, the prompt and the output tokens are the front
verifier's own arguments. The public files are no argument of it: they reach it through r and R
alone: "the public files come from the user's side" is true only of a function Z ↦ the front
verifier at an r and an R made of Z, which is written nowhere here. All else, the key with its
public part among it, is what the parser makes of the prover's files.

What is not claimed. All that the heads of the two files named do not claim. Nothing is won for
soundness by a definition: the debt sits in the arms' bounds, the commitment and the meaning,
hypotheses here; `FrontParts` of `frontOf` holds given the counts, also where it never says yes. The
game of `frontOf_sound` is `SoundForWithO` (an extractor that may query the hash function), not the
library's `Sound`. r, R and the honest prover are letters. That the key file's and the proof file's
arms begin with the test of the record's seed against the hash function is asked by nothing here: it
lies in the arms' bounds: an arm without it lets a prover name the seed. Where an arm is the
compiler's verifier at a flat description, the soundness of that description's protocol is a named
hypothesis inside the arm's bound, and its verifier's arithmetic is written by hand after the C++
checks. With no hand-written call beside the arms, "it accepts the files that the C++ prover makes"
and "the arm's bound is below 1" both hang on what the arm's coding spells: at a format in which the
request reaches the proof's queries through the second hash's digest alone the two cannot hold
together (an argument, not a theorem). The three counts are a real debt at a reading that hashes
as it cuts a file: its count must be bounded whatever the file holds. That it accepts any file is
not shown. It is not the program that ships: where a program runs another verifier, its exit code 0
says nothing of `frontOf` without a tie between the two at the program's hash function. For proofs
only; the program does not import this file.


-/
import Johnson.Top.FrontOnly
import Johnson.Top.FrontParse
import Johnson.Top.FrontGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC}

/-- At every hash function, what is done behind the parser decides as the verifier of
`systemArmsC r` decides. -/
theorem afterParse_accepts (g : Hash) (c : Commitment) (prompt output : List Token)
    (a : List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) :
    (afterParse r c prompt output a).evaluate g = (systemArmsC r).accepts g c prompt output a := by
  cases hy : (afterParse r c prompt output a).evaluate g with
  | true =>
    obtain ⟨x, code, hb, he, hc, vK, vE, vP⟩ := (afterParse_yes_iff g c prompt output a).1 hy
    exact (accepts_of_armsC g c prompt output a.1 a.2.1 a.2.2 x code hb he hc vK vE vP).symm
  | false =>
    cases hz : (systemArmsC r).accepts g c prompt output a with
    | false => rfl
    | true =>
      obtain ⟨x, code, hb, he, hc, hv⟩ := OnBytes.K.front_yes_only (schemeArmsC r) r.enc r.bound
        r.build r.π₀ g c prompt output a.1 a.2.1 a.2.2 hz
      exact absurd (hy.symm.trans ((afterParse_yes_iff g c prompt output a).2
        ⟨x, code, hb, he, hc, (schemeArmsC_yes_iff _ _ _ _).1 hv⟩)) Bool.false_ne_true

/-- **At every hash function the front verifier is the verifier of `systemArmsC r`, behind the
parser.** -/
theorem PortArmsC.only_is (p : PortArmsC r) (g : Hash) (c : Commitment)
    (prompt output : List Token) (F : p.Files) :
    (p.only.port c prompt output F).evaluate g =
      (systemArmsC r).accepts g c prompt output (p.parsed g prompt output F) := by
  show ((p.reader prompt output F).andThen (afterParse r c prompt output)).evaluate g = _
  rw [DeterministicAlgorithm.evaluate_andThen]
  exact afterParse_accepts g c prompt output _

variable {Files : Type}

/-- The front verifier made of a parser's four parts and the input alone. (The field `port` of the
record below is a filler: `PortArmsC.only` writes over it.) -/
def frontOf (prove : (systemArmsC r).Weights → (systemArmsC r).CommitmentRandomness →
      List Token → List Token → RandomizedAlgorithm Files) (R : ParseParts r Files) (n : ℕ) :
    PortArmsC r :=
  PortArmsC.only
    { Files := Files
      prove := prove
      port := fun _ _ _ _ => .done false
      reader := R.reader
      n := n
      exc := fun _ _ _ _ => .done false
      δ := fun _ => 0 }

variable (prove : (systemArmsC r).Weights → (systemArmsC r).CommitmentRandomness →
  List Token → List Token → RandomizedAlgorithm Files) (R : ParseParts r Files)

/-- All fields on the front verifier, from the three readings' counts of queries alone. -/
theorem frontParts_frontOf {nK nE nP : ℕ}
    (hK : ∀ prompt output F, (R.key prompt output F).QueryBound nK)
    (hE : ∀ prompt output F, (R.ent prompt output F).QueryBound nE)
    (hP : ∀ prompt output F, (R.prf prompt output F).QueryBound nP) :
    FrontParts (frontOf prove R (nK + (nE + nP))) :=
  frontParts_only _ (R.reader_budget hK hE hP) exceptionBound_never

variable {b : BesideArmsCD r}

/-- The top at it. -/
theorem frontOf_sound {claim : r.I → List Token → List Token → Prop}
    {extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)} {q : ℕ} {εO : ℕ → ℕ → ℝ≥0∞}
    {ε : ℕ → ℝ≥0∞} {nK nE nP : ℕ}
    (hK : ∀ prompt output F, (R.key prompt output F).QueryBound nK)
    (hE : ∀ prompt output F, (R.ent prompt output F).QueryBound nE)
    (hP : ∀ prompt output F, (R.prf prompt output F).QueryBound nP) (arms : CoreArmsCD b)
    (commitment : HoleArmsCD.commitmentOO b extO q εO) (meaning : HoleArmsCD.soundFor b claim)
    (error : ∀ tC tP, εO tC tP ≤ ε (tC + tP)) :
    SoundForWithO (systemPortC (frontOf prove R (nK + (nE + nP))))
      (fun c l => deterministicOf (extO.Ei c l)) q claim
      fun t => ε (t + (nK + (nE + nP))) + 0 :=
  front_sound ⟨frontParts_frontOf prove R hK hE hP, arms, commitment, meaning, error⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.afterParse_accepts
#print axioms VerifiableInference.OnPublicFiles.PortArmsC.only_is
#print axioms VerifiableInference.OnPublicFiles.frontParts_frontOf
#print axioms VerifiableInference.OnPublicFiles.frontOf_sound
