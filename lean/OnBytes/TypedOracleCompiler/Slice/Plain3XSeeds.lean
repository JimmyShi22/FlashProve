-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3XSeeds.lean: the judge of OnBytes/TypedOracleCompiler/Slice/Plain3XJudge.lean with the
sibling's seeds' protocol as the interface's Test: the second lane's laws are no hypothesis any
more: they come from two: the drawing round's verifier's messages are exactly uniform under the
wiring, and ONE PROBABILITY over these uniform messages.

`seedsT C (dSeed e) E` (OnBytes/TypedOracleCompiler/Slice/SeedsT.lean, SeedsTData.lean) has a silent first round and
one written round of the kind "seeds", with no item, no tree, no opening and no proof of work; it
reads nothing and decides nothing. Its chain is run at one fixed string: no salt, the default
request root, no roots, the rounds' fixed plain parts. The value is `sOf` of what the round draws,
as the format's record of draws (`drawnT`); `sOf` is a parameter.
 - `TS`, `wTS`: that protocol and its wiring at the stretches' kit, with the external string's wire
   `we1`;
 - `seedOfS sOf`: the value from the verifier's messages;
 - `x3_judge_seeds`: `JudgeAtAsk` for `judgeOff` at `preSeed`, with the language: Lg x holds of the
   string read, and `badS` is false of that string and x.2.

Asked by `x3_judge_seeds`: for each instance x the protocol `Plain3 G (dec x)` is round-by-round
sound for Lg x, with one list of counts ε, each at most εs; no tree is deeper than 63; the wiring of
the three stretches is lawful; the drawing round's verifier's messages are exactly uniform under
`chal`; AND: for every string y and every first message, the probability over a uniform verifier's
message c of the drawing round that `badS y` is true of the value drawn is at most εs.

Main definitions: `TS`, `wTS`, `seedOfS`.
Main theorem: `x3_judge_seeds`.

Not claimed. NO SOUNDNESS IS PROVED, AND NO PROBABILITY: both are hypotheses. That the drawing
round's messages are exactly uniform is a hypothesis too; it fails where a field element is sampled,
and can hold where the messages are hash blocks. The probability is over the round's verifier's
messages as the wiring makes them from hash blocks, not over seeds: a count of seeds does not give
it without the draw's bias. One εs stands above both lanes' errors: where the second is the greater
the whole linear term is paid at it; and where `JudgeAtAsk` is used the whole count is multiplied by
3 (1 + the seeds' protocol's two rounds), in both terms. That the judge ever says yes is not shown.
No `sOf`, `badS`, decision, language or stretches are given: nothing speaks of a record, of a key
file, or of the program. How the seeds' protocol's first query is spelled as a string of bytes:
OnBytes/TypedOracleCompiler/Run/FirstName.lean; the second: nowhere. No part is made. What the heads of
Plain3XJudge.lean, JudgeOff.lean and SeedsT.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is
the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3XJudge
import OnBytes.TypedOracleCompiler.Slice.SeedsTData

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {A Sd : Type} [DecidableEq Sd] (G : Stretches)
  (dec : A × Sd → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones) (salt : ℕ) (d : Sd)
  (e : _root_.Fmt.Entry) (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)

/-- The seeds' protocol at the stretches' kit, on the stored table's string. -/
abbrev TS : InteractiveOracleProof Unit (oneExternalString (2 ^ G.a) PQ.SgX) := seedsT G.C (dSeed e) (oneExternalString (2 ^ G.a) PQ.SgX)

/-- Its wiring, with the external string's wire. -/
abbrev wTS : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (TS G e)) :=
  wqT G.C K chal (dSeed e) (we1 G.a)

omit [DecidableEq Sd] in
/-- The value from the verifier's messages: `sOf` of what the drawing round draws. -/
def seedOfS (sOf : List _root_.Fmt.Drawn → Sd) (ρ : Rho (TS G e).shape) : Sd :=
  sOf (drawnT G.C (dSeed e) (oneExternalString (2 ^ G.a) PQ.SgX) ρ)

/-- From soundness instance by instance, exactly uniform verifier's messages in the drawing round,
and one probability over them, to the analysis' conclusion on the judge, for traces that ask
first. What is asked: see the file's head. -/
theorem x3_judge_seeds (sOf : List _root_.Fmt.Drawn → Sd) (sMT sFS : ℕ)
    (R : Reading (Strings.strung (LX3 G dec (earlyWith d) (TS G e))) embE)
    (Lg : A × Sd → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop)
    (badS : (Fin (2 ^ G.a) → PQ.SgX) → Sd → Bool) (ε : Err G.sh) (εs : ℝ≥0∞)
    (hS : ∀ x, (Plain3 G (dec x)).Sound (fun _ => Lg x) ε) (hb : Err.Below ε εs)
    (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG)
    (hc : (unif (Fin K → Dig 256)).map (chal (dSeed e).entry (dSeed e).kind) =
      unif (G.C.Ch (dSeed e).entry (dSeed e).kind))
    (hpr : ∀ (y : Fin (2 ^ G.a) → PQ.SgX) c0,
      pr (unif (PQ.roundS G.C (dSeed e)).up.Chal)
        {c | badS y (seedOfS G e sOf (c0, c, ())) = true} ≤ εs) :
    JudgeAtAsk
      (WXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
        (prjST G.C e _))
      (judgeOff
        (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        (testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        [] default [] (plainsT G.C (dSeed e) _) (seedOfS G e sOf) sMT sFS R Lg badS) εs
      (preSeed
        (testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        [] default [] (plainsT G.C (dSeed e) _)
        (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))) := by
  obtain ⟨h1, h2⟩ := countOK_of_pr (PQ.s0 G.C).up (PQ.roundS G.C (dSeed e)).up
    (fun (y : Fin (2 ^ G.a) → PQ.SgX) ρ => badS y (seedOfS G e sOf ρ)) εs hpr
  exact x3_judgeAtAsk G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
    (prjST G.C e _) [] default [] (plainsT G.C (dSeed e) _) (seedOfS G e sOf) sMT sFS R Lg badS ε
    _ εs hS hb hs hw (seedsT_ne G.C (dSeed e) _)
    (lane_stBad_ok (TS G e)
      (wqT_okg G.C K chal (dSeed e) (we1 G.a) hc (Nat.zero_le _) (we1_ok G.a)).sh h1) h2

end TypedOracleCompiler.Slice
