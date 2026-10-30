-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3XJudge.lean: the judge of OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean at the protocol in
three stretches with an instance of which one part stands in no query: FROM SOUNDNESS INSTANCE BY
INSTANCE, AND THE LAWS OF THE SECOND LANE, to the analysis' conclusion for traces that ask first.

Instances are pairs (a, s); the interface is `LX3` at `early := earlyWith d`
(OnBytes/TypedOracleCompiler/Slice/Plain3XOff.lean); its Test is a given protocol T with at least one round. The
judge runs T's chain at a fixed string under the root, compares `seedOf` of its verifier's messages
with s, and then runs the compiled verifier of `Plain3X G dec` with the strict format.
 - `testWritten`: T as a written protocol, under the tag of Test; plain parts as they are;
 - `x3_judgeAtAsk`: `JudgeAtAsk` for `judgeOff` at `preSeed`. Its language: Lg x holds of the string
   read, and `badS` is false of that string and x.2.

Asked by `x3_judgeAtAsk`: for each instance x the protocol `Plain3 G (dec x)` is round-by-round
sound for Lg x, with one list of counts ε; every count of ε and of εT is at most εs; no tree is
deeper than 63; the wiring of `Plain3X` is lawful (T's is part of the lane's laws); T has a round;
the lane whose state is "badS y (seedOf ρ)" obeys the laws of a lane at one slot (see the head of
JudgeOff.lean: a count over T's verifier's messages, not over Sd).

Main definition: `testWritten`.
Main theorem: `x3_judgeAtAsk`.

Not claimed. NO SOUNDNESS IS PROVED, and no count. No T, `seedOf`, `badS`, decision, language or
stretches are given: nothing speaks of a record, of a key file, or of the program. No part is made.
That the judge ever says yes, and that the hypotheses are met together by a language other than
"true" and a `badS` other than "false", is shown by nothing. THE PRICE is not in this statement:
where `JudgeAtAsk` is used (`one_worldJ_ask`, OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean) the whole count,
the judge's own tV among it, is multiplied by 1 + the number of the second protocol's rounds, in
both terms; and εs is one number above both lanes' counts. What the heads of JudgeOff.lean,
Plain3XOff.lean and Plain3X.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3XOff
import OnBytes.TypedOracleCompiler.Slice.JudgeOff

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (replySt below_timesShared_one)
open scoped ENNReal

variable {A Sd : Type} [DecidableEq Sd] (G : Stretches)
  (dec : A × Sd → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones) (salt : ℕ) (d : Sd)
  (T : InteractiveOracleProof Unit (oneExternalString (2 ^ G.a) PQ.SgX))
  (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)
  (wT : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → List Bool)
  (pT : (p : OPos T.shape) → List Bool → Option (OSym T.shape p))

omit [DecidableEq Sd] in
/-- The interface's Test as a written protocol: under the tag of Test; plain parts as they are. -/
def testWritten : Written (WXo G dec K chal o salt d T embE prjE wT eT pT) where
  t := Tag.test
  P := T
  wq := wT
  embS := eT
  prjS := pT
  embP := id
  prjP := some

/-- From soundness instance by instance, and the laws of the second lane, to the analysis'
conclusion on the judge, for traces that ask first. What is asked: see the file's head. -/
theorem x3_judgeAtAsk (saltT : Bits) (rtT : Dig 256) (rootsT : List (Dig 256))
    (plainsT : Plains T.shape) (seedOf : Rho T.shape → Sd) (sMT sFS : ℕ)
    (R : Reading (Strings.strung (LX3 G dec (earlyWith d) T)) embE)
    (Lg : A × Sd → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop)
    (badS : (Fin (2 ^ G.a) → PQ.SgX) → Sd → Bool) (ε : Err G.sh) (εT : Err T.shape) (εs : ℝ≥0∞)
    (hS : ∀ x, (Plain3 G (dec x)).Sound (fun _ => Lg x) ε) (hb : Err.Below ε εs)
    (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG) (hneT : T.shape ≠ [])
    (oT : ((testWritten G dec K chal o salt d T embE prjE wT eT pT).laneBad R εT
      fun y ρ => badS y (seedOf ρ)).OK 1) (bT : Err.Below εT εs) :
    JudgeAtAsk (WXo G dec K chal o salt d T embE prjE wT eT pT)
      (judgeOff (ZXo G dec K chal o salt d T embE prjE wT eT pT)
        (testWritten G dec K chal o salt d T embE prjE wT eT pT) saltT rtT rootsT plainsT seedOf sMT
        sFS R Lg badS) εs
      (preSeed (testWritten G dec K chal o salt d T embE prjE wT eT pT) saltT rtT rootsT plainsT
        (ZXo G dec K chal o salt d T embE prjE wT eT pT)) := by
  have h1 : Err.Below (Err.timesShared 1 (RoundSplits.allLocal G.sh) ε) (((1 : ℕ) : ℝ≥0∞) * εs) :=
    below_timesShared_one le_rfl _ ε εs hb
  rw [Nat.cast_one, one_mul] at h1
  exact judgeAtAsk_off (ZXo G dec K chal o salt d T embE prjE wT eT pT)
    (testWritten G dec K chal o salt d T embE prjE wT eT pT) saltT rtT rootsT plainsT seedOf sMT sFS
    R Lg badS d (Err.timesShared 1 (RoundSplits.allLocal G.sh) ε) (replySt (Plain3X G dec) ε id Lg) εT εs
    h1
    (joint_reply_id (ZXo G dec K chal o salt d T embE prjE wT eT pT) Lg ε)
    (stLawsOwn_reply (ZXo G dec K chal o salt d T embE prjE wT eT pT) Lg ε
      ((plain3X_sound_iff G dec Lg ε).2 hS))
    (ZX3_ok G dec K chal o salt (earlyWith d) T embE prjE wT eT pT hs hw) rfl rfl (fun _ => rfl) rfl
    (show Tag.test ≠ Tag.onl by decide) hneT (fun _ => rfl) oT bT

end TypedOracleCompiler.Slice
