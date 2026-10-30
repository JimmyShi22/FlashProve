-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean: a judge for a written batch protocol whose instances have a part
that stands in no query: it recomputes that part by a second protocol's chain, compares, and then
runs the compiled verifier; and the analysis' conclusion on it, for traces that ask first.

OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean leaves two things open: a hypothesis on the trace
(`SeedFirst`) and a way out ("the value read off the trace is not the instance's").
OnBytes/TypedOracleCompiler/Slice/SeedFirstAsk.lean draws the first from `AsksFirst`. This judge shuts the second:
its run holds the second protocol's chain at the fixed string, so outside the named set, where each
query has one answer, the value read off the trace is the value that the run computed, and the run
goes on only if that is the instance's. From the same chain OnBytes/TypedOracleCompiler/Slice/SeedLane.lean gives
that the value is not bad for the string read.
 - `judgeOffRun`: the second protocol's chain at the fixed string under the output's root; a no if
   it refuses or if `seedOf` of its verifier's messages is not the instance's second part; else the
   compiled verifier with the strict format;
 - `judgeOff`: that run as a judge (`Judge`, OnBytes/TypedOracleCompiler/Slice/OneWorldJ.lean); its language: Lg
   holds of the instance and the string, AND `badS` is false of the string and the instance's second
   part;
 - `judgeAtAsk_off`: `JudgeAtAsk` (OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean) for that judge at `preSeed`,
   under conditions (below);
 - `preSeed_blind`: every reading reads the same off a trace and off the trace lengthened by what
   `preSeed` asks: a part's field `blind` (with `preSeed_noCoin` and `preSeed_queries` of
   SeedFirstAsk.lean: the three fields on `pre` of `Part.OKAsk`, OnBytes/TypedOracleCompiler/Slice/PartAsk.lean).

Asked by `judgeAtAsk_off`: every count of ε and of εT is at most εs; the state function has the laws
`StLawsOwn` for Lg and obeys the law on verifier's messages; `Z.OK`; as many slots as the request
tree at Z's tag has leaves; the first query holds (x.1, d) of an instance x and no later query holds
the instance; the two tags differ; the second protocol has a round and what it writes of a plain
part is read back; THE LANE WHOSE STATE IS "badS y (seedOf ρ)" OBEYS THE LAWS OF A LANE, at as many
slots as the request tree at the second protocol's tag has leaves: its wiring is lawful, and
at every string y, whatever the earlier verifier's messages, at most εT's last count of values of
the last one make badS y (seedOf ρ) true. The count is over the second protocol's verifier's
messages, through `seedOf`: not over Sd.

Main definitions: `judgeOffRun`, `judgeOff`.
Main theorems: `judgeAtAsk_off`, `preSeed_blind`.

Not claimed. NO SOUNDNESS IS PROVED: the laws of the state function and of the second lane are
hypotheses. No second protocol, no `seedOf`, no `badS` and no fixed string are given: nothing speaks
of a record, of a key file, or of the program. No part is made: a checker, a page and their laws are
not here; a checker on bytes has to return, as the instance's second part, the very value that the
second protocol's typed chain yields. THAT THE JUDGE EVER SAYS YES is not shown: at a fixed string
with too few roots for the second protocol's trees it refuses everything. That the hypotheses are
met together by a language other than "true" and a `badS` other than "false" is shown by nothing.
THE PRICE is not in this statement: where `JudgeAtAsk` is used (`one_worldJ_ask`,
OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean) the whole count, the judge's own tV among it, is multiplied by 1
+ the number of the second protocol's rounds, in both terms; and εs is one number above both lanes'
counts. The form has "there is a set": it is for use in one world (see `JudgeAt`). What the heads of
the four files named do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.SeedFirstAsk
import OnBytes.TypedOracleCompiler.Slice.OneWorldAsk
import OnBytes.TypedOracleCompiler.Slice.BatchJudge
import OnBytes.TypedOracleCompiler.Slice.ReadingBlind

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (AsksFirst lenB)
open scoped ENNReal

variable {I A Sd : Type} [DecidableEq Sd] {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L}
  (Z : WrittenB W) (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
  (plainsT : Plains ZT.P.shape) (seedOf : Rho ZT.P.shape → Sd) (sMT sFS : ℕ)

/-- The judge's run: the second protocol's chain at the fixed string under the root; a no if it
refuses, or if the value that it yields is not the instance's second part; else the compiled
verifier with the strict format. -/
def judgeOffRun (o : BatchOut Z) : TypedOracleComputation lam W.K L Bool :=
  (ZT.chainT saltT rtT rootsT plainsT [o.1]).bind fun z =>
    match z with
    | some y =>
        if seedOf y.1 = o.2.1.2 then Z.verifierS sMT sFS o.1 o.2.1 o.2.2 else OComp.pure false
    | none => OComp.pure false

/-- It tosses no coin and asks at most as many queries as the second protocol has rounds and the
compiled verifier asks. -/
theorem detBound_judgeOffRun (o : BatchOut Z) :
    DetBound (judgeOffRun Z ZT saltT rtT rootsT plainsT seedOf sMT sFS o)
      (ZT.P.shape.length + tVQB Z.wq (W.dReq Z.t)) := by
  refine DetBound.bind (chainB_lo ZT.t [o.1] none saltT rtT ZT.P.shape (RoundSplits.allLocal ZT.P.shape)
    ZT.wq.sh ZT.embP 0 .first rootsT plainsT (allLoA_allLocal _)).1 fun z => ?_
  cases z with
  | none => exact detBound_pure _ _
  | some y =>
    show DetBound (if seedOf y.1 = o.2.1.2 then Z.verifierS sMT sFS o.1 o.2.1 o.2.2
      else OComp.pure false) _
    split
    · exact detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _
    · exact detBound_pure _ _

variable (R : Reading L W.embE) (Lg : A × Sd → (oneExternalString L.wordLength L.Symbol).Str → Prop)
  (badS : (Fin L.wordLength → L.Symbol) → Sd → Bool)

/-- That run as a judge. Its language: Lg holds of the instance and the string, and `badS` is
false of the string and the instance's second part. -/
def judgeOff : Judge W (BatchOut Z) where
  run := judgeOffRun Z ZT saltT rtT rootsT plainsT seedOf sMT sFS
  tV := ZT.P.shape.length + tVQB Z.wq (W.dReq Z.t)
  bound := detBound_judgeOffRun Z ZT saltT rtT rootsT plainsT seedOf sMT sFS
  roots := fun o => [o.1]
  R := R
  Lang := fun o ys => ∀ y, ys = [y] → Lg o.2.1 y ∧ badS y o.2.1.2 = false
  ok := fun o => ∀ p op, o.2.2.ext p = some op → R.keeps p op.sym op.salt

/-- The analysis' conclusion on that judge, for traces that ask first at `preSeed`. What is
asked: see the file's head. -/
theorem judgeAtAsk_off (d : Sd) (ε : Err Z.Q.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → A × Sd → PTr Z.Q.loc.shape → Bool) (εT : Err ZT.P.shape)
    (εs : ℝ≥0∞) (hb : Err.Below ε εs) (hJ : Joint Z ε State) (hS : StLawsOwn Z State Lg)
    (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) {NT : ℕ} (hNT : NT = 2 ^ (W.dReq ZT.t))
    (hE : ∀ x, L.early x = (x.1, d))
    (hl : L.late = none) (hne : ZT.t ≠ Z.t) (hneT : ZT.P.shape ≠ [])
    (hP : ∀ z, ZT.prjP (ZT.embP z) = some z)
    (oT : (ZT.laneBad R εT fun y ρ => badS y (seedOf ρ)).OK NT) (bT : Err.Below εT εs) :
    JudgeAtAsk W (judgeOff Z ZT saltT rtT rootsT plainsT seedOf sMT sFS R Lg badS) εs
      (preSeed ZT saltT rtT rootsT plainsT Z) := by
  refine ⟨batBadOff Z R (ZT.extSW saltT rtT rootsT plainsT seedOf d) d ε State
      (ZT.laneBad R εT fun y ρ => badS y (seedOf ρ)),
    fun β Alg t hA => batBadOff_rare Z R _ d ε State _ εs hb hJ hZ hN hNT hne.symm oT bT β Alg t hA,
    batBadOff_mono Z R _ d ε State _, fun F tr o hB hA _ hok hrun y hy => ?_,
    fun tr tr' cm hB hann => batBadOff_stable Z R _ d ε State _ tr tr' cm hB hann⟩
  have e : [R.at W tr o.1] = [y] := hy
  rw [← (List.cons.inj e).1]
  obtain ⟨z, hz, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  cases z with
  | none => cases runsIn_pure_iff.1 h2
  | some y0 =>
    obtain ⟨ρ, rts, ph⟩ := y0
    have h3 : RunsIn tr (if seedOf ρ = o.2.1.2 then Z.verifierS sMT sFS o.1 o.2.1 o.2.2
        else OComp.pure false) true := h2
    by_cases hs : seedOf ρ = o.2.1.2
    · rw [if_pos hs] at h3
      obtain ⟨P1, P2, h4⟩ := runsIn_verifyB_of_strict hZ.wire h3
      have h1 : OneAns tr := (batBadOff_second Z R _ d ε State _ tr hB).2
      have he : ZT.extSW saltT rtT rootsT plainsT seedOf d tr [o.1] = seedOf ρ :=
        extSOf_run ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT
          seedOf d h1 [o.1] hz
      refine ⟨(batBadOff_lang_ask ZT saltT rtT rootsT plainsT seedOf d Z R ε State _ Lg hS hZ hE hl
        hne F tr o.1 o.2.1 (o.2.2.withPaths P1 P2) hB hA (keeps_withPaths R o.2.2 P1 P2 hok)
        h4).resolve_left fun h => h (he.trans hs), ?_⟩
      rw [← hs]
      exact batBadOff_bad_false Z R _ d ε State ZT εT (fun y ρ => badS y (seedOf ρ)) hneT hP tr o.1
        hB saltT rtT rootsT plainsT hz
    · rw [if_neg hs] at h3
      cases runsIn_pure_iff.1 h3

omit [DecidableEq Sd] in
/-- Every reading is blind to what `preSeed` asks: it asks at a challenge oracle alone, and a
reading sees leaves and vertices alone. In the form of the field `blind` of `Part.OKAsk`
(OnBytes/TypedOracleCompiler/Slice/PartAsk.lean). -/
theorem preSeed_blind (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W) (cm : Dig lam) :
    R.at W (lenB (preSeed ZT saltT rtT rootsT plainsT Z) F tr) cm = R.at W tr cm :=
  R.at_lenB W _ F (fun o q x hx => by
    obtain ⟨xo, xq, xr⟩ := x
    have h : xo = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t :=
      preSeed_tag ZT saltT rtT rootsT plainsT Z F o q _ hx
    subst h
    rfl) tr cm

end TypedOracleCompiler.Slice
