-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Closed.lean: THE TOKEN PROGRAMS OF THE SCHEME WITH THE WHOLE KEY PUBLISHED KEEP
THE RULES OF DEFERRED PROGRAMMING AND STAY WITHIN THE WRITTEN COUNTS: Spec.safeTwin and
Spec.countTwin (Johnson/TokenRules/Spec.lean) WITH NO NAMED STATEMENT LEFT AS A HYPOTHESIS. The
premises that stand INSIDE these statements stay (see withinZetaT below). An assembly: each part is
proved in another file.

General lemmas. This file states no goal of the release.

  safeTwinT      Spec.safeTwin: the chain (Johnson/TokenRel/Rules.lean) laid into
                 Johnson/TokenRules/Scheme.lean.
  countTwinT     Spec.countTwin: the step of the challenger and the zeros of the counts
                 (Johnson/TokenRules/Zero.lean) laid into Johnson/TokenRules/Count.lean.
  withinZetaT    Spec.withinZeta (Johnson/TokenRules/Bridge.lean): the same at the counts that stand
                 in the written error of the statement of index privacy
                 (Johnson/WholeKey/Zeta.lean). ITS PREMISES, which stay: the rules' letters do not
                 pass the lengths of the tokens (LensOK at the free bits of a leaf's salt and at the
                 shorter of a first salt and a digest); the three numbers of sibling digests of the
                 token side are the wire's three depths of request trees; the adversary asks for one
                 setup and then for at most n batches (GAdm). At the letters of the statement the
                 first four are met (lensOK_tokAt, Johnson/TokenSide2/AtPrem.lean; the depths by
                 definition of tokAt). THE PROOF OF INDEX PRIVACY CALLS THIS ONE.
  within_largest The form in which deferred programming (Rom.Spec.defer, Rom/Defer.lean) takes it,
                 at the largest letters that the programs' lengths allow (blOf, bfOf): there the
                 premise on the letters is met at all lengths, so nothing is asked but that the
                 adversary asks for one setup and then for at most n batches.
The proof of index privacy calls neither safeTwinT nor within_largest.

Limits. What is shown is on the token programs, which are a device of one step of a proof of index
privacy. That they are the scheme's own programs written a second time is not shown here (it is the
subject of Johnson/TokenSide2/Closed.lean). No number is evaluated: whether the counts make a small
error is not said.

-/
import Johnson.TokenRel.Rules
import Johnson.TokenRules.Scheme
import Johnson.TokenRules.Count
import Johnson.TokenRules.Zero
import Johnson.TokenRules.Bridge

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

/-- **The token programs keep the rules.** -/
theorem safeTwinT : Spec.safeTwin := safeTwin safeChain

/-- **The counts of the token programs.** -/
theorem countTwinT : Spec.countTwin := countTwin (safeStep safeChain) zeroOutside

/-- **Every run against the challenger stays within the counts of the written error**, under the
premises of Spec.withinZeta: LensOK, the three depths, GAdm. -/
theorem withinZetaT : Spec.withinZeta := withinZeta_of countTwinT.2.2

/-- **Every run against the challenger stays within the counts**, at the largest letters. -/
theorem within_largest {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (i : I) (m : Bool) {α : Type}
    (ok : ZKCP.Gen.Batch X Unit → Prop)
    (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (_root_.Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ)
    (hA : GAdm ok A false n) :
    ∀ x ∈ (interact ((challT W S cA r₀ h tl i).world m) A (none, DSt.init _)).support,
      x.2.2.Within (eAllT W S h n) (mAllT W h tl n) (bitsOfT lam (blOf tl) (bfOf tl)) (osAllT h) :=
  countTwinT.2.2 I X lam L Bd aT aL W S cA r₀ h tl (blOf tl) (bfOf tl) i m α ok A n (lensOK_of tl)
    hA

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.countTwinT
#print axioms OnBytes.TokenRules.withinZetaT
