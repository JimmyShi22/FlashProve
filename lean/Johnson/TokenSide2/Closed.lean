-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Closed.lean: THE TOKEN PROGRAMS ARE LAID ON THE SCHEME's OWN TERMS, WITH NO
HYPOTHESIS LEFT but the premises on the letters. An assembly: each part is proved in another file.

Lemmas of one step of a proof. This file states no goal of the release. The token programs are a
device of that step and stand in no statement on the scheme.

  sameStepT      SameStep (Johnson/HopSide/Spec.lean) at all letters that fit (TokFit,
                 Johnson/TokenSide2/Sess.lean): one table (Johnson/TokenSide2/SameTab.lean), one
                 compiled run (Johnson/TokenSide/TieRun.lean) and the committer with late draws
                 (Johnson/TokenSide2/LateProof.lean) laid into Johnson/TokenSide2/Step.lean.
  sameStep_prem  the same at the letters of the statement of index privacy: the honest side
                 a.side, the token side's letters tokAt (Johnson/TokenSide2/AtPrem.lean), under the
                 statement's own premises (PremW, Johnson/WholeKey/Premises.lean), of which the laws
                 on the coins and the wires' laws are used.

Limits. What is shown: as ordinary oracle algorithms, with the names of the later tries of a search
written back, the token side's committer and its prover of one shown request have the runs of the
scheme's committer and prover, under every rule for answering queries. Nothing is said here on the
mode in which marked evaluations are deferred.

-/
import Johnson.TokenSide2.Step
import Johnson.TokenSide2.AtPrem
import Johnson.TokenSide2.SameTab
import Johnson.TokenSide2.LateProof
import Johnson.TokenSide.TieRun

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.HopSide

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The token programs are laid on the scheme's own terms**, at all letters that fit. -/
theorem sameStepT {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) {h : HonestSide lam L Bd aT aL}
    {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB} (hf : TokFit W h tl) :
    SameStep W S cA r₀ h tl id :=
  sameStep sameTab sameRun lateCommit hf

/-- The same at the letters of the statement of index privacy, under its own premises. -/
theorem sameStep_prem {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} (r₀ : L.Rec) {p : Params} {a : AtRecs lam L Bd aT aL}
    {Sm : Sims L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {c : CoinNums Bd}
    {N : NumsW} (hP : PremW W S cA p a Sm ok Gs Ryes c N) :
    SameStep W S cA r₀ a.side (tokAt W p a c) id :=
  sameStepT S cA r₀ (tokFit_tokAt hP.coins hP.wires)

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.sameStepT
#print axioms OnBytes.TokenSide.sameStep_prem
