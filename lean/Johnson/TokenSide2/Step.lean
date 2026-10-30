-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Step.lean: THE TOKEN PROGRAMS ARE LAID ON THE SCHEME's OWN TERMS: a member of
SameStep (Johnson/HopSide/Spec.lean), at the identity in the place of its map on keys. An assembly.

Lemmas of one step of a proof. This file states no goal of the release. The token programs are a
device of that step and stand in no statement on the scheme.

  sameStep   from Spec.sameTab, Spec.sameRun (Johnson/TokenSide/SpecSame.lean), Spec.lateCommit
             (Johnson/TokenSide2/Late.lean), which are hypotheses here (the form without them is
             sameStepT, Johnson/TokenSide2/Closed.lean), and the premises TokFit
             (Johnson/TokenSide2/Sess.lean):
               setup    same_commit (Johnson/TokenSide2/Setup.lean), and the scheme's committer
                        against the program with late draws;
               keyIn    same_commit's property of all outputs;
               sess     same_sess (Johnson/TokenSide2/Sess.lean);
               cutFree  the map is the identity: the scheme hands on its salts cut behind the tree,
                        so the key that it keeps is what is read off the token side's key.

-/
import Johnson.TokenSide2.Setup
import Johnson.HopSide.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.HopSide

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec} {h : HonestSide lam L Bd aT aL}
  {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB}

/-- **The token programs are laid on the scheme's own terms.** -/
theorem sameStep (hT : Spec.sameTab) (hR : Spec.sameRun) (hL : Spec.lateCommit)
    (hf : TokFit W h tl) : SameStep W S cA r₀ h tl id where
  setup := fun i σ hd s => by
    rw [((same_commit hT hR hf i).congr (hL W S cA h i)).run σ hd s, PMF.map_comp]
    rfl
  keyIn := fun i => (same_commit hT hR hf i).post.mono fun _ hy t ht a ha => ((hy t ht).2.1 a ha).1
  sess := fun k vs hk x σ hd s => by
    have e := (same_sess (cA := cA) (r₀ := r₀) hR hf k vs hk x).run σ hd s
    rw [OComp.interp_bind] at e
    exact e.symm
  cutFree := fun _ _ => rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.sameStep
