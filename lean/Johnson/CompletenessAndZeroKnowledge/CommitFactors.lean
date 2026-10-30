-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/CommitFactors.lean: THE COMMITTER OF argW READS A FAILED TRY THROUGH ITS FIRST BLOCK ALONE
(FactorsBy), under PassFits: the key's run and each link are compiled runs, as the prover's session
is (factors_proveW, Johnson/WholeKey/CompleteOneHash.lean); tables ask one-block oracles; the seeds'
answers are asked whole. With factors_proveW this is the premise of the third exit at the scheme.
Nothing here is a goal.
-/
import Johnson.WholeKey.CompleteOneHash

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL) {hK : 0 < W.K}
  {pass : Pass lam (typedOracleCarrier L Bd aT aL)}

theorem factors_tabO (H : PassFits W S hK pass) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    (tabO W S b₀ i r s).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind (factors_committerTreeKeptByProver b₀ hK pass _ _) fun _ =>
    OComp.FactorsBy.bind (factors_seedsO H _) fun _ => trivial

theorem factors_tabsO (H : PassFits W S hK pass) (i : I) :
    ∀ ds : List (DrawCopy lam L Bd aT aL h.KL), (tabsO W S h i ds).FactorsBy (agP hK pass)
  | [] => trivial
  | d :: ds => OComp.FactorsBy.bind (factors_tabO H h.b₀ i d.r _) fun _ =>
      OComp.FactorsBy.bind (factors_tabsO H i ds) fun _ => trivial

theorem factors_linkO (H : PassFits W S hK pass) (i : I) (t₁ t₂ : TabK lam L Bd aT aL)
    (d : DrawCopy lam L Bd aT aL h.KL) :
    (linkO W cA h i t₁ t₂ d).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind (factors_proveX hK pass Tag.link (batLC L aL) (wLC W) W.embL id _ _ _ _ _ _ _
    _ H.testsL) fun _ => trivial

theorem factors_linksO (H : PassFits W S hK pass) (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (linksO W cA h i t₁ l).FactorsBy (agP hK pass)
  | [] => trivial
  | a :: l => OComp.FactorsBy.bind (factors_linkO cA h H i t₁ a.2 a.1) fun _ =>
      OComp.FactorsBy.bind (factors_linksO H i t₁ l) fun _ => trivial

/-- **The committer behind its coins factors.** -/
theorem factors_commitAt (H : PassFits W S hK pass) (i : I)
    (d : DrawC lam L Bd aT aL h.KT h.KL) :
    (commitAt W S cA h i d).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind (factors_tabO H h.b₀ i d.r _) fun t₁ =>
    OComp.FactorsBy.bind (factors_tabsO h H i d.copies) fun _ =>
    OComp.FactorsBy.bind (factors_proveX hK pass Tag.test (batTC L aT) (wTC W) W.embT id _ _ _ _ _ _
      _ _ H.testsT) fun _ =>
    OComp.FactorsBy.bind (factors_linksO cA h H i t₁ _) fun _ => trivial

theorem factors_coinsCopy : (coinsCopy W h).FactorsBy (agP hK pass) := fun _ _ _ _ => trivial

theorem factors_coinsCopies : ∀ n : ℕ, (coinsCopies W h n).FactorsBy (agP hK pass)
  | 0 => trivial
  | n + 1 => OComp.FactorsBy.bind (factors_coinsCopy h) fun _ =>
      OComp.FactorsBy.bind (factors_coinsCopies n) fun _ => trivial

theorem factors_coinsC : (coinsC W h).FactorsBy (agP hK pass) := fun _ _ _ _ =>
  OComp.FactorsBy.bind (factors_coinsCopies h _) fun _ => trivial

/-- **The committer factors.** -/
theorem factors_commitW (H : PassFits W S hK pass) (i : I) :
    (commitW W S cA h i).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind (factors_coinsC h) fun d => factors_commitAt cA h H i d

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.factors_commitAt
#print axioms OnBytes.WholeKey.factors_commitW
