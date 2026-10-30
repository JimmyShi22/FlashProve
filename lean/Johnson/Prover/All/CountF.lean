-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/CountF.lean: the runs of a whole request (allY, Johnson/Prover/All/Defs.lean) by
the first-block exit (Rom/OverOneF.lean): the letters for saying that they factor, and how many hash
calls they cost.

Main names.
  allF       the number, in HASH CALLS: two whole trees (two calls a leaf), the two seeds' four
             queries (each a whole answer: W.K + 1 calls), the three chains by chainF
             (Johnson/Prover/Law/CountF.lean). allN's text (Johnson/Prover/All/Count.lean) with
             W.K + 1 for each seed query and chainF for chainN: allN counts TYPED QUERIES, allF HASH
             CALLS.
  PassFits   a premise's record: at the wiring W and the record's wire S the one letter pass is the
             three wire records' tests (TestsAt, at embP := id), and the seeds' two queries are
             asked whole.
  asksIn_seedsO, factors_seedsO, costBound_seedsO, factors_committerTreeKeptByProver, costBound_committerTreeKeptByProver   the parts.
  factors_allY, factors_allX     THE RUNS FACTOR by agP (OnBytes/Prover/FirstBlock.lean).
  costBound_allY, costBound_allX   THEIR HASH CALLS: the weighted bound (OComp.CostBoundR,
             Rom/OverOneF.lean) at allF.

Limits. PassFits IS A PREMISE: nothing says here that a wiring has such a pass. An upper bound on
every path, with chainF's looseness. allF hangs on the draw through the three paths' lengths alone.
The committer's count is not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Count
import Johnson.Prover.Law.CountF

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The number, in hash calls: two trees, two seeds, three chains. -/
def allF (capT capL capB : ℕ → ℕ) (d : Draw lam L Bd aT aL Kap) : ℕ :=
  2 * 2 ^ W.depth + (2 * (W.K + 1) + (2 * 2 ^ W.depth + (2 * (W.K + 1) +
    (chainF L.offline.shape aT (wTC W).sh capT 0 d.coT.path.length +
      (chainF L.link.shape aL (wLC W).sh capL 0 d.coL.path.length +
        (chainF L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 d.coB.path.length + 0))))))

/-- The one letter pass fits the wiring and the record's wire. -/
structure PassFits (hK : 0 < W.K) (pass : Pass lam (typedOracleCarrier L Bd aT aL)) : Prop where
  testsT : TestsAt hK pass Tag.test 0 L.offline.shape aT (wTC W).sh id
  testsL : TestsAt hK pass Tag.link 0 L.link.shape aL (wLC W).sh id
  testsB : TestsAt hK pass Tag.onl 0 L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh id
  seed0 : ∀ cm, AskedWhole pass (TypedOracleCompiler.Compile.Batch.OracleName.fb S.t) (seedQ0 W S cm)
  seed1 : ∀ v, AskedWhole pass (TypedOracleCompiler.Compile.Batch.OracleName.fb S.t) (seedQ1 W S v)

variable {W S}
variable (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ) {hK : 0 < W.K} {pass : Pass lam (typedOracleCarrier L Bd aT aL)}

/-! ## The parts -/

theorem asksIn_seedsO (H : PassFits W S hK pass) (cm : Dig lam) :
    (seedsO W S cm).AsksIn (AskedWhole pass) :=
  ⟨H.seed0 cm, fun _ => ⟨H.seed1 _, fun _ => trivial⟩⟩

theorem factors_seedsO (H : PassFits W S hK pass) (cm : Dig lam) :
    (seedsO W S cm).FactorsBy (agP hK pass) :=
  factors_of_whole hK pass _ (asksIn_seedsO H cm)

/-- The seed's two queries: two whole answers. -/
theorem costBound_seedsO (H : PassFits W S hK pass) (cm : Dig lam) :
    (seedsO W S cm).CostBoundR (costP hK pass) (2 * (W.K + 1)) := fun a0 =>
  ⟨W.K + 1, by
    show 2 * (W.K + 1) = (if pass S.t (seedQ0 W S cm) (a0.1 ⟨0, hK⟩) = true then W.K + 1 else 1) +
      (W.K + 1)
    rw [if_pos (H.seed0 cm _)]
    omega, fun a1 => ⟨0, by
    show W.K + 1 = (if pass S.t (seedQ1 W S _) (a1.1 ⟨0, hK⟩) = true then W.K + 1 else 1) + 0
    rw [if_pos (H.seed1 _ _)], trivial⟩⟩

theorem factors_committerTreeKeptByProver (hK : 0 < W.K) (pass : Pass lam (typedOracleCarrier L Bd aT aL))
    (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) : (committerTreeKeptByProver W b₀ y salt).FactorsBy (agP hK pass) :=
  factors_of_whole hK pass _ (asksIn_treeO (small_whole pass) _ _)

theorem costBound_committerTreeKeptByProver (hK : 0 < W.K) (pass : Pass lam (typedOracleCarrier L Bd aT aL))
    (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeKeptByProver W b₀ y salt).CostBoundR (costP hK pass) (2 * 2 ^ W.depth) :=
  cost_of_small hK pass (queryBound_committerTreeKeptByProver W b₀ y salt) (asksIn_treeO (small_cost hK pass) _ _)

/-! ## The runs of a whole request -/

/-- **They factor.** -/
theorem factors_allY (H : PassFits W S hK pass) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) :
    (allY W S cA r₀ b₀ st capT capL capB isk x d).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind (factors_committerTreeKeptByProver b₀ hK pass _ _) fun _ =>
  OComp.FactorsBy.bind (factors_seedsO H _) fun _ =>
  OComp.FactorsBy.bind (factors_committerTreeKeptByProver b₀ hK pass _ _) fun _ =>
  OComp.FactorsBy.bind (factors_seedsO H _) fun _ =>
  OComp.FactorsBy.bind (factors_proveX hK pass Tag.test (batTC L aT) (wTC W) W.embT id _ _ _ _ _ _
    _ _ H.testsT) fun _ =>
  OComp.FactorsBy.bind (factors_proveX hK pass Tag.link (batLC L aL) (wLC W) W.embL id _ _ _ _ _ _
    _ _ H.testsL) fun _ =>
  OComp.FactorsBy.bind (factors_proveX hK pass Tag.onl L.onlineBatch (wBC W) W.embB id _ _ _ _ _ _ _ _
    H.testsB) fun _ => trivial

theorem factors_allX (H : PassFits W S hK pass) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind (factors_allY cA r₀ b₀ st capT capL capB H isk x d) fun _ => trivial

/-- **Their hash calls.** -/
theorem costBound_allY (H : PassFits W S hK pass) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) :
    (allY W S cA r₀ b₀ st capT capL capB isk x d).CostBoundR (costP hK pass)
      (allF W capT capL capB d) :=
  OComp.CostBoundR.bind (fun _ =>
  OComp.CostBoundR.bind (fun _ =>
  OComp.CostBoundR.bind (fun _ =>
  OComp.CostBoundR.bind (fun _ =>
  OComp.CostBoundR.bind (fun _ =>
  OComp.CostBoundR.bind (fun _ =>
  OComp.CostBoundR.bind (by intro _; trivial)
    (costBound_proveX hK pass Tag.onl L.onlineBatch (wBC W) W.embB id _ _ _ _ _ _ _ _ H.testsB))
    (costBound_proveX hK pass Tag.link (batLC L aL) (wLC W) W.embL id _ _ _ _ _ _ _ _ H.testsL))
    (costBound_proveX hK pass Tag.test (batTC L aT) (wTC W) W.embT id _ _ _ _ _ _ _ _ H.testsT))
    (costBound_seedsO H _)) (costBound_committerTreeKeptByProver b₀ hK pass _ _)) (costBound_seedsO H _))
    (costBound_committerTreeKeptByProver b₀ hK pass _ _)

theorem costBound_allX (H : PassFits W S hK pass) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).CostBoundR (costP hK pass)
      (allF W capT capL capB d) :=
  (OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
    (costBound_allY cA r₀ b₀ st capT capL capB H isk x d)).mono (by omega)

end OnBytes.Prover

#print axioms OnBytes.Prover.asksIn_seedsO
#print axioms OnBytes.Prover.factors_seedsO
#print axioms OnBytes.Prover.costBound_seedsO
#print axioms OnBytes.Prover.factors_committerTreeKeptByProver
#print axioms OnBytes.Prover.costBound_committerTreeKeptByProver
#print axioms OnBytes.Prover.factors_allY
#print axioms OnBytes.Prover.factors_allX
#print axioms OnBytes.Prover.costBound_allY
#print axioms OnBytes.Prover.costBound_allX
