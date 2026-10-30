-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedMain.lean: the compiled scheme whose proving key is (i, seed) has the three
properties (`IsZKCPArgWith`, ZKCP/Gen.lean) of the scheme that it is made from, with added error
terms. (not all hypotheses are named here: see `Spec.seedMainB`) (Words of this library:
lean/GLOSSARY.md.)

The statement is `Spec.seedMainB` of Compile/Batch/SeedStar.lean, whose header says for which
schemes and under which hypotheses it holds, and what it does not say.

  `seedMainB`   Under these hypotheses: the same extractor and simulator; completeness error α + b;
                the same ε; ζ(t, N) + b + t / (number of seeds). b bounds the bias, along a path of
                the committer C, of the samples made from small ones; t bounds the adversary's
                queries to all oracles.
  `pathBiasB_argOf`   The function `key` that is applied to the output of C changes no bias.

The statement is for every wire record W: no law of a wire record (`W.OK`, `W.OKG`) is asked of it,
so it holds where rounds have proof-of-work bits (the search over nonces takes no sample:
Compile/Batch/SeedShape.lean; sanity lemmas: Compile/Batch/SeedGhost.lean).

Notation: α, ε, ζ: arguments of `IsZKCPArgWith` (ZKCP/Gen.lean): α stands in its field
`completeness`, ε in `indexBinding`, ζ in `indexPrivacy`; `F`: a `Face W IVK' Pf'`: what a scheme
over the committer of Compile/Batch/Star.lean is made of, beside that committer
(Compile/Batch/SeedStar.lean); `bk`: a `CoinPlan`: how a uniform sample is made from small ones
(Rom/Blocks.lean); `σ`: a `SeedOracle`: an auxiliary oracle, used as a source of coins; `pt s j` is
the query for the seed s and the counter j (Rom/SpecDerive.lean); `c.pathBiasB bk`: the supremum,
over the paths of the algorithm, of the sum along the path of the biases of its samples
(Rom/Blocks.lean); `W`: a `QueryLayout lam L`, the wire record (Iop/BatchWire.lean).
-/
import Compile.Batch.SeedReplay

noncomputable section

open Rom Iop ZKCP
open scoped ENNReal

namespace Compile.Batch
namespace Seed

/-- a function applied to the result changes no bias -/
theorem pathBiasB_map {S : OSpec} {α β : Type} (bk : CoinPlan) (G : α → β) (c : OComp S α) :
    (c.bind fun a => .pure (G a)).pathBiasB bk = c.pathBiasB bk := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    simp only [Rom.OComp.bind, OComp.pathBiasB]
    exact congrArg _ (funext ih)
  | sample n k ih =>
    simp only [Rom.OComp.bind, OComp.pathBiasB]
    exact congrArg _ (congrArg _ (funext ih))

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} (WP : WireBP L) (p : Params)
  {IVK' Pf' : Type} (F : Face W IVK' Pf')

theorem pathBiasB_argOf (bk : CoinPlan) (i : I) :
    ((argOf WP p F).C i).pathBiasB bk = (C W WP p i).pathBiasB bk :=
  pathBiasB_map bk (fun o : IVK lam L × ISK lam L => (F.key o.1 o.2.1, o.2)) (C W WP p i)

end Seed

open Seed

/-- The proof of `Spec.seedMainB` (Compile/Batch/SeedStar.lean). -/
theorem seedMainB : Spec.seedMainB := by
  intro I X PP lam L W WP p IVK' Pf' F bk σ R B E Sim α b ε ζ hσ hw hb hT hN h
  have hb' : ∀ i, ((argOf WP p F).C i).pathBiasB bk ≤ b := fun i =>
    (pathBiasB_argOf WP p F bk i).le.trans (hb i)
  have h1 : Gen.IsZKCPArgWith R (argBk WP p F bk) B E Sim (α + b) ε (fun t N => ζ t N + b) :=
    replaceC (C' := Cb WP p F bk)
      (fun i => (OComp.tv_blocks_le bk ((argOf WP p F).C i) _).trans (hb' i)) h
  have h2 := deriveWith (b := 0) (hσ ▸ argAvoidsBk WP p F bk hN)
    (fun i => (OComp.pathBias_blocks σ bk hw ((argOf WP p F).C i)).le) (replays WP p F bk hσ hT) h1
  simpa only [add_zero] using h2

end Compile.Batch
