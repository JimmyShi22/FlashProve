-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecTables.lean: THE MAKING OF ONE TABLE WITH ITS LEAVES LAID LATE: two
statements. DEFINITIONS AND STATEMENTS. The proofs are in Johnson/LateWorld/Tables.lean.

This file states no goal of the release: two steps of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

The honest committer builds a table's tree over the encoded index (tabO,
Johnson/WholeKey/Defs.lean); the reduction builds it over fillings, with the same salts, and learns
the out-of-domain sample from the game afterwards (tableA, Johnson/WholeKey/Wrap.lean). Where the
leaves get fresh answers without a look at the table (OComp.runDefer at mkTab,
Johnson/WholeKey/Sim.lean), the digests do not hang on what the leaves hold.

  Spec.tabBodies   the honest table is the reduction's with the bodies put in: the same law of
      (tree's levels and salts, seed, table of answers after it).
  Spec.seedsBad    from a table of answers in which every entry at a seed's second query gives a
      seed in Gs, the making of one table gives a seed outside Gs, or leaves a table of answers
      without that property, with probability at most δ.

Main names (namespace OnBytes.LateWorld).
  tabF       the reduction's program for one table: the tree over fillings, the seed's two queries.
  realTree   a kept tree with the bodies of the word y put in, the salts and levels kept.
  SeedsIn    every entry at a seed's second query gives a seed in Gs (seedsIn_empty: the empty table
             of answers has the property).

Limits. One table.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Sim
import Johnson.Prover.CommitterTreeKeptByProver

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The reduction's program for one table: the tree over fillings with the salts s, then the seed's
two queries at its root. -/
def tabF (b₀ : Bd) (s : ℕ → Bits) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) :=
  (treeO W.depth fun j => (⟨b₀, s j⟩ : LeafIn (typedOracleCarrier L Bd aT aL))).bind fun tr =>
    (seedsO W S tr.root).bind fun e => .pure (tr, e)

/-- A kept tree with the bodies of the word y put in: the committer's own leaves (committerLeafInput) at the
tree's salts; the levels stay. -/
def realTree (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (T : TreeK lam (typedOracleCarrier L Bd aT aL)) :
    TreeK lam (typedOracleCarrier L Bd aT aL) :=
  { T with inp := committerLeafInput W b₀ y fun j => (T.inp j).salt }

/-- Every entry of the table of answers at a seed's second query gives a seed in Gs. -/
def SeedsIn (Gs : L.OutOfDomainSeed → Prop) (T : Tb W) : Prop :=
  ∀ (v : Bits) (a : TypedOracleCompiler.Compile.Batch.FsAns lam W.K),
    T (TypedOracleCompiler.Compile.Batch.OracleName.fb S.t) (seedQ1 W S v) = some a → Gs (S.seed a.1)

/-- The empty table of answers has the property. -/
theorem seedsIn_empty (Gs : L.OutOfDomainSeed → Prop) : SeedsIn W S Gs (Table.empty _) :=
  fun _ _ h => by cases h

/-- **The honest table is the reduction's with the bodies put in.** -/
def Spec.tabBodies : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) (T : Tb W),
    ((tabO W S b₀ i r s).runDefer mkTab T []).map (fun o => (o.1, o.2.1)) =
      ((tabF W S b₀ s).runDefer mkTab T []).map fun o =>
        ((⟨r, realTree W b₀ (L.encodeIndex i r) o.1.1, o.1.2⟩ : TabK lam L Bd aT aL), o.2.1)

/-- **A seed outside Gs.** -/
def Spec.seedsBad : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (b₀ : Bd) (s : ℕ → Bits) (T : Tb W),
    pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ → SeedsIn W S Gs T →
    pr ((tabF W S b₀ s).runDefer mkTab T []) {o | ¬ Gs o.1.2 ∨ ¬ SeedsIn W S Gs o.2.1} ≤ δ

end OnBytes.LateWorld
