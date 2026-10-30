-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecTabList.lean: THE MAKING OF THE COPIES' TABLES, ONE AFTER THE OTHER, WITH
THEIR LEAVES LAID LATE: the two statements of Johnson/LateWorld/SpecTables.lean for lists.
DEFINITIONS AND STATEMENTS. The proofs are in Johnson/LateWorld/TabList.lean.

This file states no goal of the release: two steps of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

Main names (namespace OnBytes.LateWorld).
  tabFR      the reduction's making of one table, as a law: (tree over fillings, seed), and the
             table of answers after it; the log of the leaves is dropped.
  tabsFR     the same for a list of families of salts, one table after the other.
  realTabs   the honest side's tables, off the encoding randomness of each and what tabsFR gives.
  Spec.tabsBodies   the honest copies' tables (tabsO, Johnson/WholeKey/Defs.lean) are the
             reduction's with the bodies put in.
  Spec.seedsBadList   from a table of answers with SeedsIn: some seed outside Gs, or SeedsIn lost,
             with probability at most (the number of tables) · δ.

Limits. The salts are letters here: nothing is said of how they are drawn.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecTables

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

/-- The reduction's making of one table, as a law. -/
def tabFR (b₀ : Bd) (s : ℕ → Bits) (T : Tb W) :
    PMF ((TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) × Tb W) :=
  ((tabF W S b₀ s).runDefer mkTab T []).map fun o => (o.1, o.2.1)

/-- One table after the other. -/
def tabsFR (b₀ : Bd) : List (ℕ → Bits) → Tb W →
    PMF (List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) × Tb W)
  | [], T => PMF.pure ([], T)
  | s :: ss, T => (tabFR W S b₀ s T).bind fun o =>
      (tabsFR b₀ ss o.2).bind fun o' => PMF.pure (o.1 :: o'.1, o'.2)

/-- The honest side's tables, off the encoding randomness of each and (tree over fillings, seed). -/
def realTabs (b₀ : Bd) (i : I) : List L.EncodingRandomness → List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) →
    List (TabK lam L Bd aT aL)
  | r :: rs, o :: os => ⟨r, realTree W b₀ (L.encodeIndex i r) o.1, o.2⟩ :: realTabs b₀ i rs os
  | _, _ => []

/-- **The honest copies' tables are the reduction's with the bodies put in.** -/
def Spec.tabsBodies : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (i : I) (ds : List (DrawCopy lam L Bd aT aL h.KL)) (T : Tb W),
    ((tabsO W S h i ds).runDefer mkTab T []).map (fun o => (o.1, o.2.1)) =
      (tabsFR W S h.b₀ (ds.map fun d => cutS (2 ^ W.depth) d.s) T).map fun o =>
        (realTabs W h.b₀ i (ds.map fun d => d.r) o.1, o.2)

/-- **Some seed outside Gs.** -/
def Spec.seedsBadList : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (b₀ : Bd) (ss : List (ℕ → Bits)) (T : Tb W),
    pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ → SeedsIn W S Gs T →
    pr (tabsFR W S b₀ ss T) {o | (∃ x ∈ o.1, ¬ Gs x.2) ∨ ¬ SeedsIn W S Gs o.2} ≤
      (ss.length : ℝ≥0∞) * δ

end OnBytes.LateWorld
