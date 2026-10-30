-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecSetupW.lean: THE REDUCTION's SETUP AGAINST THE REAL GAME, WHERE THE GAME
SERVES: the calls for the copies' tables, and the links. DEFINITIONS AND STATEMENTS. The proofs
are in Johnson/LateWorld/SetupGame.lean.

This file states no goal of the release: steps of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean). The game's reply and the run of one of the reduction's programs
against the game are repG and runG (Johnson/LateWorld/Steps.lean).

Main names (namespace OnBytes.LateWorld).
  tabOf        the reduction's table, off its tree and the game's reply.
  gameTabs     the calls "a table at this seed" for a list of (tree, seed), one after the other: the
               reduction's tables, if none was refused; the game's state.
  push, stAfter   the game's host's state with one more table; after a list of tables.
  mkTs         the reduction's tables, off the encoding randomness of each and (tree, seed).
  drawU        uniform encoding randomness for n tables.
  linksUsed    the game's counts after the links on the tables number e, .., e + n - 1.
  Spec.gameTabsGood   all seeds in Gs and room for the tables: the game draws each table's
               randomness uniformly and refuses none.
  Spec.stAfterKeeps, Spec.stAfterCopies, Spec.stAfterOod   what the host's state says afterwards:
               the earlier tables are kept; the honest side's copies read off it (realCopies,
               Johnson/LateWorld/Steps.lean) are realTabs (Johnson/LateWorld/SpecTabList.lean); the
               reduction's out-of-domain samples are the index's.
  Spec.linksW  the links against the game are the honest links laid late (linksM,
               Johnson/LateWorld/SpecSetup.lean), and the game's state but for its counts is kept.

Limits. Nothing is said where the game refuses: a seed outside Gs, or no room for a table.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Steps
import Johnson.LateWorld.SpecSetup

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The reduction's table, off its tree and the game's reply. -/
def tabOf {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} (r₀ : L.Rec) {h : HonestSide lam L Bd aT aL}
    (tr : TreeK lam (typedOracleCarrier L Bd aT aL)) :
    Hiop.Seeded.GIn L (kitW W r₀ h).form → Option (TabW lam L Bd aT aL)
  | .ood rc => some ⟨tr, rc⟩
  | _ => none

/-- The game's host's state with one more table, at (randomness, seed) u. -/
def push (st : StH L) (u : L.EncodingRandomness × L.OutOfDomainSeed) : StH L :=
  (st.1 + 1, Function.update st.2 (st.1 + 1) u)

/-- The host's state after a list of tables. -/
def stAfter (st : StH L) :
    List L.EncodingRandomness → List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) → StH L
  | r :: rs, o :: os => stAfter (push st (r, o.2)) rs os
  | _, _ => st

/-- The reduction's tables, off the encoding randomness of each and (tree, seed). -/
def mkTs (i : I) : List L.EncodingRandomness → List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) →
    List (TabW lam L Bd aT aL)
  | r :: rs, o :: os => ⟨o.1, L.recOf i r o.2⟩ :: mkTs i rs os
  | _, _ => []

/-- Uniform encoding randomness for n tables. -/
def drawU (L : HolographicProtocol I X) : ℕ → PMF (List L.EncodingRandomness)
  | 0 => PMF.pure []
  | n + 1 => (unif L.EncodingRandomness).bind fun r => (drawU L n).bind fun rs => PMF.pure (r :: rs)

/-- The game's counts after the links on the tables number e, .., e + n - 1. -/
def linksUsed (u : Hiop.UsedR) : ℕ → ℕ → Hiop.UsedR
  | _, 0 => u
  | e, n + 1 => linksUsed { u with links := Hiop.bump u.links e } (e + 1) n

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop)
  (s1 : ℕ) (i : I)

/-- The calls for a list of tables, one after the other. -/
def gameTabs : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) → StGm W →
    PMF (Option (List (TabW lam L Bd aT aL)) × StGm W)
  | [], g => PMF.pure (some [], g)
  | o :: os, g => (repG W r₀ a Gs s1 i g (.table o.2)).bind fun p =>
      (gameTabs os p.2).map fun q =>
        ((tabOf r₀ o.1 p.1).bind fun t => q.1.map fun ts => t :: ts, q.2)

/-- **Where all seeds lie in Gs and there is room, the game refuses no table.** -/
def Spec.gameTabsGood : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (r₀ : L.Rec)
    (a : AtRecs lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop) (s1 : ℕ) (i : I)
    (os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)) (c : ℕ) (u : Hiop.UsedR) (st : StH L)
    (Tg : Tb W),
    (∀ x ∈ os, Gs x.2) → c + os.length ≤ a.M + 1 →
    gameTabs W r₀ a Gs s1 i os (some (c, u, st), Tg) =
      (drawU L os.length).map fun rs =>
        (some (mkTs i rs os), (some (c + os.length, u, stAfter st rs os), Tg))

/-- The earlier tables are kept. -/
def Spec.stAfterKeeps : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (rs : List L.EncodingRandomness)
    (os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)) (st : StH L) (e : ℕ),
    e ≤ st.1 → (stAfter st rs os).2 e = st.2 e

/-- The honest side's copies, read off the reduction's tables and the host's state. -/
def Spec.stAfterCopies : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (a : AtRecs lam L Bd aT aL)
    (i : I) (rs : List L.EncodingRandomness) (os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)) (st : StH L),
    realCopies W a i (stAfter st rs os).2 (st.1 + 1) (mkTs i rs os) = realTabs W a.b₀ i rs os

/-- The reduction's out-of-domain samples are the index's at the host's (randomness, seed). -/
def Spec.stAfterOod : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (i : I) (rs : List L.EncodingRandomness)
    (os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)) (st : StH L) (e : ℕ)
    (t : TabW lam L Bd aT aL),
    (mkTs i rs os)[e]? = some t →
    t.ood =
      L.recOf i ((stAfter st rs os).2 (st.1 + 1 + e)).1 ((stAfter st rs os).2 (st.1 + 1 + e)).2

/-- **The links against the game are the honest links laid late.** t₁: the first table as the
reduction keeps it; l: the copies' coins and tables; e: the number of the first of these tables. -/
def Spec.linksW : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (s1 : ℕ) (i : I),
    PremLate W S cA a ok Gs δ → ok i →
    ∀ (t₁ : TabW lam L Bd aT aL) (c : ℕ) (st : StH L) (Tg : Tb W)
      (l : List (DrawCopy lam L Bd aT aL a.side.KL × TabW lam L Bd aT aL)) (e : ℕ)
      (u : Hiop.UsedR) (T : Tb W),
      1 ≤ e → e + l.length ≤ c + 1 → (∀ k, k < l.length → u.links (e + k) = 0) →
      t₁.ood = L.recOf i (st.2 0).1 (st.2 0).2 →
      (∀ k x, l[k]? = some x →
        x.2.ood = L.recOf i (st.2 (e + k)).1 (st.2 (e + k)).2 ∧
          x.1.co.path.length = W.depthReqL) →
      runG W r₀ a Gs s1 i (linksA W cA r₀ a.side t₁ e l T) (some (c, u, st), Tg) =
        (linksM W cA a.side i
          ⟨(st.2 0).1, realTree W a.b₀ (L.encodeIndex i (st.2 0).1) t₁.tree, (st.2 0).2⟩
          ((l.map fun x => x.1.co).zip (realCopies W a i st.2 e (l.map fun x => x.2))) T).map
          fun o => (o, (some (c, linksUsed u e l.length, st), Tg))

end OnBytes.LateWorld
