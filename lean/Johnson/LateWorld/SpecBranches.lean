-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecBranches.lean: THE SESSION LEMMA (Spec.session,
Johnson/LateWorld/SpecSession.lean) AT THE LETTERS OF THE KEY's TEST AND OF A LINK. DEFINITIONS AND
STATEMENTS. The proofs are in Johnson/LateWorld/Branches.lean.

This file states no goal of the release: two steps of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

Each says: a run of the real game, then the reduction's second pass, is the honest compiled run laid
late. The reduction keeps a table's tree with fillings for bodies; the game keeps the table's
(encoding randomness, seed); the honest side's tree is the reduction's with the bodies of the
encoded index put in (realTree, Johnson/LateWorld/SpecTables.lean). The same at the session's
letters is sess_branch (Johnson/LateWorld/Steps.lean), which is the pattern.

Main names (namespace OnBytes.LateWorld).
  coVT, coVL   the coins that the reduction's second pass is handed: with the public starts that the
               view's plain parts give; as they were drawn, if there is no view.
  Spec.testBranch, Spec.linkBranch   THE STATEMENTS.

Limits. One run each.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecSession
import Johnson.LateWorld.SpecWrap
import Johnson.LateWorld.SpecTables

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The coins of the second pass of the key's test. -/
def coVT (a : AtRecs lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Option (Plains L.offline.shape) → Coins lam (typedOracleCarrier L Bd aT aL)
  | some pl => a.side.dressT (a.side.pvT pl) co
  | none => co

/-- The coins of the second pass of a link. -/
def coVL (a : AtRecs lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Option (Plains L.link.shape) → Coins lam (typedOracleCarrier L Bd aT aL)
  | some pl => a.side.dressL (a.side.pvL pl) co
  | none => co

/-- **The key's test**, on the table that the reduction keeps as t and whose (randomness, seed) the
game keeps as (r, sd); e: the table's number in the game. -/
def Spec.testBranch : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (i : I),
    PremLate W S cA a ok Gs δ → ok i →
    ∀ (e : ℕ) (t : TabW lam L Bd aT aL) (r : L.EncodingRandomness) (sd : L.OutOfDomainSeed)
      (co : Coins lam (typedOracleCarrier L Bd aT aL)), co.path.length = W.depthReqT → ∀ T : Tb W,
      ((Hiop.Seeded.runAt ((recsG a).T e) ((kitW W r₀ a.side).μT e (L.recOf i r sd))
          (kitW W r₀ a.side).ρT (i, r, sd) (L.recOf i r sd)).bind fun v =>
        pass2 Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
          (cmsTA cA t.tree.root (L.recOf i r sd).2) (L.recOf i r sd) (fun _ => t.tree) a.side.capT
          W.embE v.2 (coVT a co (v.2.map DView.plains)) v.1.2 T) =
        (unif a.Hs.T.Coin).bind fun κ =>
          lateTA W cA (fun _ => realTree W a.b₀ (L.encodeIndex i r) t.tree)
            (a.side.dressT (a.side.rvT κ) co) a.side.capT t.tree.root (L.recOf i r sd) (L.encodeIndex i r)
            (a.side.st.stopT i r sd) (a.side.st.T i r sd κ) T

/-- **A link**, from the first table (t₁; u₁ its (randomness, seed)) to a copy's (t₂; u₂); e: the
copy's table's number in the game. -/
def Spec.linkBranch : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (i : I),
    PremLate W S cA a ok Gs δ → ok i →
    ∀ (e : ℕ) (t₁ t₂ : TabW lam L Bd aT aL) (u₁ u₂ : L.EncodingRandomness × L.OutOfDomainSeed)
      (co : Coins lam (typedOracleCarrier L Bd aT aL)), co.path.length = W.depthReqL → ∀ T : Tb W,
      ((Hiop.Seeded.runAt ((recsG a).Lk e)
          ((kitW W r₀ a.side).μL e (L.recOf i u₁.1 u₁.2, L.recOf i u₂.1 u₂.2))
          (kitW W r₀ a.side).ρL (i, u₁, u₂) (L.recOf i u₁.1 u₁.2, L.recOf i u₂.1 u₂.2)).bind
        fun v =>
        pass2 Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
          (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i u₁.1 u₁.2).2 (L.recOf i u₂.1 u₂.2).2)
          (L.recOf i u₁.1 u₁.2, L.recOf i u₂.1 u₂.2) (fun k => if k = 0 then t₁.tree else t₂.tree)
          a.side.capL W.embE v.2 (coVL a co (v.2.map DView.plains)) v.1.2 T) =
        (unif a.Hs.Lk.Coin).bind fun κ =>
          lateLA W cA
            (fun k => if k = 0 then realTree W a.b₀ (L.encodeIndex i u₁.1) t₁.tree
              else realTree W a.b₀ (L.encodeIndex i u₂.1) t₂.tree)
            (a.side.dressL (a.side.rvL κ) co) a.side.capL t₁.tree.root t₂.tree.root
            (L.recOf i u₁.1 u₁.2) (L.recOf i u₂.1 u₂.2) (L.encodeIndex i u₁.1, L.encodeIndex i u₂.1)
            (a.side.st.stopL i u₁ u₂) (a.side.st.Lk i u₁ u₂ κ) T

end OnBytes.LateWorld
