-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecSetupA.lean: THE REDUCTION's SETUP (setupA, Johnson/WholeKey/Wrap.lean)
AGAINST THE REAL GAME IN A NORMAL FORM: first all that does not hang on the game (phase1,
Johnson/LateWorld/SpecSetup.lean: the committer's coins, all trees over fillings, all seeds), then
the calls to the game and what follows them. DEFINITIONS AND ONE STATEMENT. Its proof is in
Johnson/LateWorld/SetupNormal.lean.

This file states no goal of the release: one step of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

Why it holds. The making of a table is hash work on the reduction's own table of answers, then one
call "a table at this seed". The hash work of the later tables reads nothing of the replies to the
earlier calls, and the game's replies read nothing of the reduction's table of answers: so all hash
work can be written first.

Main names (namespace OnBytes.LateWorld).
  restA        the setup behind the tables: the text of setupA's last part.
  setupA_eq    setupA is: the coins, the first table, the copies' tables, restA.
  contW        the calls for all tables, then restA, against the game.
  Spec.setupNormal   setupA against the game = phase1, then contW.

Limits. An unfolding and a change of order alone: nothing is said of what the game replies.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecSetupW

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- The setup behind the tables. d: the committer's coins; T: the table of answers; then the first
table and the copies' tables as the reduction keeps them, if the game has refused none. -/
def restA (h : HonestSide lam L Bd aT aL) (d : DrawC lam L Bd aT aL h.KT h.KL) (T : Tb W) :
    Option (TabW lam L Bd aT aL) → Option (List (TabW lam L Bd aT aL)) →
    AdvG W r₀ h (GIn (FullKey lam L aT aL) (RequestProof lam L) × StG W)
  | some t₁, some ts =>
      .call (.test 0) fun rp =>
        (match rp with
          | .test u =>
              pass2A Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
                (cmsTA cA t₁.tree.root t₁.ood.2) t₁.ood (fun _ => t₁.tree) h.capT W.embE u.2
                (match u.2 with
                  | some d' => h.dressT (h.pvT d'.plains) d.co
                  | none => d.co) u.1.2 T
          | _ => .halt (none, T)).bind fun o₃ =>
        (linksA W cA r₀ h t₁ 1 (d.copies.zip ts) o₃.2).bind fun o₄ =>
          .halt (.inl ⟨t₁.tree.root, t₁.ood, o₃.1, o₄.1⟩, (o₄.2, some ts))
  | _, _ => .halt (.inl ⟨default, r₀, none, []⟩, (T, none))

theorem setupA_eq (h : HonestSide lam L Bd aT aL) (T : Tb W) :
    setupA W S cA r₀ h T =
      ((coinsC W h).runLazyA T).bind fun o₀ =>
      (tableA W S r₀ h (cutS (2 ^ W.depth) o₀.1.s) o₀.2).bind fun o₁ =>
      (tablesA W S r₀ h (o₀.1.copies.map fun d => cutS (2 ^ W.depth) d.s) o₁.2).bind fun o₂ =>
      restA W cA r₀ h o₀.1 o₂.2 o₁.1 o₂.1 := rfl

variable (a : AtRecs lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop) (s1 : ℕ) (i : I)

/-- The calls for all tables, then the rest of the setup, against the game from the state g. -/
def contW (ω : Om W a.side) (g : StGm W) :
    PMF ((GIn (FullKey lam L aT aL) (RequestProof lam L) × StG W) × StGm W) :=
  (repG W r₀ a Gs s1 i g (.table ω.o₁.2)).bind fun p₁ =>
  (gameTabs W r₀ a Gs s1 i ω.os p₁.2).bind fun q =>
  runG W r₀ a Gs s1 i (restA W cA r₀ a.side ω.d ω.T (tabOf r₀ ω.o₁.1 p₁.1) q.1) q.2

/-- **The reduction's setup against the game in its normal form.** -/
def Spec.setupNormal : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop)
    (s1 : ℕ) (i : I) (T : Tb W) (g : StGm W),
    runG W r₀ a Gs s1 i (setupA W S cA r₀ a.side T) g =
      (phase1 W S a.side T).bind fun ω => contW W cA r₀ a Gs s1 i ω g

end OnBytes.LateWorld
