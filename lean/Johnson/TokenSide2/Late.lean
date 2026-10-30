-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Late.lean: THE COMMITTER OF THE SCHEME WITH THE WHOLE KEY PUBLISHED
(Johnson/WholeKey/Defs.lean), WRITTEN WITH EACH SECRET COIN DRAWN JUST BEFORE THE PART THAT READS
IT. DEFINITIONS, and one statement under a name. No proof here: the statement is proved in
Johnson/TokenSide2/LateProof.lean.

Definitions of one step of a proof. This file states no goal of the release, and the scheme is not
defined by these programs.

The scheme's committer draws all its coins first (coinsC) and then runs a program without coins
(commitAt). The token side (Johnson/TokenSide/Whole.lean) draws a secret string where it is first
used. Between the two stands the program of this file: an ordinary oracle algorithm made of the
scheme's own terms, from the scheme's own lists of coins, in which
  the coins that both sides draw from lists at the start (a table's encoding randomness, the
  strategies' coins) are drawn at the start, in the token side's order (coinsCS);
  a table's salts are drawn just before the table is built (tabL);
  the coins of a compiled run are drawn just before the run (testL, linkL).

  Spec.lateCommit   the scheme's committer and this program have the same run, under every rule for
                    answering queries (Eqv, Johnson/TokenSide2/Same.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide2.Same
import Johnson.TokenSide.Whole

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-- One table: its salts, then the scheme's builder. -/
def tabL (i : I) (r : L.EncodingRandomness) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (TabK lam L Bd aT aL) :=
  .sample h.sl.n fun b => tabO W S h.b₀ i r (cutS (2 ^ W.depth) (h.sl.e b))

/-- The copies' tables. -/
def tabsL (i : I) : List (DrawCopyD L h.KL) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (TabK lam L Bd aT aL))
  | [] => .pure []
  | d :: ds => (tabL W S h i d.r).bind fun t => (tabsL i ds).bind fun ts => .pure (t :: ts)

/-- The proof on the first table: the coins of its compiled run, the run, what is handed out. -/
def testL (i : I) (t₁ : TabK lam L Bd aT aL) (κ : h.KT) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Option (OneProtocolProof lam (batTC L aT))) :=
  .sample h.coT.n fun e =>
    (proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT κ) (h.coT.e e)) h.capT t₁.tree.root
      (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r) (h.st.T i t₁.r t₁.seed κ)).bind fun a =>
    .pure (shown (h.st.stopT i t₁.r t₁.seed) a)

/-- One copy's entry in the key's list: the coins of the link's compiled run, then the scheme's own
term. Of the coins of a copy that term reads the strategy's and the run's alone. -/
def linkL (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (κ : h.KL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) :=
  .sample h.coL.n fun e => linkO W cA h i t₁ t₂ ⟨t₂.r, fun _ => [], κ, h.coL.e e⟩

/-- The entries of the key's list. -/
def linksL (i : I) (t₁ : TabK lam L Bd aT aL) :
    List (DrawCopyD L h.KL × TabK lam L Bd aT aL) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))))
  | [] => .pure []
  | a :: l => (linkL W cA h i t₁ a.2 a.1.κ).bind fun e =>
      (linksL i t₁ l).bind fun es => .pure (e :: es)

/-- The committer behind the coins that are drawn at the start. -/
def commitAtL (i : I) (d : DrawCD L h.KT h.KL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × Isk lam L Bd aT aL) :=
  (tabL W S h i d.r).bind fun t₁ =>
    (tabsL W S h i d.copies).bind fun ts =>
    (testL W cA h i t₁ d.κ).bind fun a =>
    (linksL W cA h i t₁ (d.copies.zip ts)).bind fun ls =>
    .pure (⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, a, ls⟩, ⟨i, ts⟩)

/-- The coins of one copy that are drawn at the start. -/
def coinsCopyS : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (DrawCopyD L h.KL) :=
  .sample h.ri.n fun a => .sample h.kL.n fun c => .pure ⟨h.ri.e a, h.kL.e c⟩

def coinsCopiesS : ℕ → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (DrawCopyD L h.KL))
  | 0 => .pure []
  | n + 1 => (coinsCopyS W h).bind fun d => (coinsCopiesS n).bind fun ds => .pure (d :: ds)

/-- The coins that are drawn at the start. -/
def coinsCS : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (DrawCD L h.KT h.KL) :=
  .sample h.ri.n fun a => .sample h.kT.n fun c =>
    (coinsCopiesS W h (h.M + 1)).bind fun ds => .pure ⟨h.ri.e a, h.kT.e c, ds⟩

/-- **The committer with each secret coin drawn just before the part that reads it.** -/
def commitL (i : I) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × Isk lam L Bd aT aL) :=
  (coinsCS W h).bind fun d => commitAtL W S cA h i d

/-- **The scheme's committer has the run of that program.** -/
def Spec.lateCommit : Prop :=
  ∀ {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL) (i : I),
    Eqv (commitW W S cA h i) (commitL W S cA h i)

end OnBytes.TokenSide
