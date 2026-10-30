-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Need.lean: THE COMMITTER THAT LAYS LATE (lateCommit, Johnson/LateWorld/Defs.lean)
WITH EACH SECRET COIN DRAWN JUST BEFORE THE PART THAT READS IT. DEFINITIONS AND ONE STATEMENT.

General definitions. This file states no goal of the release. These laws are a device of one step of
a proof and stand in no statement on the scheme.

lateCommit draws all coins of the committer at the start, as the scheme does. The token programs
draw a secret coin where it is first used. Between the two stands the form of this file: the coins
that are no secrets (the encodings' randomness, the strategies' coins) at the start; a table's salts
just before the table; the coins of a compiled run just before the run. Each part is a map from a
table to a law on (what it gives, the table after it), in lateCommit's own terms.

  tabInward, tabsInward     one table, the copies' tables: the salts, then the scheme's builder with
                            its leaves deferred.
  testInward                the proof on the first table: the run's coins, then lateTA.
  linkInward, linksInward   one entry, all entries of the key's list: the run's coins, then lateLA.
  commitAtInward            the committer behind the coins that are drawn at the start.
  copiesInward, commitInward   these coins; THE COMMITTER.
  Spec.lateDraws            lateCommit is commitInward: draws that nothing in between reads can be
                            carried inward. Its proof is in Johnson/TokenSide2/LateDraws.lean.
The plain programs with one rule for all queries have the like in Johnson/TokenSide2/Late.lean
(commitL, Spec.lateCommit); here the rule changes from part to part and entries are written between
the parts, so the statement is on laws and not on programs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Defs
import Johnson.TokenSide.Whole

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.LateWorld
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-- One table: its salts, then the scheme's builder, its leaves deferred; the log is dropped. -/
def tabInward (i : I) (r : L.EncodingRandomness) (T : Tb W) : PMF (TabK lam L Bd aT aL × Tb W) :=
  (unif (Fin (h.sl.n + 1))).bind fun b =>
    ((tabO W S h.b₀ i r (cutS (2 ^ W.depth) (h.sl.e b))).runDefer mkTab T []).map fun o =>
      (o.1, o.2.1)

/-- The copies' tables. -/
def tabsInward (i : I) : List (DrawCopyD L h.KL) → Tb W → PMF (List (TabK lam L Bd aT aL) × Tb W)
  | [], T => PMF.pure ([], T)
  | d :: ds, T => (tabInward W S h i d.r T).bind fun o =>
      (tabsInward i ds o.2).bind fun o' => PMF.pure (o.1 :: o'.1, o'.2)

/-- The proof on the first table: the coins of its compiled run, then the run, laid late. -/
def testInward (i : I) (t₁ : TabK lam L Bd aT aL) (κ : h.KT) (T : Tb W) :
    PMF (Option (OneProtocolProof lam (batTC L aT)) × Tb W) :=
  (unif (Fin (h.coT.n + 1))).bind fun e =>
    lateTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT κ) (h.coT.e e)) h.capT t₁.tree.root
      (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r) (h.st.stopT i t₁.r t₁.seed)
      (h.st.T i t₁.r t₁.seed κ) T

/-- One copy's link proof: the coins of its compiled run, then the run, laid late. -/
def linkInward (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (κ : h.KL) (T : Tb W) :
    PMF (Option (OneProtocolProof lam (batLC L aL)) × Tb W) :=
  (unif (Fin (h.coL.n + 1))).bind fun e =>
    lateLA W cA (fun k => if k = 0 then t₁.tree else t₂.tree) (h.dressL (h.rvL κ) (h.coL.e e))
      h.capL t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed) (L.recOf i t₂.r t₂.seed)
      (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r) (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))
      (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) κ) T

/-- The entries of the key's list. -/
def linksInward (i : I) (t₁ : TabK lam L Bd aT aL) :
    List (DrawCopyD L h.KL × TabK lam L Bd aT aL) → Tb W →
    PMF (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) × Tb W)
  | [], T => PMF.pure ([], T)
  | a :: l, T => (linkInward W cA h i t₁ a.2 a.1.κ T).bind fun o =>
      (linksInward i t₁ l o.2).bind fun o' =>
      PMF.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o.1) :: o'.1, o'.2)

/-- The committer behind the coins that are drawn at the start. -/
def commitAtInward (i : I) (d : DrawCD L h.KT h.KL) (T : Tb W) :
    PMF ((FullKey lam L aT aL × Isk lam L Bd aT aL) × Tb W) :=
  (tabInward W S h i d.r T).bind fun o₁ =>
  (tabsInward W S h i d.copies o₁.2).bind fun o₂ =>
  (testInward W cA h i o₁.1 d.κ o₂.2).bind fun o₃ =>
  (linksInward W cA h i o₁.1 (d.copies.zip o₂.1) o₃.2).bind fun o₄ =>
  PMF.pure ((⟨o₁.1.tree.root, L.recOf i o₁.1.r o₁.1.seed, o₃.1, o₄.1⟩, ⟨i, o₂.1⟩), o₄.2)

/-- The coins of n copies that are drawn at the start. -/
def copiesInward : ℕ → PMF (List (DrawCopyD L h.KL))
  | 0 => PMF.pure []
  | n + 1 => (unif (Fin (h.ri.n + 1))).bind fun a => (unif (Fin (h.kL.n + 1))).bind fun c =>
      (copiesInward n).bind fun ds => PMF.pure (⟨h.ri.e a, h.kL.e c⟩ :: ds)

/-- **The committer that lays late, each secret coin drawn just before the part that reads it.** -/
def commitInward (i : I) (T : Tb W) : PMF ((FullKey lam L aT aL × Isk lam L Bd aT aL) × Tb W) :=
  (unif (Fin (h.ri.n + 1))).bind fun a => (unif (Fin (h.kT.n + 1))).bind fun c =>
    (copiesInward h (h.M + 1)).bind fun ds => commitAtInward W S cA h i ⟨h.ri.e a, h.kT.e c, ds⟩ T

/-- **lateCommit is that committer.** -/
def Spec.lateDraws : Prop :=
  ∀ {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL) (i : I) (T : Tb W),
    lateCommit W S cA h i T = commitInward W S cA h i T

end OnBytes.LateSide
