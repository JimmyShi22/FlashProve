-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecSetup.lean: THE SETUP OF THE HONEST SIDE THAT LAYS LATE (lateCommit,
Johnson/LateWorld/Defs.lean) IN A NORMAL FORM: first what does not hang on the index, then the rest.
DEFINITIONS AND TWO STATEMENTS. The proofs are in Johnson/LateWorld/Normal.lean (Spec.lateNormal)
and Johnson/LateWorld/TabList.lean (Spec.phaseBad).

This file states no goal of the release: two steps of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

Why. The reduction (setupA, Johnson/WholeKey/Wrap.lean) draws the committer's coins, builds all
trees over fillings and asks for the seeds; the game draws each table's encoding randomness AFTER
its seed is handed in, and each strategy's coins inside its run. The honest committer draws all of
these at the start. To lay the two side by side the honest setup is written as
  phase1   the committer's coins (of which the encoding randomness and the strategies' coins are
           read no more); all trees over fillings, their leaves late; all seeds;
  contC    then, for what phase1 gave: fresh encoding randomness for each table, the bodies put in;
           the key's test and the links, laid late, each with fresh coins of its strategy and with
           the coins of its compiled run that phase1 drew.

Main names (namespace OnBytes.LateWorld).
  Om         what phase1 gives: the committer's coins; (tree over fillings, seed) of the first table
             and of each copy's; the table of answers.
  phase1, drawRs, testM, linkM, linksM, contAt, contC
  Spec.lateNormal   lateCommit = phase1, then contC.
  Spec.phaseBad     from a table of answers with SeedsIn (Johnson/LateWorld/SpecTables.lean), phase1
             gives some seed outside Gs with probability at most (M + 2) · δ.

All draws here go through the honest side's enumerations, as the committer's do: no law of an
enumeration is asked.

Limits. phase1 and contC are devices of the proof and stand in no statement on the scheme. δ is a
letter.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Defs
import Johnson.LateWorld.SpecTabList

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- What phase1 gives: the committer's coins; (tree over fillings, seed) of the first table; the
same of each copy's table; the table of answers. -/
structure Om (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (h : HonestSide lam L Bd aT aL) where
  d : DrawC lam L Bd aT aL h.KT h.KL
  o₁ : TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed
  os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)
  T : Tb W

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-- **What does not hang on the index**: the committer's coins; all trees over fillings, their
leaves late; all seeds. -/
def phase1 (T : Tb W) : PMF (Om W h) :=
  ((coinsC W h).runLazy T).bind fun o₀ =>
  (tabFR W S h.b₀ (cutS (2 ^ W.depth) o₀.1.s) o₀.2).bind fun o₁ =>
  (tabsFR W S h.b₀ (o₀.1.copies.map fun d => cutS (2 ^ W.depth) d.s) o₁.2).bind fun o₂ =>
  PMF.pure ⟨o₀.1, o₁.1, o₂.1, o₂.2⟩

/-- Fresh encoding randomness for n tables. -/
def drawRs : ℕ → PMF (List L.EncodingRandomness)
  | 0 => PMF.pure []
  | n + 1 => (unif (Fin (h.ri.n + 1))).bind fun a =>
      (drawRs n).bind fun rs => PMF.pure (h.ri.e a :: rs)

/-- The key's test laid late, with fresh coins of its strategy; co: the coins of its compiled run,
as drawn. -/
def testM (i : I) (t₁ : TabK lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) (T : Tb W) :
    PMF (Option (OneProtocolProof lam (batTC L aT)) × Tb W) :=
  (unif (Fin (h.kT.n + 1))).bind fun c =>
    lateTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT (h.kT.e c)) co) h.capT t₁.tree.root
      (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r) (h.st.stopT i t₁.r t₁.seed)
      (h.st.T i t₁.r t₁.seed (h.kT.e c)) T

/-- A link laid late, with fresh coins of its strategy. -/
def linkM (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) (T : Tb W) :
    PMF (Option (OneProtocolProof lam (batLC L aL)) × Tb W) :=
  (unif (Fin (h.kL.n + 1))).bind fun c =>
    lateLA W cA (fun k => if k = 0 then t₁.tree else t₂.tree) (h.dressL (h.rvL (h.kL.e c)) co)
      h.capL t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed) (L.recOf i t₂.r t₂.seed)
      (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r) (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))
      (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) (h.kL.e c)) T

/-- The entries of the key's list, one after the other. -/
def linksM (i : I) (t₁ : TabK lam L Bd aT aL) :
    List (Coins lam (typedOracleCarrier L Bd aT aL) × TabK lam L Bd aT aL) → Tb W →
    PMF (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) × Tb W)
  | [], T => PMF.pure ([], T)
  | a :: l, T => (linkM W cA h i t₁ a.2 a.1 T).bind fun o =>
      (linksM i t₁ l o.2).bind fun o' =>
      PMF.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o.1) :: o'.1, o'.2)

/-- The rest behind the tables' encoding randomness r₁, rs. -/
def contAt (i : I) (ω : Om W h) (r₁ : L.EncodingRandomness) (rs : List L.EncodingRandomness) :
    PMF ((FullKey lam L aT aL × Isk lam L Bd aT aL) × Tb W) :=
  (testM W cA h i ⟨r₁, realTree W h.b₀ (L.encodeIndex i r₁) ω.o₁.1, ω.o₁.2⟩ ω.d.co ω.T).bind fun o₃ =>
  (linksM W cA h i ⟨r₁, realTree W h.b₀ (L.encodeIndex i r₁) ω.o₁.1, ω.o₁.2⟩
    ((ω.d.copies.map fun d => d.co).zip (realTabs W h.b₀ i rs ω.os)) o₃.2).bind fun o₄ =>
  PMF.pure ((⟨ω.o₁.1.root, L.recOf i r₁ ω.o₁.2, o₃.1, o₄.1⟩, ⟨i, realTabs W h.b₀ i rs ω.os⟩), o₄.2)

/-- **The rest**: fresh encoding randomness for each table; then the proofs that are made once. -/
def contC (i : I) (ω : Om W h) : PMF ((FullKey lam L aT aL × Isk lam L Bd aT aL) × Tb W) :=
  (unif (Fin (h.ri.n + 1))).bind fun a => (drawRs h ω.os.length).bind fun rs =>
    contAt W cA h i ω (h.ri.e a) rs

/-- **The honest setup in its normal form.** -/
def Spec.lateNormal : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL) (i : I) (T : Tb W),
    lateCommit W S cA h i T = (phase1 W S h T).bind (contC W cA h i)

/-- **Some seed outside Gs.** -/
def Spec.phaseBad : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (T : Tb W),
    pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ → SeedsIn W S Gs T →
    pr (phase1 W S h T) {ω | ¬ Gs ω.o₁.2 ∨ ∃ x ∈ ω.os, ¬ Gs x.2} ≤ ((h.M + 2 : ℕ) : ℝ≥0∞) * δ

end OnBytes.LateWorld
