-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/Law.lean: THE LAW OF WHAT THE RUNS OF A WHOLE REQUEST YIELD, AT EVERY FIXING OF
THE COINS: a search runs out, or a seed falls into a set Z, or the verifier messages of one of the
three runs fall into a set B (which may hang on the seeds), with probability at most the three
searches' failures + the measures of the Z's and the B's (a B's: with the test bits set to 0).

How. A union bound over five events. The runs have no coins, so under oracle functions g each part
of what they yield is the value of the sub-program that it hangs on, whatever ran beside it: a seed:
its table's tree, then the seed's two queries; a run's outcome: the trees and seeds that it is
handed, then that run. Each event is bounded for ITS sub-program: the trees ask no Fiat-Shamir
oracle; the seeds' queries lie off the places that the chain's freshness asks to be empty (OffAt);
then prove_law (Johnson/Prover/Law/Chain.lean) or seeds_law (Johnson/Prover/Law/SeedsOff.lean). No
freshness across the three chains is wanted. The library's pattern: completeCU
(Johnson/RecCompile/HonestComplete.lean [not in this library]).

Main names.
  OffAt, FreshAll, Bads   the premises' forms; the sets.
  subS, subT, subL, subB   the sub-programs; det_allY: what the runs yield, by them.
  evT, EvY   a run's event; the whole event, on the raw runs.
  subS_law, subT_law, subL_law, subB_law   the five bounds.
  LawFit, SetsSmall, alphaAll   the premises in bundles; the sum of the bounds.
  allY_law   THE STATEMENT.

Limits. At fixed coins. The sets are letters: nothing says that they are small. No verifier occurs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs
import Johnson.Prover.Law.Chain
import Johnson.Prover.Law.Stages
import Johnson.Prover.Law.SeedsOff

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- No query that the committer or the seeds ask is one of the places that the freshness of the
chain at the tag t asks to be empty. -/
def OffAt (t : Tag) (s : Shape) (A : RoundSplits s)
    (embP : PlainPart s A → PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t)) : Prop :=
  ∀ q : FbIn lam (typedOracleCarrier L Bd aT aL) t, (∃ z, q.plain = embP z ∧ q.round = 0 + PlainPart.depth s A z) →
    ¬ SeedQ W S (OracleName.fb t) q

/-- The table holds none of the three chains' Fiat-Shamir queries and no seed's query. -/
structure FreshAll (T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) : Prop where
  T : FreshFrom (L := typedOracleCarrier L Bd aT aL) Tag.test L.offline.shape aT id 0 T₀
  Lk : FreshFrom (L := typedOracleCarrier L Bd aT aL) Tag.link L.link.shape aL id 0 T₀
  B : FreshFrom (L := typedOracleCarrier L Bd aT aL) Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann id 0 T₀
  q0 : ∀ cm, T₀ (OracleName.fb S.t) (seedQ0 W S cm) = none
  q1 : ∀ v, T₀ (OracleName.fb S.t) (seedQ1 W S v) = none

/-- The sets outside which the accept laws hold, as families in the seeds. -/
structure Bads (L : HolographicProtocol I X) where
  Z₁ : Set L.OutOfDomainSeed
  Z₂ : Set L.OutOfDomainSeed
  T : L.OutOfDomainSeed → Set (Rho L.offline.shape)
  Lk : L.OutOfDomainSeed → L.OutOfDomainSeed → Set (Rho L.link.shape)
  B : L.OutOfDomainSeed → Set (Rho L.onlineBatch.loc.shape)

/-- A run's event: its search has run out, or its verifier messages lie in B. -/
def evT {P : Type} {s : Shape} (B : Set (Rho s)) : Set (Res (P × Tr s)) :=
  {r | (∃ j, r = .ranOut j) ∨ ∃ π τ, r = .ok (π, τ) ∧ τ.rho ∈ B}

/-- The whole event, on the raw runs. -/
def EvY (Bs : Bads L) : Set (Raw lam L aT aL) :=
  {y | y.2.1 ∈ Bs.Z₁ ∨ y.2.2.1 ∈ Bs.Z₂ ∨ y.2.2.2.1 ∈ evT (Bs.T y.2.1) ∨
    y.2.2.2.2.1 ∈ evT (Bs.Lk y.2.1 y.2.2.1) ∨ y.2.2.2.2.2 ∈ evT (Bs.B y.2.2.1)}

theorem seedQ_seedsO (cm : Dig lam) : (seedsO W S cm).AsksIn (SeedQ W S) :=
  ⟨Or.inr (Or.inl ⟨cm, rfl⟩), fun _ => ⟨Or.inr (Or.inr ⟨_, rfl⟩), fun _ => trivial⟩⟩

theorem noCoin_seedsO (cm : Dig lam) : (seedsO W S cm).NoCoin := fun _ _ => trivial

theorem avoids_committerTreeKeptByProver (t : Tag) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeKeptByProver W b₀ y salt).Avoids (OracleName.fb t) := avoids_treeO t _ _

variable (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ)

/-! ## The sub-programs -/

/-- a table's tree, then its seed -/
def subS (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) L.OutOfDomainSeed :=
  (committerTreeKeptByProver W b₀ (L.encodeIndex i r) s).bind fun T => seedsO W S T.root

/-- the first table and its seed, then the key's test -/
def subT (isk : I × L.EncodingRandomness × (ℕ → Bits)) (d : Draw lam L Bd aT aL Kap) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
      (L.OutOfDomainSeed × Res (OneProtocolProof lam (batTC L aT) × Tr L.offline.shape)) :=
  (committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 isk.2.1) isk.2.2).bind fun T₁ =>
  (seedsO W S T₁.root).bind fun e₁ =>
  (proveTA W cA (fun _ => T₁) d.coT capT T₁.root (L.recOf isk.1 isk.2.1 e₁)
    (L.encodeIndex isk.1 isk.2.1) (st.T isk.1 isk.2.1 e₁ d.κ)).bind fun a => .pure (e₁, a)

/-- both tables and their seeds, then the link -/
def subL (isk : I × L.EncodingRandomness × (ℕ → Bits)) (d : Draw lam L Bd aT aL Kap) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
      ((L.OutOfDomainSeed × L.OutOfDomainSeed) × Res (OneProtocolProof lam (batLC L aL) × Tr L.link.shape)) :=
  (committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 isk.2.1) isk.2.2).bind fun T₁ =>
  (seedsO W S T₁.root).bind fun e₁ =>
  (committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 d.r) d.s).bind fun T₂ =>
  (seedsO W S T₂.root).bind fun e₂ =>
  (proveLA W cA (fun k => if k = 0 then T₁ else T₂) d.coL capL T₁.root T₂.root
    (L.recOf isk.1 isk.2.1 e₁) (L.recOf isk.1 d.r e₂) (L.encodeIndex isk.1 isk.2.1, L.encodeIndex isk.1 d.r)
    (st.Lk isk.1 (isk.2.1, e₁) (d.r, e₂) d.κ)).bind fun b => .pure ((e₁, e₂), b)

/-- the copy and its seed, then the session -/
def subB (i : I) (x : X) (d : Draw lam L Bd aT aL Kap) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
      (L.OutOfDomainSeed × Res (OneProtocolProof lam L.onlineBatch × Tr L.onlineBatch.loc.shape)) :=
  (committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).bind fun T₂ =>
  (seedsO W S T₂.root).bind fun e₂ =>
  (proveBA W cA r₀ (fun _ => T₂) d.coB capB T₂.root x (L.recOf i d.r e₂) (L.encodeIndex i d.r)
    (st.B i d.r e₂ x d.n d.κ)).bind fun c => .pure (e₂, c)

/-- **Under g each part of what the runs yield is the value of its own sub-program.** -/
theorem det_allY (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (isk : I × L.EncodingRandomness × (ℕ → Bits))
    (x : X) (d : Draw lam L Bd aT aL Kap) :
    ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.1 =
        (subS W S b₀ isk.1 isk.2.1 isk.2.2).det g ∧
      ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.1 =
        (subS W S b₀ isk.1 d.r d.s).det g ∧
      (((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.1,
        ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.2.1) =
          (subT W S cA b₀ st capT isk d).det g ∧
      ((((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.1,
        ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.1),
        ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.2.2.1) =
          (subL W S cA b₀ st capL isk d).det g ∧
      (((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.1,
        ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.2.2.2) =
          (subB W S cA r₀ b₀ st capB isk.1 x d).det g := by
  unfold allY subS subT subL subB
  simp only [OComp.det_bind]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## No coins -/

theorem noCoin_subS (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) : (subS W S b₀ i r s).NoCoin :=
  (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => noCoin_seedsO W S _

theorem noCoin_subT (isk : I × L.EncodingRandomness × (ℕ → Bits)) (d : Draw lam L Bd aT aL Kap) :
    (subT W S cA b₀ st capT isk d).NoCoin :=
  (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ =>
    (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

theorem noCoin_subL (isk : I × L.EncodingRandomness × (ℕ → Bits)) (d : Draw lam L Bd aT aL Kap) :
    (subL W S cA b₀ st capL isk d).NoCoin :=
  (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ =>
    (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ =>
      (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

theorem noCoin_subB (i : I) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (subB W S cA r₀ b₀ st capB i x d).NoCoin :=
  (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ =>
    (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

theorem noCoin_allY (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allY W S cA r₀ b₀ st capT capL capB isk x d).NoCoin :=
  (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ =>
    (noCoin_committerTreeKeptByProver W b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ =>
      (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ =>
        (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ =>
          (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

/-! ## The five bounds -/

variable {W S}

/-- a seed is S.seed of a uniform answer -/
theorem subS_law {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀) (i : I)
    (r : L.EncodingRandomness) (s : ℕ → Bits) (Z : Set L.OutOfDomainSeed) :
    PrFrom T₀ (subS W S b₀ i r s) Z ≤ pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Z} := by
  refine PrFrom_bind_le T₀ _ _ _ fun o ho => ?_
  have hk := fun q => fb_kept (avoids_committerTreeKeptByProver W S.t b₀ (L.encodeIndex i r) s) ho q
  exact seeds_law o.1.root o.2 ((hk _).trans (hT.q0 _)) (fun v => (hk _).trans (hT.q1 v)) Z

/-- the key's test behind its table and seed -/
theorem subT_law {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀)
    (off : OffAt W S Tag.test L.offline.shape aT id) (hW : (wTC W).OKG) (hF : aT.Fmt)
    (hP : PutsApart L.offline.shape aT (wTC W).sh capT 0) (isk : I × L.EncodingRandomness × (ℕ → Bits))
    (d : Draw lam L Bd aT aL Kap) (B : L.OutOfDomainSeed → Set (Rho L.offline.shape)) {δ : ℝ≥0∞}
    (hδ : ∀ e, pr (unif (Rho L.offline.shape))
      {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ B e} ≤ δ) :
    PrFrom T₀ (subT W S cA b₀ st capT isk d) {y | y.2 ∈ evT (B y.1)} ≤
      capFail L.offline.shape aT (wTC W).sh capT 0 + δ := by
  refine PrFrom_bind_le T₀ _ _ _ fun o1 h1 => ?_
  have f1 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.test b₀ _ _) hT.T o1 h1
  refine PrFrom_bind_le o1.2 _ _ _ fun o2 h2 => ?_
  have f2 := fresh_after_asksIn (seedQ_seedsO W S _) off f1 o2 h2
  rw [PrFrom_bind_pure]
  exact (prove_law Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) _ _ _ _ _ d.coT capT
    o2.2 f2 hW hF hP Function.injective_id (B o2.1)).trans (add_le_add le_rfl (hδ _))

/-- the link behind both tables and seeds -/
theorem subL_law {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀)
    (off : OffAt W S Tag.link L.link.shape aL id) (hW : (wLC W).OKG) (hF : aL.Fmt)
    (hP : PutsApart L.link.shape aL (wLC W).sh capL 0) (isk : I × L.EncodingRandomness × (ℕ → Bits))
    (d : Draw lam L Bd aT aL Kap) (B : L.OutOfDomainSeed → L.OutOfDomainSeed → Set (Rho L.link.shape)) {δ : ℝ≥0∞}
    (hδ : ∀ e e', pr (unif (Rho L.link.shape))
      {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ B e e'} ≤ δ) :
    PrFrom T₀ (subL W S cA b₀ st capL isk d) {y | y.2 ∈ evT (B y.1.1 y.1.2)} ≤
      capFail L.link.shape aL (wLC W).sh capL 0 + δ := by
  refine PrFrom_bind_le T₀ _ _ _ fun o1 h1 => ?_
  have f1 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.link b₀ _ _) hT.Lk o1 h1
  refine PrFrom_bind_le o1.2 _ _ _ fun o2 h2 => ?_
  have f2 := fresh_after_asksIn (seedQ_seedsO W S _) off f1 o2 h2
  refine PrFrom_bind_le o2.2 _ _ _ fun o3 h3 => ?_
  have f3 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.link b₀ _ _) f2 o3 h3
  refine PrFrom_bind_le o3.2 _ _ _ fun o4 h4 => ?_
  have f4 := fresh_after_asksIn (seedQ_seedsO W S _) off f3 o4 h4
  rw [PrFrom_bind_pure]
  exact (prove_law Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) _ _ _ _ _ d.coL capL
    o4.2 f4 hW hF hP Function.injective_id (B o2.1 o4.1)).trans (add_le_add le_rfl (hδ _ _))

/-- the session behind the copy and its seed -/
theorem subB_law {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀)
    (off : OffAt W S Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann id) (hW : (wBC W).OKG) (hF : L.onlineBatch.ann.Fmt)
    (hP : PutsApart L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0) (i : I) (x : X)
    (d : Draw lam L Bd aT aL Kap) (B : L.OutOfDomainSeed → Set (Rho L.onlineBatch.loc.shape)) {δ : ℝ≥0∞}
    (hδ : ∀ e, pr (unif (Rho L.onlineBatch.loc.shape))
      {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ B e} ≤ δ) :
    PrFrom T₀ (subB W S cA r₀ b₀ st capB i x d) {y | y.2 ∈ evT (B y.1)} ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 + δ := by
  refine PrFrom_bind_le T₀ _ _ _ fun o1 h1 => ?_
  have f1 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.onl b₀ _ _) hT.B o1 h1
  refine PrFrom_bind_le o1.2 _ _ _ fun o2 h2 => ?_
  have f2 := fresh_after_asksIn (seedQ_seedsO W S _) off f1 o2 h2
  rw [PrFrom_bind_pure]
  exact (prove_law Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) _ _ _ _ _ d.coB capB
    o2.2 f2 hW hF hP Function.injective_id (B o2.1)).trans (add_le_add le_rfl (hδ _))

/-- What the three chains and the seeds ask of the wires and the caps. -/
structure LawFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (capT capL capB : ℕ → ℕ) : Prop where
  offT : OffAt W S Tag.test L.offline.shape aT id
  offL : OffAt W S Tag.link L.link.shape aL id
  offB : OffAt W S Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann id
  okT : (wTC W).OKG
  okL : (wLC W).OKG
  okB : (wBC W).OKG
  fmt : aT.Fmt ∧ aL.Fmt ∧ L.onlineBatch.ann.Fmt
  putsT : PutsApart L.offline.shape aT (wTC W).sh capT 0
  putsL : PutsApart L.link.shape aL (wLC W).sh capL 0
  putsB : PutsApart L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0

/-- Bounds on the measures of the sets. -/
structure SetsSmall (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (Bs : Bads L) (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) : Prop where
  z₁ : pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Bs.Z₁} ≤ ζ₁
  z₂ : pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Bs.Z₂} ≤ ζ₂
  T : ∀ e, pr (unif (Rho L.offline.shape))
    {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ Bs.T e} ≤ δT
  Lk : ∀ e e', pr (unif (Rho L.link.shape))
    {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ Bs.Lk e e'} ≤ δL
  B : ∀ e, pr (unif (Rho L.onlineBatch.loc.shape))
    {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ Bs.B e} ≤ δB

/-- The sum of the bounds. -/
def alphaAll (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (capT capL capB : ℕ → ℕ)
    (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) : ℝ≥0∞ :=
  capFail L.offline.shape aT (wTC W).sh capT 0 + capFail L.link.shape aL (wLC W).sh capL 0 +
    capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 + (ζ₁ + ζ₂) + (δT + δL + δB)

/-- **The law of what the runs of a whole request yield, at every fixing of the coins.** -/
theorem allY_law {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀)
    (hL : LawFit W S capT capL capB) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) (Bs : Bads L) {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}
    (hs : SetsSmall W S Bs ζ₁ ζ₂ δT δL δB) :
    PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) (EvY Bs) ≤
      alphaAll W capT capL capB ζ₁ ζ₂ δT δL δB := by
  have hN := noCoin_allY W S cA r₀ b₀ st capT capL capB isk x d
  have hD := fun g => det_allY W S cA r₀ b₀ st capT capL capB g isk x d
  have e1 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) {y | y.2.1 ∈ Bs.Z₁} ≤ ζ₁ :=
    (PrFrom_le_of_det hN (noCoin_subS W S b₀ _ _ _) T₀ fun g h => by
      rw [← (hD g).1]
      exact h).trans ((subS_law b₀ hT _ _ _ Bs.Z₁).trans hs.z₁)
  have e2 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) {y | y.2.2.1 ∈ Bs.Z₂} ≤ ζ₂ :=
    (PrFrom_le_of_det hN (noCoin_subS W S b₀ _ _ _) T₀ fun g h => by
      rw [← (hD g).2.1]
      exact h).trans ((subS_law b₀ hT _ _ _ Bs.Z₂).trans hs.z₂)
  have e3 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d)
      {y | y.2.2.2.1 ∈ evT (Bs.T y.2.1)} ≤ capFail L.offline.shape aT (wTC W).sh capT 0 + δT :=
    (PrFrom_le_of_det (E' := {y | y.2 ∈ evT (Bs.T y.1)}) hN (noCoin_subT W S cA b₀ st capT isk d) T₀
      fun g h => by
        rw [← (hD g).2.2.1]
        exact h).trans (subT_law cA b₀ st capT hT hL.offT hL.okT hL.fmt.1 hL.putsT isk d Bs.T hs.T)
  have e4 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d)
      {y | y.2.2.2.2.1 ∈ evT (Bs.Lk y.2.1 y.2.2.1)} ≤
        capFail L.link.shape aL (wLC W).sh capL 0 + δL :=
    (PrFrom_le_of_det (E' := {y | y.2 ∈ evT (Bs.Lk y.1.1 y.1.2)}) hN
      (noCoin_subL W S cA b₀ st capL isk d) T₀ fun g h => by
        rw [← (hD g).2.2.2.1]
        exact h).trans
      (subL_law cA b₀ st capL hT hL.offL hL.okL hL.fmt.2.1 hL.putsL isk d Bs.Lk hs.Lk)
  have e5 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d)
      {y | y.2.2.2.2.2 ∈ evT (Bs.B y.2.2.1)} ≤
        capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 + δB :=
    (PrFrom_le_of_det (E' := {y | y.2 ∈ evT (Bs.B y.1)}) hN
      (noCoin_subB W S cA r₀ b₀ st capB isk.1 x d) T₀ fun g h => by
        rw [← (hD g).2.2.2.2]
        exact h).trans
      (subB_law cA r₀ b₀ st capB hT hL.offB hL.okB hL.fmt.2.2 hL.putsB isk.1 x d Bs.B hs.B)
  have hU : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) (EvY Bs) ≤
      ζ₁ + (ζ₂ + ((capFail L.offline.shape aT (wTC W).sh capT 0 + δT) +
        ((capFail L.link.shape aL (wLC W).sh capL 0 + δL) +
          (capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 + δB)))) := by
    refine (PrFrom_union_le T₀ _ {y : Raw lam L aT aL | y.2.1 ∈ Bs.Z₁} _).trans
      (add_le_add e1 ?_)
    refine (PrFrom_union_le T₀ _ {y : Raw lam L aT aL | y.2.2.1 ∈ Bs.Z₂} _).trans
      (add_le_add e2 ?_)
    refine (PrFrom_union_le T₀ _ {y : Raw lam L aT aL | y.2.2.2.1 ∈ evT (Bs.T y.2.1)} _).trans
      (add_le_add e3 ?_)
    exact (PrFrom_union_le T₀ _
      {y : Raw lam L aT aL | y.2.2.2.2.1 ∈ evT (Bs.Lk y.2.1 y.2.2.1)} _).trans (add_le_add e4 e5)
  refine hU.trans (le_of_eq ?_)
  unfold alphaAll
  ring

end OnBytes.Prover
