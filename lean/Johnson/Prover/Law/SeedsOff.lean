-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/SeedsOff.lean: THE SEEDS' TWO QUERIES LIE OFF THE PLACES THAT FreshFrom READS:
so the committer (committerAtFixedCoins, Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) and the verifier's own outOfDomainSeedIs
(Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) keep FreshFrom, at the seeds' own tag too; and the premise is
met at the plain part that verify()'s letters lay.

Why. There are three tags and no fourth: the seeds share a Fiat-Shamir oracle with a chain (where
verify() stands: fb .test, the key file's). chain_meets_q1 (Johnson/TypedOracleCompiler/RecCompile/SeedsApart.lean)
shows that at unlucky letters a chain does ask a seed's second query.

Main names.
  SeedsOff   THE PREMISE: the seeds' first plain part is no plain part of round 1, the second none
    of round 2 (as embP writes plain parts).
  SeedQ   what the committer asks: no Fiat-Shamir oracle at all, or a seed's first or second query.
  asksIn_of_avoids_all, asksIn_committerTreeRoot, asksIn_committerAtFixedCoins, asksIn_committerOverTypedOracles, asksIn_seedIs
  seedQ_off   under SeedsOff no such query is one of FreshFrom's places from round 0 on, at the
    seeds' tag; seedQ_other: at another tag: no premise.
  fresh_after_seedQ, fresh_after_seedQ_other   SO FreshFrom IS KEPT by every program that asks in
    SeedQ.
  seeds_law   the seed's two queries, from a table that holds neither: the seed is S.seed of a
    uniform answer: Pr[the seed in Z] is at most the measure of {a | S.seed a in Z}.
  seedsOff_of_depth   at embP := id the premise follows from "both plain parts are of round 0".
  depth_plainFirst, depth_plF   THAT IS SO AT verify()'s LETTERS: pl0 = pl1 = PV.MFull.plF
    (Johnson/PV/MFull.lean; laid by vAtR, Johnson/Top/Fire/Code/TieAtValues.lean), which is
    SeedVals.plainFirst: by unfolding.

Limits. That a description's record of seeds holds plF, and that its key file's embP is id
(fileKeyD, Johnson/Flat/Dec/ChainedAtFrame.lean [not in this library]): by these files' texts; not called here. Nothing on
whether two seeds' queries meet each other. On the support of a run's law alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Stages
import Johnson.Prover.Law.Round
import Johnson.TypedOracleCompiler.RecCompile.CommitOverTypedOracles
import Johnson.PV.MFull

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Rom.Derive (Avoids.bind)
open Prob
open scoped ENNReal

/-- The second form's names of oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- **The premise**: the seeds' first plain part is no plain part of round 1, the second none of
round 2. -/
def SeedsOff {s : Shape} {A : RoundSplits s}
    (embP : PlainPart s A → PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) S.t) (annOf (typedOracleCarrier L Bd aT aL) S.t)) :
    Prop :=
  (∀ z, embP z = S.pl0 → PlainPart.depth s A z ≠ 1) ∧ ∀ z, embP z = S.pl1 → PlainPart.depth s A z ≠ 2

/-- What the committer asks: no Fiat-Shamir oracle at all, or a seed's first or second query. -/
def SeedQ (o : ON₂) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) : Prop :=
  (∀ t, o ≠ OracleName.fb t) ∨
    (∃ cm, (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) = ⟨OracleName.fb S.t, seedQ0 W S cm⟩) ∨
    ∃ v, (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) = ⟨OracleName.fb S.t, seedQ1 W S v⟩

/-- A program that asks no Fiat-Shamir oracle. -/
theorem asksIn_of_avoids_all {α : Type} {K : ℕ} {L' : BatchProtocolWithLeafBody I X} :
    ∀ {c : TypedOracleComputation lam K L' α}, (∀ t, c.Avoids (OracleName.fb t)) → c.AsksIn fun o _ => ∀ t, o ≠ OracleName.fb t
  | .pure _, _ => trivial
  | .query _ _ _, h => ⟨fun t => (h t).1, fun r => asksIn_of_avoids_all fun t => (h t).2 r⟩
  | .sample _ _, h => fun r => asksIn_of_avoids_all fun t => h t r

theorem avoids_committerLeafHashes (t : Tag) : ∀ l : List (LeafIn (typedOracleCarrier L Bd aT aL)),
    (committerLeafHashes W l).Avoids (OracleName.fb t)
  | [] => trivial
  | _ :: xs =>
    Avoids.bind (c := OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf _)
      ⟨(by intro h; cases h), fun _ => trivial⟩ fun _ =>
      Avoids.bind (avoids_committerLeafHashes t xs) fun _ => trivial

theorem avoids_committerTreeRoot (t : Tag) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeRoot W b₀ y salt).Avoids (OracleName.fb t) :=
  Avoids.bind (avoids_committerLeafHashes W t _) fun l =>
    Avoids.bind (avoids_levelsO t W.depth l) fun _ => trivial

theorem asksIn_committerTreeRoot (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeRoot W b₀ y salt).AsksIn (SeedQ W S) :=
  (asksIn_of_avoids_all fun t => avoids_committerTreeRoot W t b₀ y salt).mono fun _ _ h => Or.inl h

/-- **The committer behind its coins asks in SeedQ.** -/
theorem asksIn_committerAtFixedCoins (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits) :
    (committerAtFixedCoins W S b₀ i r salt).AsksIn (SeedQ W S) :=
  asksIn_bind (asksIn_committerTreeRoot W S b₀ _ salt) fun root =>
    ⟨Or.inr (Or.inl ⟨root, rfl⟩), fun _ => ⟨Or.inr (Or.inr ⟨_, rfl⟩), fun _ => trivial⟩⟩

theorem asksIn_committerOverTypedOracles (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : Bd) (i : I) :
    (committerOverTypedOracles W S ri sl b₀ i).AsksIn (SeedQ W S) :=
  fun a c => asksIn_committerAtFixedCoins W S b₀ i (ri.e a) (sl.e c)

/-- The verifier's own test of a seed asks in SeedQ. -/
theorem asksIn_seedIs (cm : Dig lam) (s : L.OutOfDomainSeed) : (outOfDomainSeedIs W S cm s).AsksIn (SeedQ W S) :=
  ⟨Or.inr (Or.inl ⟨cm, rfl⟩), fun _ => ⟨Or.inr (Or.inr ⟨_, rfl⟩), fun _ => trivial⟩⟩

variable {W S}

/-- **Under SeedsOff no query in SeedQ is one of FreshFrom's places from round 0 on.** -/
theorem seedQ_off {s : Shape} {A : RoundSplits s}
    {embP : PlainPart s A → PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) S.t) (annOf (typedOracleCarrier L Bd aT aL) S.t)}
    (off : SeedsOff W S embP) (q : FbIn lam (typedOracleCarrier L Bd aT aL) S.t)
    (hq : ∃ z, q.plain = embP z ∧ q.round = 0 + PlainPart.depth s A z) : ¬ SeedQ W S (OracleName.fb S.t) q := by
  obtain ⟨z, h1, h2⟩ := hq
  rintro (h | ⟨cm, e⟩ | ⟨v, e⟩)
  · exact h S.t rfl
  · obtain rfl := eq_of_heq (Sigma.mk.inj e).2
    exact off.1 z h1.symm (by have : (1 : ℕ) = 0 + PlainPart.depth s A z := h2; omega)
  · obtain rfl := eq_of_heq (Sigma.mk.inj e).2
    exact off.2 z h1.symm (by have : (2 : ℕ) = 0 + PlainPart.depth s A z := h2; omega)

/-- At another tag: no query to fb t is in SeedQ. -/
theorem seedQ_other {t : Tag} (ht : t ≠ S.t) (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) :
    ¬ SeedQ W S (OracleName.fb t) q := by
  rintro (h | ⟨cm, e⟩ | ⟨v, e⟩)
  · exact h t rfl
  · exact ht (OracleName.fb.inj (Sigma.mk.inj e).1)
  · exact ht (OracleName.fb.inj (Sigma.mk.inj e).1)

/-- **FreshFrom at the seeds' own tag is kept by every program that asks in SeedQ**, under
SeedsOff. -/
theorem fresh_after_seedQ {α : Type} {s : Shape} {A : RoundSplits s}
    {embP : PlainPart s A → PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) S.t) (annOf (typedOracleCarrier L Bd aT aL) S.t)}
    (off : SeedsOff W S embP) {c : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) α} (h : c.AsksIn (SeedQ W S))
    {T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshFrom S.t s A embP 0 T) :
    ∀ x ∈ (c.runLazy T).support, FreshFrom S.t s A embP 0 x.2 :=
  fresh_after_asksIn h (seedQ_off off) hT

/-- **FreshFrom at another tag likewise**: no premise on the seeds. -/
theorem fresh_after_seedQ_other {α : Type} {t : Tag} (ht : t ≠ S.t) {s : Shape} {A : RoundSplits s}
    {embP : PlainPart s A → PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t)} {i : ℕ}
    {c : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) α} (h : c.AsksIn (SeedQ W S))
    {T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshFrom t s A embP i T) :
    ∀ x ∈ (c.runLazy T).support, FreshFrom t s A embP i x.2 :=
  fresh_after_asksIn h (fun q _ => seedQ_other ht q) hT

/-- **The seed's two queries, from a table that holds neither: the seed is S.seed of a uniform
answer.** The program is the text of the committer's two queries (committerAtFixedCoins) and of the verifier's
(outOfDomainSeedIs). -/
theorem seeds_law (cm : Dig lam) (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (h0 : T (OracleName.fb S.t) (seedQ0 W S cm) = none) (h1 : ∀ v, T (OracleName.fb S.t) (seedQ1 W S v) = none)
    (Z : Set L.OutOfDomainSeed) :
    PrFrom T ((askTypedOracle (L := typedOracleCarrier L Bd aT aL) (K := W.K) (OracleName.fb S.t) (seedQ0 W S cm)).bind
        fun a0 => (askTypedOracle (L := typedOracleCarrier L Bd aT aL) (K := W.K) (OracleName.fb S.t)
          (seedQ1 W S (TypedOracleCompiler.Compile.Batch.link a0))).bind
            fun a1 => OComp.pure (S.seed a1.1)) Z ≤
      pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Z} := by
  rw [PrFrom_ask S.t _ _ T h0]
  refine expect_le_of_forall_le _ fun a0 _ => ?_
  have hne : seedQ1 W S (TypedOracleCompiler.Compile.Batch.link a0) ≠ seedQ0 W S cm := fun e =>
    absurd (show (2 : ℕ) = 1 from
      congrArg (fun z : FbIn lam (typedOracleCarrier L Bd aT aL) S.t => z.round) e) (by decide)
  rw [PrFrom_bind_pure, PrFrom_ask_new S.t _ _ (by rw [set_fb_other _ _ hne]; exact h1 _),
    ← Prob.map_fst_unif (C := Fin W.K → Dig lam) (D := Dig lam), pr_map]
  exact le_refl _

/-- At embP := id the premise follows from "both plain parts are of round 0". -/
theorem seedsOff_of_depth
    (h0 : PlainPart.depth _ _ S.pl0 = 0) (h1 : PlainPart.depth _ _ S.pl1 = 0) : SeedsOff W S id :=
  ⟨fun z e => by rw [show z = S.pl0 from e, h0]; decide,
    fun z e => by rw [show z = S.pl1 from e, h1]; decide⟩

/-- SeedVals.plainFirst is a plain part of round 0. -/
theorem depth_plainFirst (r : Round) (s : Shape) (a : RAnn r) (A : RoundSplits s) :
    PlainPart.depth (r :: s) (a, A) (TypedOracleCompiler.Run.SeedVals.plainFirst r s a A) = 0 := rfl

end OnBytes.Prover

namespace PV.MFull
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX))
  (aL : RoundSplits (LvOf DK DP runK runP rK rP depthReq early lk).link.shape)

/-- **The plain part that verify()'s letters lay for the seeds' two queries is of round 0.** -/
theorem depth_plF : PlainPart.depth _ _ (plF DK DP runK runP rK rP depthReq early lk aL) = 0 := rfl

end PV.MFull

#print axioms PV.MFull.depth_plF
#print axioms OnBytes.Prover.asksIn_committerAtFixedCoins
#print axioms OnBytes.Prover.asksIn_committerOverTypedOracles
#print axioms OnBytes.Prover.asksIn_seedIs
#print axioms OnBytes.Prover.seedQ_off
#print axioms OnBytes.Prover.seedQ_other
#print axioms OnBytes.Prover.fresh_after_seedQ
#print axioms OnBytes.Prover.fresh_after_seedQ_other
#print axioms OnBytes.Prover.seeds_law
#print axioms OnBytes.Prover.seedsOff_of_depth
#print axioms OnBytes.Prover.depth_plainFirst
