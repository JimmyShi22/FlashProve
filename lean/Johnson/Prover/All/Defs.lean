-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/Defs.lean: A COMMITTER AND A PROVER OF A WHOLE REQUEST OVER THE TYPED ORACLES, AT
LETTERS, for the compiled verifier at the key (root, record) (verifyAtKeyRoot,
Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean). DEFINITIONS ALONE.

The committer is the library's own (committerOverTypedOracles, Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean), to the
letter. The prover is stateless: from the committer's (index, randomness, salts) it builds the first
table's tree again, asks the seed's two queries at its root, encodes the index once more (the copy),
builds that tree, asks its seed's queries, and runs the compiled prover of one slot
(OnBytes/Prover/Defs.lean) three times: the key's test, the link, the session
(Johnson/Prover/YesOfProve.lean).
ARGUMENTS, not chosen here: the three strategies, as families in the seeds and in the interactive
provers' own coins κ; all coins, by enumerations; the caps; the proof that is handed over where a
search has run out. A salt is any string: what its first part is, is said where bytes are.
Main names.
  seedsO   the seed's two queries at a root.
  Strats, Draw, Seen   the strategies; what the prover draws; what it has seen beside the proof.
  three    three outcomes as one.
  Raw, allY, pack, allX   the runs behind the coins, raw; the proof out of them; the prover behind
    its coins, with what it has seen.
  proveA, argA   the prover with its coins; the scheme (committerOverTypedOracles, proveA, verifyAtKeyRoot).
  expAt    committer, prover, verifier behind all coins: one program without coins.

Limits. Definitions alone. Tied to no program. The prover encodes one copy of the committed table
for each request. No clause says that the copy's encoding randomness differs from the first table's
or from another copy's. One request a proof. seedsO follows outOfDomainSeedIs
(Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) step for step.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.YesOfProve
import Johnson.Prover.CommitterTreeKeptByProver
import Johnson.TypedOracleCompiler.RecCompile.FrontRootAns

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

/-- The three strategies, as families in what the honest side knows, in the seeds, and in the
interactive provers' own coins κ : Kap. -/
structure Strats (L : HolographicProtocol I X) (Kap : Type) where
  T : I → L.EncodingRandomness → L.OutOfDomainSeed → Kap → Strat L.offline.shape Unit
  Lk : I → L.EncodingRandomness × L.OutOfDomainSeed → L.EncodingRandomness × L.OutOfDomainSeed → Kap → Strat L.link.shape Unit
  B : I → L.EncodingRandomness → L.OutOfDomainSeed → X → ℕ → Kap → Strat L.onlineBatch.loc.shape Unit

/-- What the prover draws for a request: the copy's randomness, salts and number; the interactive
provers' own coins; the coins of the three compiled runs. -/
structure Draw (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (Kap : Type) where
  r : L.EncodingRandomness
  s : ℕ → Bits
  n : ℕ
  κ : Kap
  coT : Coins lam (typedOracleCarrier L Bd aT aL)
  coL : Coins lam (typedOracleCarrier L Bd aT aL)
  coB : Coins lam (typedOracleCarrier L Bd aT aL)

/-- What the prover has seen beside the proof: the two seeds, the three transcripts as hashed. -/
abbrev Seen (L : HolographicProtocol I X) : Type :=
  L.OutOfDomainSeed × L.OutOfDomainSeed × Tr L.offline.shape × Tr L.link.shape × Tr L.onlineBatch.loc.shape

/-- Three outcomes as one: the first that is no value. -/
def three {α β γ δ : Type} (f : α → β → γ → δ) : Res α → Res β → Res γ → Res δ
  | .ok a, .ok b, .ok c => .ok (f a b c)
  | .ok _, .ok _, .noFormat => .noFormat
  | .ok _, .ok _, .ranOut j => .ranOut j
  | .ok _, .noFormat, _ => .noFormat
  | .ok _, .ranOut j, _ => .ranOut j
  | .noFormat, _, _ => .noFormat
  | .ranOut j, _, _ => .ranOut j

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params)

/-- The seed's two queries at a root: those of the committer (committerAtFixedCoins) and of the verifier
(outOfDomainSeedIs). -/
def seedsO (cm : Dig lam) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) L.OutOfDomainSeed :=
  (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t) (seedQ0 W S cm)).bind fun a0 =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ1 W S
        (TypedOracleCompiler.Compile.Batch.link (show TypedOracleCompiler.Compile.Batch.FsAns lam W.K from
                    a0)))).bind fun a1 =>
      .pure (S.seed (show TypedOracleCompiler.Compile.Batch.FsAns lam W.K from a1).1)

variable (b₀ : Bd) (st : Strats L Kap) (capT capL capB : ℕ → ℕ)

/-- What the runs of a request yield, raw: the two roots (the key's, the copy's), the two seeds, the
three outcomes. -/
abbrev Raw (lam : ℕ) (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape) : Type :=
  (Dig lam × Dig lam) × L.OutOfDomainSeed × L.OutOfDomainSeed × Res (OneProtocolProof lam (batTC L aT) × Tr L.offline.shape) ×
    Res (OneProtocolProof lam (batLC L aL) × Tr L.link.shape) × Res (OneProtocolProof lam L.onlineBatch × Tr L.onlineBatch.loc.shape)

/-- The runs of a request behind the coins. -/
def allY (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Raw lam L aT aL) :=
  (committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 isk.2.1) isk.2.2).bind fun T₁ =>
  (seedsO W S T₁.root).bind fun e₁ =>
  (committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 d.r) d.s).bind fun T₂ =>
  (seedsO W S T₂.root).bind fun e₂ =>
  (proveTA W cA (fun _ => T₁) d.coT capT T₁.root (L.recOf isk.1 isk.2.1 e₁)
    (L.encodeIndex isk.1 isk.2.1) (st.T isk.1 isk.2.1 e₁ d.κ)).bind fun a =>
  (proveLA W cA (fun k => if k = 0 then T₁ else T₂) d.coL capL T₁.root T₂.root
    (L.recOf isk.1 isk.2.1 e₁) (L.recOf isk.1 d.r e₂) (L.encodeIndex isk.1 isk.2.1, L.encodeIndex isk.1 d.r)
    (st.Lk isk.1 (isk.2.1, e₁) (d.r, e₂) d.κ)).bind fun b =>
  (proveBA W cA r₀ (fun _ => T₂) d.coB capB T₂.root x (L.recOf isk.1 d.r e₂) (L.encodeIndex isk.1 d.r)
    (st.B isk.1 d.r e₂ x d.n d.κ)).bind fun c =>
  .pure ((T₁.root, T₂.root), e₁, e₂, a, b, c)

/-- The proof, with what was seen, out of the raw runs. -/
def pack (i : I) (d : Draw lam L Bd aT aL Kap) (y : Raw lam L aT aL) :
    Res (OfflineLinkOnlineProof lam L aT aL × Seen L) :=
  three (fun a b c =>
    ((⟨d.n, some a.1, (y.1.2, L.recOf i d.r y.2.2.1, some b.1), some c.1⟩ : OfflineLinkOnlineProof lam L aT aL),
      (y.2.1, y.2.2.1, a.2, b.2, c.2))) y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2

/-- **The prover of a whole request behind its coins**, with what it has seen. -/
def allX (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Res (OfflineLinkOnlineProof lam L aT aL × Seen L)) :=
  (allY W S cA r₀ b₀ st capT capL capB isk x d).bind fun y => .pure (pack isk.1 d y)

/-- Committer, prover and verifier behind all coins: one program without coins. -/
def expAt (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap)
    (π₀ : OfflineLinkOnlineProof lam L aT aL) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (committerAtFixedCoins W S b₀ i r₁ s₁).bind fun k =>
    (allX W S cA r₀ b₀ st capT capL capB k.2 x d).bind fun u =>
      verifyAtKeyRoot W S cA r₀ p k.1 x ((u.toOption.map Prod.fst).getD π₀)

variable (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (dr : Enum (Draw lam L Bd aT aL Kap))
  (π₀ : OfflineLinkOnlineProof lam L aT aL)

/-- The prover: one request a proof; where a search has run out it hands over π₀. -/
def proveA (isk : I × L.EncodingRandomness × (ℕ → Bits)) : (b : List (X × Unit)) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (ZKCP.Gen.Slots (OfflineLinkOnlineProof lam L aT aL) b)
  | [] => .pure ⟨[], rfl⟩
  | [(x, _)] => .sample dr.n fun a =>
      (allX W S cA r₀ b₀ st capT capL capB isk x (dr.e a)).bind fun u =>
        .pure ⟨[(u.toOption.map Prod.fst).getD π₀], rfl⟩
  | u :: v :: l => .pure ⟨(u :: v :: l).map fun _ => π₀, by simp⟩

/-- The scheme: the library's committer, this prover, the compiled verifier at the key (root,
record). -/
def argA : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L)
    (I × L.EncodingRandomness × (ℕ → Bits)) (OfflineLinkOnlineProof lam L aT aL) :=
  ⟨committerOverTypedOracles W S ri sl b₀, proveA W S cA r₀ b₀ st capT capL capB dr π₀, verifyAtKeyRoot W S cA r₀ p⟩

end OnBytes.Prover
