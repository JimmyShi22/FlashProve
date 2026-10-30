-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/Yes.lean: WHAT THE PROVER OF A WHOLE REQUEST HANDS OVER IS ACCEPTED: under
whatever oracle functions g, the proof that allX (Johnson/Prover/All/Defs.lean) returns gets the yes
of the compiled verifier at the committer's own key (verifyAtKeyRoot, Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean),
if the three interactive verifiers accept the three transcripts as hashed and the session's plain
parts hold the copy's number.

Main names.
  WiresFit, DrawFit   what is asked of the wires, the marks and the three verifiers; the lengths of
    what is drawn.
  three_eq_ok, three_eq_noFormat, det_seedsO, det_committerAtFixedCoins, vca_six   the programs' values under g.
  all_yes_of, all_yes   THE STATEMENT: the three accepts asked only where all tests are passed and
    the transcript is the strategy's own run but for nonces; and asked outright.
  all_format  at formatted marks the outcome is never "no format".

How. verifyAtKeyRoot's run at a key with one entry is the "and" of six runs (vca_six). The two seeds: seedIs_det
(Johnson/TypedOracleCompiler/RecCompile/SeedDet.lean). The three slots: verifyOfflineProof | verifyLinkProof | vBA_yes_of_prove
(Johnson/Prover/YesOfProve.lean), with the outer trees from extAt_key | _link | _session
(Johnson/Prover/CommitterTreeKeptByProver.lean).

Limits. Pointwise in g: no probability. That the three interactive verifiers accept is a premise.
Typed proofs: nothing on bytes. Tied to no program.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs
import Johnson.TypedOracleCompiler.RecCompile.SeedDet

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

/-- What is asked of the wires, the marks and the three verifiers: as the theorems on soundness ask
it, and at most maxRt trees a component. -/
structure WiresFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (cA : L.OutOfDomainAnswer → List (Dig lam)) : Prop where
  oka : OKA W cA
  fewT : FewJ L.offline.shape aT (wTC W).sh ∧ Few0 L.offline.shape aT (wTC W).sh
  fewL : FewJ L.link.shape aL (wLC W).sh ∧ Few0 L.link.shape aL (wLC W).sh
  fewB : FewJ L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ∧ Few0 L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh
  loc : L.offline.IsLocal ∧ L.link.IsLocal ∧ L.onlineBatch.loc.IsLocal
  coh : aT.Coherent ∧ aL.Coherent ∧ L.onlineBatch.ann.Coherent
  fmt : aT.Fmt ∧ aL.Fmt ∧ L.onlineBatch.ann.Fmt

/-- The lengths of what is drawn. -/
structure DrawFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params)
    (d : Draw lam L Bd aT aL Kap) : Prop where
  s : ∀ j, j < L.wordLength → (d.s j).length = p.sMT
  T : d.coT.Fit p.sMT p.sFS W.depthReqT
  Lk : d.coL.Fit p.sMT p.sFS W.depthReqL
  B : d.coB.Fit p.sMT p.sFS W.depthReq

theorem three_eq_ok {α β γ δ : Type} {f : α → β → γ → δ} {a : Res α} {b : Res β} {c : Res γ} {z : δ}
    (h : three f a b c = .ok z) :
    ∃ a' b' c', a = .ok a' ∧ b = .ok b' ∧ c = .ok c' ∧ z = f a' b' c' := by
  cases a <;> cases b <;> cases c <;> first
    | exact ⟨_, _, _, rfl, rfl, rfl, (Res.ok.inj h).symm⟩
    | cases h

theorem three_eq_noFormat {α β γ δ : Type} {f : α → β → γ → δ} {a : Res α} {b : Res β} {c : Res γ}
    (h : three f a b c = .noFormat) : a = .noFormat ∨ b = .noFormat ∨ c = .noFormat := by
  cases a <;> cases b <;> cases c <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | cases h

section
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- the seed that the prover finds is the one that the verifier's test finds -/
theorem det_seedsO (cm : Dig lam) : (seedsO W S cm).det g = seedOfRoot W S g cm := by
  unfold seedsO seedOfRoot seedAns0
  simp only [OComp.det_bind]
  rfl

/-- the committer's key under g: the tree's root, the honest record at the seed at that root -/
theorem det_committerAtFixedCoins (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits) :
    ((committerAtFixedCoins W S b₀ i r salt).det g).1 =
      ⟨((committerTreeKeptByProver W b₀ (L.encodeIndex i r) salt).det g).root,
        L.recOf i r ((seedsO W S ((committerTreeKeptByProver W b₀ (L.encodeIndex i r) salt).det g).root).det g)⟩ := by
  rw [root_committerTreeKeptByProver]
  unfold committerAtFixedCoins seedsO
  simp only [OComp.det_bind]
  rfl

end

section
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- The run of verifyAtFullKey at a key with one entry is the "and" of its six runs. (At 256 bits: vca_det,
Johnson/Top/Fire/KeyArmIsPart.lean [not in this library]; VCA_det, Johnson/Top/TieInnerCompiledVerifier.lean. Here at every length of
a digest, with their proof.) -/
theorem vca_six (cm : Dig lam) (c : L.Rec) (πT : OneProtocolProof lam (batTC L aT)) (cmj : Dig lam) (cj : L.Rec)
    (πL : OneProtocolProof lam (batLC L aL)) (x : X) (n : ℕ) (πB : OneProtocolProof lam L.onlineBatch) :
    (verifyAtFullKey W S cA r₀ p ⟨cm, c, some πT, [(cmj, cj, some πL)]⟩ x ⟨0, n, some πB⟩).det g =
      (S.num n πB.plains && (outOfDomainSeedIs W S cm c.1).det g && (outOfDomainSeedIs W S cmj cj.1).det g &&
        (verifyOfflineProof W cA p cm c πT).det g && (verifyLinkProof W cA p cm cmj c cj πL).det g &&
        (verifyOnlineProof W cA r₀ p cmj x cj πB).det g) := by
  show ((outOfDomainSeedIs W S cm c.1).bind fun s0 =>
      (outOfDomainSeedIs W S cmj cj.1).bind fun sj =>
      (verifyOfflineProof W cA p cm c πT).bind fun a =>
      (verifyLinkProof W cA p cm cmj c cj πL).bind fun b =>
      (verifyOnlineProof W cA r₀ p cmj x cj πB).bind fun d =>
      OComp.pure (S.num n πB.plains && s0 && sj && a && b && d)).det g = _
  simp only [OComp.det_bind]
  rfl

/-- **What the prover of a whole request hands over is accepted**, the three accepts asked only at
transcripts with all tests passed that are the strategies' own runs but for nonces. -/
theorem all_yes_of (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X)
    (d : Draw lam L Bd aT aL Kap) (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape)
    (τL : Tr L.link.shape) (τB : Tr L.onlineBatch.loc.shape) (hW : WiresFit W cA)
    (l₁ : ∀ j, j < L.wordLength → (s₁ j).length = p.sMT) (hd : DrawFit W p d)
    (h : (allX W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g =
      .ok (π, e₁, e₂, τT, τL, τB))
    (aT' : RoundsQueryLayout.pass L.offline.shape aT (wTC W).sh τT.rho = true →
      Puts L.offline.shape aT (wTC W).sh ((st.T i r₁ e₁ d.κ).run τT.rho).1 τT →
      L.offline.accept (L.recOf i r₁ e₁) (L.encodeIndex i r₁) τT = true)
    (aL' : RoundsQueryLayout.pass L.link.shape aL (wLC W).sh τL.rho = true →
      Puts L.link.shape aL (wLC W).sh ((st.Lk i (r₁, e₁) (d.r, e₂) d.κ).run τL.rho).1 τL →
      L.link.accept (L.recOf i r₁ e₁, L.recOf i d.r e₂) (L.encodeIndex i r₁, L.encodeIndex i d.r) τL = true)
    (aB' : RoundsQueryLayout.pass L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh τB.rho = true →
      Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ((st.B i d.r e₂ x d.n d.κ).run τB.rho).1 τB →
      L.onlineBatch.loc.accept (x, L.recOf i d.r e₂) (L.encodeIndex i d.r) τB = true)
    (hn : Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ((st.B i d.r e₂ x d.n d.κ).run τB.rho).1 τB →
      S.num d.n τB.plains = true) :
    (verifyAtKeyRoot W S cA r₀ p ((committerAtFixedCoins W S b₀ i r₁ s₁).det g).1 x π).det g = true := by
  unfold allX allY at h
  simp only [OComp.det_bind, OComp.det, pack] at h
  obtain ⟨a, b, u, ha, hb, hu, hz⟩ := three_eq_ok (show three _ _ _ _ = Res.ok _ from h)
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ : π = _ ∧ e₁ = _ ∧ e₂ = _ ∧ τT = _ ∧ τL = _ ∧ τB = _ := by
    simpa only [Prod.mk.injEq] using hz
  have l₂ := hd.s
  rw [det_committerAtFixedCoins]
  show (verifyAtFullKey W S cA r₀ p ⟨_, _, some a.1, [(_, _, some b.1)]⟩ x ⟨0, d.n, some u.1⟩).det g = true
  have yT := (vTA_yes_of_prove W cA p _ d.coT capT g hW.oka _ _ _ _ hW.fewT.1 hW.fewT.2 hW.loc.1
    hW.coh.1 hW.fmt.1 hd.T (by
      rw [root_committerTreeKeptByProver]
      exact extAt_key W cA g p.sMT b₀ _ _ _ hW.oka.base l₁) a.1 a.2 ha)
  have yL := (vLA_yes_of_prove W cA p _ d.coL capL g hW.oka _ _ _ _ _ _ hW.fewL.1 hW.fewL.2
    hW.loc.2.1 hW.coh.2.1 hW.fmt.2.1 hd.Lk (by
      rw [root_committerTreeKeptByProver, root_committerTreeKeptByProver]
      exact extAt_link W cA g p.sMT b₀ b₀ _ _ _ _ _ _ hW.oka.base l₁ l₂) b.1 b.2 hb)
  have yB := (vBA_yes_of_prove W cA r₀ p _ d.coB capB g hW.oka _ _ _ _ _ hW.fewB.1 hW.fewB.2
    hW.loc.2.2 hW.coh.2.2 hW.fmt.2.2 hd.B (by
      rw [root_committerTreeKeptByProver]
      exact extAt_session W cA g p.sMT b₀ _ _ _ hW.oka.base l₂) u.1 u.2 hu)
  rw [vca_six, yT.2.2.2 (aT' yT.1 yT.2.1), yL.2.2.2 (aL' yL.1 yL.2.1),
    yB.2.2.2 (aB' yB.1 yB.2.1), yB.2.2.1, hn yB.2.1]
  show (true && (outOfDomainSeedIs W S _ ((seedsO W S _).det g)).det g &&
    (outOfDomainSeedIs W S _ ((seedsO W S _).det g)).det g && true && true && true) = true
  rw [(seedIs_det W S g _ _).2 (det_seedsO W S g _), (seedIs_det W S g _ _).2 (det_seedsO W S g _)]
  rfl

/-- The same, the three accepts asked outright. -/
theorem all_yes (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X)
    (d : Draw lam L Bd aT aL Kap) (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape)
    (τL : Tr L.link.shape) (τB : Tr L.onlineBatch.loc.shape) (hW : WiresFit W cA)
    (l₁ : ∀ j, j < L.wordLength → (s₁ j).length = p.sMT) (hd : DrawFit W p d)
    (h : (allX W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g =
      .ok (π, e₁, e₂, τT, τL, τB))
    (aT' : L.offline.accept (L.recOf i r₁ e₁) (L.encodeIndex i r₁) τT = true)
    (aL' : L.link.accept (L.recOf i r₁ e₁, L.recOf i d.r e₂) (L.encodeIndex i r₁, L.encodeIndex i d.r) τL = true)
    (aB' : L.onlineBatch.loc.accept (x, L.recOf i d.r e₂) (L.encodeIndex i d.r) τB = true)
    (hn : S.num d.n τB.plains = true) :
    (verifyAtKeyRoot W S cA r₀ p ((committerAtFixedCoins W S b₀ i r₁ s₁).det g).1 x π).det g = true :=
  all_yes_of W S cA r₀ p b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB hW l₁ hd h
    (fun _ _ => aT') (fun _ _ => aL') (fun _ _ => aB') fun _ => hn

/-- At formatted marks the outcome is never "no format". -/
theorem all_format (hW : WiresFit W cA) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).det g ≠ .noFormat := by
  intro h
  unfold allX allY at h
  simp only [OComp.det_bind, OComp.det, pack] at h
  rcases three_eq_noFormat (show three _ _ _ _ = Res.noFormat from h) with e | e | e
  · rcases proveX_returns Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) _ _ _ _ _ d.coT
      capT g hW.fmt.1 with ⟨z, hz⟩ | ⟨j, hj, -⟩
    · cases hz.symm.trans e
    · cases hj.symm.trans e
  · rcases proveX_returns Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) _ _ _ _ _ d.coL
      capL g hW.fmt.2.1 with ⟨z, hz⟩ | ⟨j, hj, -⟩
    · cases hz.symm.trans e
    · cases hj.symm.trans e
  · rcases proveX_returns Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) _ _ _ _ _ d.coB
      capB g hW.fmt.2.2 with ⟨z, hz⟩ | ⟨j, hj, -⟩
    · cases hz.symm.trans e
    · cases hj.symm.trans e

end

end OnBytes.Prover
