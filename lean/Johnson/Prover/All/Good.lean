-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/Good.lean: THE POSITIVE STEP, POINTWISE IN THE ORACLE FUNCTIONS: where what the
runs of a whole request yield lies OUTSIDE the event of allY_law (Johnson/Prover/All/Law.lean), the
prover returns a proof, all tests of the three transcripts are passed, each transcript is its
strategy's own run but for nonces, the proof's plain parts are the transcripts', the three
interactive verifiers accept, the session's plain parts hold the copy's number, and the compiled
verifier says yes at the committer's own key.

Why. exp_law (Johnson/Prover/All/End.lean) bounds "the compiled verifier verifyAtKeyRoot says no". Whoever
stands above verifyAtKeyRoot (a verifier that parses bytes) needs the good case itself, with all that a printer
asks of the honest proof: not the bound on verifyAtKeyRoot's no.

Main names.
  Ends, all_ends   what a returned value holds: the proof's fields with the three compiled provers'
    own equations, the seeds, and for each of the three runs the ends of yes_of_prove
    (OnBytes/Prover/Main.lean).
  allY_roots, allY_seeds, allY_ranOut   the roots are the kept trees'; the seeds are those at the
    two roots; a search runs out in a round with a test alone.
  all_good   THE STATEMENT.

Limits. Pointwise in g: no probability. The accept laws are premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.End

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- What a returned value holds. -/
structure Ends (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap)
    (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape) (τL : Tr L.link.shape)
    (τB : Tr L.onlineBatch.loc.shape) : Prop where
  /-- the proof's fields: the three strings, each with the compiled prover's own equation -/
  fields : ∃ πT πL πB, π = ⟨d.n, some πT,
      (((committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g).root, L.recOf i d.r e₂, some πL), some πB⟩ ∧
    (proveTA W cA (fun _ => (committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g) d.coT capT
      ((committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g).root (L.recOf i r₁ e₁) (L.encodeIndex i r₁)
      (st.T i r₁ e₁ d.κ)).det g = .ok (πT, τT) ∧
    (proveLA W cA (fun k => if k = 0 then (committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g
        else (committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g) d.coL capL
      ((committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g).root ((committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g).root
      (L.recOf i r₁ e₁) (L.recOf i d.r e₂) (L.encodeIndex i r₁, L.encodeIndex i d.r)
      (st.Lk i (r₁, e₁) (d.r, e₂) d.κ)).det g = .ok (πL, τL) ∧
    (proveBA W cA r₀ (fun _ => (committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g) d.coB capB
      ((committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g).root x (L.recOf i d.r e₂) (L.encodeIndex i d.r)
      (st.B i d.r e₂ x d.n d.κ)).det g = .ok (πB, τB) ∧
    πT.plains = τT.plains ∧ πL.plains = τL.plains ∧ πB.plains = τB.plains
  /-- the seeds are those at the two roots -/
  seed₁ : e₁ = seedOfRoot W S g ((committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g).root
  seed₂ : e₂ = seedOfRoot W S g ((committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g).root
  passT : RoundsQueryLayout.pass L.offline.shape aT (wTC W).sh τT.rho = true
  putsT : Puts L.offline.shape aT (wTC W).sh ((st.T i r₁ e₁ d.κ).run τT.rho).1 τT
  passL : RoundsQueryLayout.pass L.link.shape aL (wLC W).sh τL.rho = true
  putsL : Puts L.link.shape aL (wLC W).sh ((st.Lk i (r₁, e₁) (d.r, e₂) d.κ).run τL.rho).1 τL
  passB : RoundsQueryLayout.pass L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh τB.rho = true
  putsB : Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ((st.B i d.r e₂ x d.n d.κ).run τB.rho).1 τB

/-- **What a returned value holds.** -/
theorem all_ends (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap)
    (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape) (τL : Tr L.link.shape)
    (τB : Tr L.onlineBatch.loc.shape) (hW : WiresFit W cA) (l₁ : ∀ j, j < L.wordLength → (s₁ j).length = p.sMT)
    (hd : DrawFit W p d)
    (h : (allX W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g =
      .ok (π, e₁, e₂, τT, τL, τB)) :
    Ends W S cA r₀ b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB := by
  unfold allX allY at h
  simp only [OComp.det_bind, OComp.det, pack] at h
  obtain ⟨a, b, u, ha, hb, hu, hz⟩ := three_eq_ok (show three _ _ _ _ = Res.ok _ from h)
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ : π = _ ∧ e₁ = _ ∧ e₂ = _ ∧ τT = _ ∧ τL = _ ∧ τB = _ := by
    simpa only [Prod.mk.injEq] using hz
  have l₂ := hd.s
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
  exact ⟨⟨a.1, b.1, u.1, rfl, ha, hb, hu, yT.2.2.1, yL.2.2.1, yB.2.2.1⟩, det_seedsO W S g _,
    det_seedsO W S g _,
    yT.1, yT.2.1, yL.1, yL.2.1, yB.1, yB.2.1⟩

/-- The two roots that the runs yield are the two kept trees'. -/
theorem allY_roots (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).1 =
      (((committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 isk.2.1) isk.2.2).det g).root,
        ((committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 d.r) d.s).det g).root) := by
  unfold allY
  simp only [OComp.det_bind, OComp.det]

/-- The two seeds that the runs yield are those at the two roots. -/
theorem allY_seeds (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.1 =
        seedOfRoot W S g ((committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 isk.2.1) isk.2.2).det g).root ∧
      ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.1 =
        seedOfRoot W S g ((committerTreeKeptByProver W b₀ (L.encodeIndex isk.1 d.r) d.s).det g).root := by
  unfold allY
  simp only [OComp.det_bind, OComp.det]
  exact ⟨det_seedsO W S g _, det_seedsO W S g _⟩

/-- A run's search runs out in a round with a test alone. -/
theorem allY_ranOut (hW : WiresFit W cA) (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X)
    (d : Draw lam L Bd aT aL Kap) :
    (∀ j, ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.2.1 = .ranOut j →
        hasTest L.offline.shape aT (wTC W).sh j = true) ∧
      (∀ j, ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.2.2.1 = .ranOut j →
        hasTest L.link.shape aL (wLC W).sh j = true) ∧
      ∀ j, ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g).2.2.2.2.2 = .ranOut j →
        hasTest L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh j = true := by
  unfold allY
  simp only [OComp.det_bind, OComp.det]
  refine ⟨fun j e => ?_, fun j e => ?_, fun j e => ?_⟩
  · rcases proveX_returns Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) _ _ _ _ _ d.coT
      capT g hW.fmt.1 with ⟨z, hz⟩ | ⟨j', hj, ht⟩
    · cases hz.symm.trans e
    · obtain rfl : j' = j := Res.ranOut.inj (hj.symm.trans e)
      exact ht
  · rcases proveX_returns Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) _ _ _ _ _ d.coL
      capL g hW.fmt.2.1 with ⟨z, hz⟩ | ⟨j', hj, ht⟩
    · cases hz.symm.trans e
    · obtain rfl : j' = j := Res.ranOut.inj (hj.symm.trans e)
      exact ht
  · rcases proveX_returns Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) _ _ _ _ _ d.coB
      capB g hW.fmt.2.2 with ⟨z, hz⟩ | ⟨j', hj, ht⟩
    · cases hz.symm.trans e
    · obtain rfl : j' = j := Res.ranOut.inj (hj.symm.trans e)
      exact ht

/-- **The positive step.** Outside the event: a proof, its ends, the three accepts, the copy's
number, and the compiled verifier's yes at the committer's own key. -/
theorem all_good (hW : WiresFit W cA) (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X)
    (d : Draw lam L Bd aT aL Kap) (l₁ : ∀ j, j < L.wordLength → (s₁ j).length = p.sMT) (hd : DrawFit W p d)
    (Bs : Bads L) (acc : AccAt W S st i r₁ x d Bs)
    (hn : (allY W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g ∉ EvY Bs) :
    ∃ π e₁ e₂ τT τL τB,
      (allX W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g = .ok (π, e₁, e₂, τT, τL, τB) ∧
      Ends W S cA r₀ b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB ∧
      L.offline.accept (L.recOf i r₁ e₁) (L.encodeIndex i r₁) τT = true ∧
      L.link.accept (L.recOf i r₁ e₁, L.recOf i d.r e₂) (L.encodeIndex i r₁, L.encodeIndex i d.r) τL = true ∧
      L.onlineBatch.loc.accept (x, L.recOf i d.r e₂) (L.encodeIndex i d.r) τB = true ∧
      S.num d.n τB.plains = true ∧
      (verifyAtKeyRoot W S cA r₀ p ((committerAtFixedCoins W S b₀ i r₁ s₁).det g).1 x π).det g = true := by
  obtain ⟨π, e₁, e₂, τT, τL, τB, hx, h1, h2, h3, h4, h5⟩ :=
    ok_of_not_ev W S cA r₀ b₀ st capT capL capB g hW (i, r₁, s₁) x d Bs hn
  have E := all_ends W S cA r₀ p b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB hW l₁ hd hx
  have aT' := acc.T e₁ h1 τT E.passT E.putsT h3
  have aL' := acc.Lk e₁ e₂ h1 h2 τL E.passL E.putsL h4
  have aB' := acc.B e₂ h2 τB E.passB E.putsB h5
  have hnum := acc.num e₂ τB E.putsB
  exact ⟨π, e₁, e₂, τT, τL, τB, hx, E, aT', aL', aB', hnum,
    all_yes W S cA r₀ p b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB hW l₁ hd hx aT' aL' aB'
      hnum⟩

end OnBytes.Prover
