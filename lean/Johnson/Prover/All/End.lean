-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/End.lean: HOW LIKELY IT IS THAT THE COMPILED VERIFIER SAYS NO TO AN HONEST PROOF
OF A WHOLE REQUEST, over the typed oracles: AT EVERY FIXING OF ALL COINS (exp_law), and so on the
average over them: the library's completeness of a scheme over typed oracles
(ZKCP.Gen.HasCompletenessError, ZKCP/Gen.lean) for (committerOverTypedOracles, proveA, verifyAtKeyRoot) at batches of at most
one request (gen_complete).

How. Behind the coins committer, prover and verifier are one program without coins (expAt).
Pointwise in the oracle functions g: where the verifier says no, what the runs yield lies in the
event of allY_law (Johnson/Prover/All/Law.lean): else all three runs return, the seeds lie outside
the Z's and the verifier messages outside the B's, the accept laws give the three accepts, and
all_yes_of (Johnson/Prover/All/Yes.lean) gives the yes. That event reads no g. The coins are a mean
of bounds.
Main names.
  AccAt   the accept laws as they are spent, at one fixing of the coins.
  not_ev, ok_of_not_ev, exp_no   the pointwise steps.
  exp_law   THE PER-COIN END.
  PrFrom_sample_le, PrFrom_bind_sample_le   a drawn number: a mean of bounds.
  AccLaws, gen_complete   the laws at all coins, for true instances; THE MEAN.

Limits. The accept laws and the bounds on the sets' measures are premises: without them the right
side holds five letters. Typed oracles, typed proofs, fixed wires: no hash function, no bytes, no
public reading. The prover encodes one copy of the committed table for each request. No clause says
that the copy's encoding randomness differs from the first table's or from another copy's.
The experiment is one run of the committer and then one request (ZKCP.Gen.completenessExp at a batch
of at most one): the bound is a mean over the key too. Nothing is said on how many keys are bad, or
on a second request under one key (ZKCP.Gen.HasRefinedCompletenessError, ZKCP/Gen.lean).
It states no goal of the release.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Yes
import Johnson.Prover.All.Law
import Johnson.TypedOracleCompiler.RecCompile.NoCoinAns

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

/-! ## A drawn number -/

theorem PrFrom_sample_le {S : OSpec} {α : Type} (T : Table S) (n : ℕ) (k : Fin (n + 1) → OComp S α)
    (E : Set α) {ε : ℝ≥0∞} (h : ∀ a, PrFrom T (k a) E ≤ ε) : PrFrom T (.sample n k) E ≤ ε := by
  rw [PrFrom_eq_lazy]
  show pr (((unif (Fin (n + 1))).bind fun r => (k r).runLazy T).map Prod.fst) E ≤ ε
  rw [PMF.map_bind]
  refine pr_bind_le_of_forall _ _ _ fun a _ => ?_
  rw [← PrFrom_eq_lazy]
  exact h a

theorem PrFrom_bind_sample_le {S : OSpec} {α β : Type} (T : Table S) (c : OComp S α) (n : ℕ)
    (R : α → Fin (n + 1) → OComp S β) (E : Set β) {ε : ℝ≥0∞}
    (h : ∀ a, PrFrom T (c.bind fun k => R k a) E ≤ ε) :
    PrFrom T (c.bind fun k => .sample n fun a => R k a) E ≤ ε := by
  have e : ∀ out : α × Table S, PrFrom out.2 (.sample n fun a => R out.1 a) E =
      expect (unif (Fin (n + 1))) fun a => PrFrom out.2 (R out.1 a) E := by
    intro out
    rw [PrFrom_eq_lazy]
    show pr (((unif (Fin (n + 1))).bind fun r => (R out.1 r).runLazy out.2).map Prod.fst) E = _
    rw [PMF.map_bind, pr_bind]
    exact expect_congr _ fun a => (PrFrom_eq_lazy _ _ _).symm
  rw [PrFrom_bind, expect_congr _ e, expect_comm]
  refine expect_le_of_forall_le _ fun a _ => ?_
  exact (PrFrom_bind T c (fun k => R k a) E).symm.trans_le (h a)

/-! ## The pointwise steps -/

theorem not_ev {P : Type} {s : Shape} {B : Set (Rho s)} {r : Res (P × Tr s)} (h : r ∉ evT B) :
    r = .noFormat ∨ ∃ π τ, r = .ok (π, τ) ∧ τ.rho ∉ B := by
  cases r with
  | ok z => exact Or.inr ⟨z.1, z.2, rfl, fun hb => h (Or.inr ⟨z.1, z.2, rfl, hb⟩)⟩
  | noFormat => exact Or.inl rfl
  | ranOut j => exact absurd (Or.inl ⟨j, rfl⟩) h

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ)

/-- The accept laws as they are spent, at one index, instance and fixing of the coins: for seeds
outside the Z's; and the copy's number in the session's plain parts. -/
structure AccAt (i : I) (r₁ : L.EncodingRandomness) (x : X) (d : Draw lam L Bd aT aL Kap) (Bs : Bads L) : Prop where
  T : ∀ e₁, e₁ ∉ Bs.Z₁ →
    AccLaw (batTC L aT) (wTC W) (L.recOf i r₁ e₁) (L.encodeIndex i r₁) (st.T i r₁ e₁ d.κ) (Bs.T e₁)
  Lk : ∀ e₁ e₂, e₁ ∉ Bs.Z₁ → e₂ ∉ Bs.Z₂ →
    AccLaw (batLC L aL) (wLC W) (L.recOf i r₁ e₁, L.recOf i d.r e₂) (L.encodeIndex i r₁, L.encodeIndex i d.r)
      (st.Lk i (r₁, e₁) (d.r, e₂) d.κ) (Bs.Lk e₁ e₂)
  B : ∀ e₂, e₂ ∉ Bs.Z₂ →
    AccLaw L.onlineBatch (wBC W) (x, L.recOf i d.r e₂) (L.encodeIndex i d.r) (st.B i d.r e₂ x d.n d.κ) (Bs.B e₂)
  num : ∀ e₂ (τ : Tr L.onlineBatch.loc.shape),
    Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ((st.B i d.r e₂ x d.n d.κ).run τ.rho).1 τ →
    S.num d.n τ.plains = true

theorem det_allX (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (isk : I × L.EncodingRandomness × (ℕ → Bits))
    (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).det g =
      pack isk.1 d ((allY W S cA r₀ b₀ st capT capL capB isk x d).det g) := by
  unfold allX
  rw [OComp.det_bind]
  rfl

/-- Outside the event all three runs have returned, the seeds lie outside the Z's and the verifier
messages outside the B's. -/
theorem ok_of_not_ev (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (hW : WiresFit W cA)
    (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) (Bs : Bads L)
    (h : (allY W S cA r₀ b₀ st capT capL capB isk x d).det g ∉ EvY Bs) :
    ∃ π e₁ e₂ τT τL τB, (allX W S cA r₀ b₀ st capT capL capB isk x d).det g =
        .ok (π, e₁, e₂, τT, τL, τB) ∧ e₁ ∉ Bs.Z₁ ∧ e₂ ∉ Bs.Z₂ ∧ τT.rho ∉ Bs.T e₁ ∧
      τL.rho ∉ Bs.Lk e₁ e₂ ∧ τB.rho ∉ Bs.B e₂ := by
  have hf := all_format W S cA r₀ b₀ st capT capL capB g hW isk x d
  rw [det_allX] at hf ⊢
  generalize (allY W S cA r₀ b₀ st capT capL capB isk x d).det g = Y at h hf
  obtain ⟨cms, e₁, e₂, a, b, c⟩ := Y
  have h1 : e₁ ∉ Bs.Z₁ := fun k => h (Or.inl k)
  have h2 : e₂ ∉ Bs.Z₂ := fun k => h (Or.inr (Or.inl k))
  have h3 : a ∉ evT (Bs.T e₁) := fun k => h (Or.inr (Or.inr (Or.inl k)))
  have h4 : b ∉ evT (Bs.Lk e₁ e₂) := fun k => h (Or.inr (Or.inr (Or.inr (Or.inl k))))
  have h5 : c ∉ evT (Bs.B e₂) := fun k => h (Or.inr (Or.inr (Or.inr (Or.inr k))))
  rcases not_ev h3 with rfl | ⟨πa, τa, rfl, ka⟩
  · exact absurd rfl hf
  rcases not_ev h4 with rfl | ⟨πb, τb, rfl, kb⟩
  · exact absurd rfl hf
  rcases not_ev h5 with rfl | ⟨πc, τc, rfl, kc⟩
  · exact absurd rfl hf
  exact ⟨_, e₁, e₂, τa, τb, τc, rfl, h1, h2, ka, kb, kc⟩

theorem det_committerAtFixedCoins_snd (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (i : I) (r : L.EncodingRandomness)
    (salt : ℕ → Bits) : ((committerAtFixedCoins W S b₀ i r salt).det g).2 = (i, r, salt) := by
  unfold committerAtFixedCoins
  simp only [OComp.det_bind]
  rfl

/-- **Pointwise in g: where the verifier says no, what the runs yield lies in the event.** -/
theorem exp_no (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (hW : WiresFit W cA) (i : I)
    (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap) (π₀ : OfflineLinkOnlineProof lam L aT aL)
    (l₁ : ∀ j, j < L.wordLength → (s₁ j).length = p.sMT) (hd : DrawFit W p d) (Bs : Bads L)
    (acc : AccAt W S st i r₁ x d Bs)
    (h : (expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀).det g = false) :
    (allY W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g ∈ EvY Bs := by
  by_contra hn
  obtain ⟨π, e₁, e₂, τT, τL, τB, hx, h1, h2, h3, h4, h5⟩ :=
    ok_of_not_ev W S cA r₀ b₀ st capT capL capB g hW (i, r₁, s₁) x d Bs hn
  have hy := all_yes_of W S cA r₀ p b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB hW l₁ hd hx
    (fun a b => acc.T e₁ h1 τT a b h3) (fun a b => acc.Lk e₁ e₂ h1 h2 τL a b h4)
    (fun a b => acc.B e₂ h2 τB a b h5) (acc.num e₂ τB)
  unfold expAt at h
  rw [OComp.det_bind, OComp.det_bind, det_committerAtFixedCoins_snd, hx] at h
  rw [show ((Res.ok (π, e₁, e₂, τT, τL, τB) : Res (OfflineLinkOnlineProof lam L aT aL × Seen L)).toOption.map
    Prod.fst).getD π₀ = π from rfl, hy] at h
  cases h

theorem noCoin_VRA (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    (verifyAtKeyRoot W S cA r₀ p k x π).NoCoin := noCoin_VCA W S cA r₀ p (k.full π) x π.low

theorem noCoin_allX (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).NoCoin :=
  (noCoin_allY W S cA r₀ b₀ st capT capL capB isk x d).bind fun _ => trivial

theorem noCoin_expAt (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap)
    (π₀ : OfflineLinkOnlineProof lam L aT aL) : (expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀).NoCoin :=
  (noCoin_committerAtFixedCoins W S b₀ i r₁ s₁).bind fun k =>
    (noCoin_allX W S cA r₀ b₀ st capT capL capB k.2 x d).bind fun _ => noCoin_VRA W S cA r₀ p _ _ _

/-- **THE PER-COIN END.** At every fixing of all coins: committer, prover, verifier: the verifier
says no with probability at most the sum of the bounds. -/
theorem exp_law {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀)
    (hL : LawFit W S capT capL capB) (hW : WiresFit W cA) (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits)
    (x : X) (d : Draw lam L Bd aT aL Kap) (π₀ : OfflineLinkOnlineProof lam L aT aL)
    (l₁ : ∀ j, j < L.wordLength → (s₁ j).length = p.sMT) (hd : DrawFit W p d) (Bs : Bads L)
    (acc : AccAt W S st i r₁ x d Bs) {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}
    (hs : SetsSmall W S Bs ζ₁ ζ₂ δT δL δB) :
    PrFrom T₀ (expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀) {b | b = false} ≤
      alphaAll W capT capL capB ζ₁ ζ₂ δT δL δB :=
  (PrFrom_le_of_det (noCoin_expAt W S cA r₀ p b₀ st capT capL capB i r₁ s₁ x d π₀)
    (noCoin_allY W S cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d) T₀ fun g h =>
      exp_no W S cA r₀ p b₀ st capT capL capB g hW i r₁ s₁ x d π₀ l₁ hd Bs acc h).trans
    (allY_law cA r₀ b₀ st capT capL capB hT hL (i, r₁, s₁) x d Bs hs)

/-! ## The mean over the coins -/

/-- The accept laws at all coins, for true instances, with the bounds on the sets' measures. -/
structure AccLaws (Yes : I → X → Prop) (Bs : I → L.EncodingRandomness → X → Draw lam L Bd aT aL Kap → Bads L)
    (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) : Prop where
  acc : ∀ i r₁ x d, Yes i x → AccAt W S st i r₁ x d (Bs i r₁ x d)
  small : ∀ i r₁ x d, Yes i x → SetsSmall W S (Bs i r₁ x d) ζ₁ ζ₂ δT δL δB

theorem noCoin_verifyAll {S' : OSpec} {I' X' W' IVK ISK Pf : Type}
    (A : ZKCP.Gen.Arg S' I' X' W' IVK ISK Pf) (hV : ∀ k x π, (A.V k x π).NoCoin) (ivk : IVK) :
    ∀ l : List (X' × Pf), (ZKCP.Gen.verifyAll A ivk l).NoCoin
  | [] => trivial
  | (x, π) :: rest =>
    (hV ivk x π).bind fun _ => (noCoin_verifyAll A hV ivk rest).bind fun _ => trivial

theorem det_verifyAll_one {S' : OSpec} {I' X' W' IVK ISK Pf : Type}
    (A : ZKCP.Gen.Arg S' I' X' W' IVK ISK Pf) (g : Fam S') (ivk : IVK) (x : X') (π : Pf) :
    (ZKCP.Gen.verifyAll A ivk [(x, π)]).det g = ((A.V ivk x π).det g && true) := by
  show ((A.V ivk x π).bind fun c => (OComp.pure true).bind fun cs => OComp.pure (c && cs)).det g = _
  rw [OComp.det_bind]
  rfl

theorem freshAll_empty : FreshAll W S (Table.empty (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **THE MEAN: the library's completeness of a scheme over the typed oracles**, for batches of at
most one request. -/
theorem gen_complete (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (dr : Enum (Draw lam L Bd aT aL Kap))
    (π₀ : OfflineLinkOnlineProof lam L aT aL) (Yes : I → X → Prop)
    (Bs : I → L.EncodingRandomness → X → Draw lam L Bd aT aL Kap → Bads L) {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}
    (hL : LawFit W S capT capL capB) (hW : WiresFit W cA)
    (hsl : ∀ a j, j < L.wordLength → (sl.e a j).length = p.sMT) (hdr : ∀ a, DrawFit W p (dr.e a))
    (acc : AccLaws W S st Yes Bs ζ₁ ζ₂ δT δL δB) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (argA W S cA r₀ p b₀ st capT capL capB ri sl dr π₀) 1
      (alphaAll W capT capL capB ζ₁ ζ₂ δT δL δB) := by
  intro i b hb
  show PrFrom (Table.empty _) _ {c | c = false} ≤ _
  match b, hb with
  | [], _ =>
    refine le_of_eq_of_le ?_ (zero_le _)
    refine le_antisymm (PrFrom_bind_le _ _ _ _ fun out _ => ?_) (zero_le _)
    exact le_of_eq (PrFrom_pure _ true _ (by intro h; cases h))
  | [(x, u)], hb =>
    have hY : Yes i x := hb.2 (x, u) (by simp)
    refine PrFrom_sample_le _ _ _ _ fun a => PrFrom_sample_le _ _ _ _ fun a' => ?_
    refine PrFrom_bind_sample_le _ (committerAtFixedCoins W S b₀ i (ri.e a) (sl.e a')) dr.n _ _ fun a'' => ?_
    refine (PrFrom_le_of_det (E' := {c | c = false}) ?_
      (noCoin_expAt W S cA r₀ p b₀ st capT capL capB i (ri.e a) (sl.e a') x (dr.e a'') π₀) _
      fun g h => ?_).trans
      (exp_law W S cA r₀ p b₀ st capT capL capB (freshAll_empty W S) hL hW i (ri.e a) (sl.e a') x
        (dr.e a'') π₀ (hsl a') (hdr a'') (Bs i (ri.e a) x (dr.e a''))
        (acc.acc i (ri.e a) x (dr.e a'') hY) (acc.small i (ri.e a) x (dr.e a'') hY))
    · exact (noCoin_committerAtFixedCoins W S b₀ i _ _).bind fun k =>
        ((noCoin_allX W S cA r₀ b₀ st capT capL capB k.2 x _).bind fun _ =>
          OComp.noCoin_pure _).bind fun _ =>
            noCoin_verifyAll _ (fun k x π => noCoin_VRA W S cA r₀ p k x π) _ _
    · have h1 : OComp.det g _ = false := h
      simp only [OComp.det_bind] at h1
      change (ZKCP.Gen.verifyAll _ _ [(x, _)]).det g = false at h1
      rw [det_verifyAll_one, Bool.and_true] at h1
      show (expAt W S cA r₀ p b₀ st capT capL capB i (ri.e a) (sl.e a') x (dr.e a'') π₀).det g =
        false
      unfold expAt
      simp only [OComp.det_bind]
      exact h1
  | _ :: _ :: _, hb => exact absurd hb.1 (by simp)

end OnBytes.Prover
