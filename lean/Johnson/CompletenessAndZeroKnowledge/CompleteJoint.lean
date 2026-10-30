-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/CompleteJoint.lean: COMPLETENESS OF THE SCHEME WITH THE WHOLE KEY (argW) FROM BOUNDS OVER
THE PROVER'S COINS AND THE CHALLENGES TOGETHER. A twin of complete_argW (Johnson/WholeKey/Complete.lean),
which asks each bound at every coin. No goal. An implication: the bounds on the provers are premises, proved
here of no protocol. At letters: any interface, any wires, any honest side.

How. At a fixing of all coins the verifier's no lies in the five events of allY_law. Their chances are
kept as they stand (allY_parts, fixed_parts), not bounded. The mean over the coins (cmean) is taken
term by term. In the term of one run, the coin of that run's strategy is taken last, and behind the
prefix that makes the seeds, which reads no coin of a strategy (meanT_le, meanL_le, meanB_le): so the
bound is spent AT EACH SEED, as the mean over the coin at that seed. A coin's number that held at all
seeds at once would be a supremum over seeds inside the mean, which a bound at each seed does not give.
The link's coin is that of the copy at the drawn place (cmean_copies).

Premises beside complete_argW's. The three enumerations of the strategies' coins list each coin once.
-/
import Johnson.WholeKey.CompleteOfRecs

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-! ## The mean over a program that samples coins and makes no query -/

section Mean
variable {S' : OSpec} {γ δ' : Type}

/-- The mean of f over what the program returns. -/
def cmean : OComp S' γ → (γ → ℝ≥0∞) → ℝ≥0∞
  | .pure a, f => f a
  | .sample n k, f => expect (unif (Fin (n + 1))) fun r => cmean (k r) f
  | .query _ _ _, _ => 0

theorem cmean_bind (g : γ → OComp S' δ') (f : δ' → ℝ≥0∞) :
    ∀ c : OComp S' γ, cmean (c.bind g) f = cmean c fun a => cmean (g a) f
  | .pure _ => rfl
  | .sample _ k => expect_congr _ fun r => cmean_bind g f (k r)
  | .query _ _ _ => rfl

theorem cmean_le {P : γ → Prop} {f : γ → ℝ≥0∞} {ε : ℝ≥0∞} (h : ∀ a, P a → f a ≤ ε) :
    ∀ c : OComp S' γ, OnlyCoins P c → cmean c f ≤ ε
  | .pure a, hc => h a hc
  | .sample _ k, hc => expect_le_of_forall_le _ fun r _ => cmean_le h (k r) (hc r)
  | .query _ _ _, hc => hc.elim

theorem cmean_mono {P : γ → Prop} {f g : γ → ℝ≥0∞} (h : ∀ a, P a → f a ≤ g a) :
    ∀ c : OComp S' γ, OnlyCoins P c → cmean c f ≤ cmean c g
  | .pure a, hc => h a hc
  | .sample _ k, hc => expect_mono _ fun r => cmean_mono h (k r) (hc r)
  | .query _ _ _, hc => hc.elim

theorem cmean_add (f g : γ → ℝ≥0∞) :
    ∀ c : OComp S' γ, cmean c (fun a => f a + g a) = cmean c f + cmean c g
  | .pure _ => rfl
  | .sample _ k => (expect_congr _ fun r => cmean_add f g (k r)).trans (expect_add _ _ _)
  | .query _ _ _ => (add_zero 0).symm

theorem cmean_const {P : γ → Prop} (v : ℝ≥0∞) :
    ∀ c : OComp S' γ, OnlyCoins P c → cmean c (fun _ => v) = v
  | .pure _, _ => rfl
  | .sample _ k, hc =>
    (expect_congr _ fun r => cmean_const v (k r) (hc r)).trans (expect_const _ _)
  | .query _ _ _, hc => hc.elim

theorem cmean_zero : ∀ c : OComp S' γ, cmean c (fun _ => 0) = 0
  | .pure _ => rfl
  | .sample _ k => (expect_congr _ fun r => cmean_zero (k r)).trans (expect_const _ _)
  | .query _ _ _ => rfl

theorem cmean_expect_comm {β : Type} (μ : PMF β) (F : γ → β → ℝ≥0∞) :
    ∀ c : OComp S' γ,
      cmean c (fun a => expect μ (F a)) = expect μ fun b => cmean c fun a => F a b
  | .pure _ => rfl
  | .sample _ k =>
    (expect_congr _ fun r => cmean_expect_comm μ F (k r)).trans (expect_comm _ _ _)
  | .query _ _ _ => (expect_const μ 0).symm

/-- Two programs of coins: the means in either order. -/
theorem cmean_comm (c' : OComp S' δ') (F : γ → δ' → ℝ≥0∞) :
    ∀ c : OComp S' γ,
      cmean c (fun a => cmean c' (F a)) = cmean c' fun b => cmean c fun a => F a b
  | .pure _ => rfl
  | .sample n k => by
    show expect (unif (Fin (n + 1))) (fun r => cmean (k r) fun a => cmean c' (F a)) =
      cmean c' fun b => expect (unif (Fin (n + 1))) fun r => cmean (k r) fun a => F a b
    rw [cmean_expect_comm (unif (Fin (n + 1))) (fun b r => cmean (k r) fun a => F a b) c']
    exact expect_congr _ fun r => cmean_comm c' F (k r)
  | .query _ _ _ => (cmean_zero c').symm

theorem cmean_sum5 {P : γ → Prop} {c : OComp S' γ} (hc : OnlyCoins P c) (a b : ℝ≥0∞)
    (t l u : γ → ℝ≥0∞) :
    cmean c (fun x => a + (b + (t x + (l x + u x)))) =
      a + (b + (cmean c t + (cmean c l + cmean c u))) := by
  rw [cmean_add (fun _ => a) _ c, cmean_const a c hc, cmean_add (fun _ => b) _ c,
    cmean_const b c hc, cmean_add t _ c, cmean_add l u c]

theorem PrFrom_sample_eq {α : Type} (T : Table S') (n : ℕ) (k : Fin (n + 1) → OComp S' α)
    (E : Set α) :
    PrFrom T (.sample n k) E = expect (unif (Fin (n + 1))) fun r => PrFrom T (k r) E := by
  rw [PrFrom_eq_lazy]
  show pr (((unif (Fin (n + 1))).bind fun r => (k r).runLazy T).map Prod.fst) E = _
  rw [PMF.map_bind, pr_bind]
  exact expect_congr _ fun r => (PrFrom_eq_lazy _ _ _).symm

theorem PrFrom_bind_sample_eq {α β : Type} (T : Table S') (c : OComp S' α) (n : ℕ)
    (R : α → Fin (n + 1) → OComp S' β) (E : Set β) :
    PrFrom T (c.bind fun k => .sample n fun a => R k a) E =
      expect (unif (Fin (n + 1))) fun a => PrFrom T (c.bind fun k => R k a) E := by
  have e : ∀ out : α × Table S', PrFrom out.2 (.sample n fun a => R out.1 a) E =
      expect (unif (Fin (n + 1))) fun a => PrFrom out.2 (R out.1 a) E :=
    fun out => PrFrom_sample_eq out.2 n _ E
  rw [PrFrom_bind, expect_congr _ e, expect_comm]
  exact expect_congr _ fun a => (PrFrom_bind T c (fun k => R k a) E).symm

/-- In front: the chance is the mean over what is sampled. -/
theorem PrFrom_coins_eq {β : Type} {P : γ → Prop} (T : Table S') (k : γ → OComp S' β) (E : Set β) :
    ∀ c : OComp S' γ, OnlyCoins P c →
      PrFrom T (c.bind k) E = cmean c fun a => PrFrom T (k a) E
  | .pure _, _ => rfl
  | .sample n kk, hc => (PrFrom_sample_eq T n _ E).trans
      (expect_congr _ fun r => PrFrom_coins_eq T k E (kk r) (hc r))
  | .query _ _ _, hc => hc.elim

/-- Behind a program: the same. -/
theorem PrFrom_bind_coins_eq {α β : Type} {P : γ → Prop} (T : Table S') (c₀ : OComp S' α)
    (R : α → γ → OComp S' β) (E : Set β) :
    ∀ c : OComp S' γ, OnlyCoins P c →
      PrFrom T (c₀.bind fun k => c.bind (R k)) E =
        cmean c fun a => PrFrom T (c₀.bind fun k => R k a) E
  | .pure _, _ => rfl
  | .sample n kk, hc =>
    (PrFrom_bind_sample_eq T c₀ n (fun k r => (kk r).bind (R k)) E).trans
      (expect_congr _ fun r => PrFrom_bind_coins_eq T c₀ R E (kk r) (hc r))
  | .query _ _ _, hc => hc.elim

/-- A mean over a coin that the prefix does not read goes behind the prefix. -/
theorem expect_PrFrom_bind_le {K α β : Type} (μ : PMF K) (T : Table S') (c : OComp S' α)
    (g : K → α → OComp S' β) (E : K → Set β) {ε : ℝ≥0∞}
    (h : ∀ out ∈ (c.runLazy T).support,
      expect μ (fun κ => PrFrom out.2 (g κ out.1) (E κ)) ≤ ε) :
    expect μ (fun κ => PrFrom T (c.bind (g κ)) (E κ)) ≤ ε := by
  have e : ∀ κ, PrFrom T (c.bind (g κ)) (E κ) =
      expect (c.runLazy T) fun out => PrFrom out.2 (g κ out.1) (E κ) :=
    fun κ => PrFrom_bind T c (g κ) (E κ)
  rw [expect_congr _ e, expect_comm]
  exact expect_le_of_forall_le _ h

end Mean

/-! ## An enumeration that lists each coin once; the joint chance -/

/-- Where each coin is listed once, the mean over the list is the mean over the coins. -/
theorem expect_enum {β : Type} [Fintype β] [Nonempty β] (e : Enum β) (h : e.OK) (G : β → ℝ≥0∞) :
    expect (unif (Fin (e.n + 1))) (fun a => G (e.e a)) = expect (unif β) G := by
  classical
  have hc : Fintype.card (Fin (e.n + 1)) = Fintype.card β := Fintype.card_of_bijective h
  rw [Prob.expect_fintype, Prob.expect_fintype]
  simp only [PMF.uniformOfFintype_apply, hc]
  exact Function.Bijective.sum_comp h (fun b => (Fintype.card β : ℝ≥0∞)⁻¹ * G b)

/-- The chance over a coin and a challenge together is the mean over the coin of the chance over
the challenge. -/
theorem pr_joint {K R : Type} [Fintype K] [Nonempty K] [Fintype R] [Nonempty R]
    (A : K → Set R) :
    pr (unif (K × R)) {q | q.2 ∈ A q.1} = expect (unif K) fun κ => pr (unif R) (A κ) := by
  classical
  rw [pr_eq_expect, unif_prod, expect_prod]
  refine expect_congr _ fun κ => ?_
  rw [pr_eq_expect]
  rfl

/-! ## The three runs, a mean over a coin at a time -/

section Runs
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap K : Type}
variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ)

/-- The key's test: the mean over a coin that the draw D κ may hold, at a bound at each seed. -/
theorem meanT_le (μ : PMF K) {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hT : FreshAll W S T₀) (off : OffAt W S Tag.test L.offline.shape aT id) (hW : (wTC W).OKG)
    (hF : aT.Fmt) (hP : PutsApart L.offline.shape aT (wTC W).sh capT 0)
    (isk : I × L.EncodingRandomness × (ℕ → Bits)) (D : K → Draw lam L Bd aT aL Kap)
    (B : K → L.OutOfDomainSeed → Set (Rho L.offline.shape)) {δ : ℝ≥0∞}
    (hδ : ∀ e, expect μ (fun κ => pr (unif (Rho L.offline.shape))
      {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ B κ e}) ≤ δ) :
    expect μ (fun κ => PrFrom T₀ (subT W S cA b₀ st capT isk (D κ)) {y | y.2 ∈ evT (B κ y.1)}) ≤
      capFail L.offline.shape aT (wTC W).sh capT 0 + δ := by
  unfold subT
  refine expect_PrFrom_bind_le μ T₀ _ _ _ fun o1 h1 => ?_
  have f1 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.test b₀ _ _) hT.T o1 h1
  refine expect_PrFrom_bind_le μ o1.2 _ _ _ fun o2 h2 => ?_
  have f2 := fresh_after_asksIn (seedQ_seedsO W S _) off f1 o2 h2
  refine (expect_mono μ (G := fun κ => capFail L.offline.shape aT (wTC W).sh capT 0 +
      pr (unif (Rho L.offline.shape))
        {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ B κ o2.1}) fun κ => ?_).trans ?_
  · rw [PrFrom_bind_pure]
    exact prove_law Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) _ _ _ _ _ (D κ).coT
      capT o2.2 f2 hW hF hP Function.injective_id (B κ o2.1)
  · rw [expect_add, expect_const]
    exact add_le_add le_rfl (hδ _)

/-- The link: the same; the copy's randomness and salts stay fixed. -/
theorem meanL_le (μ : PMF K) {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hT : FreshAll W S T₀) (off : OffAt W S Tag.link L.link.shape aL id) (hW : (wLC W).OKG)
    (hF : aL.Fmt) (hP : PutsApart L.link.shape aL (wLC W).sh capL 0)
    (isk : I × L.EncodingRandomness × (ℕ → Bits)) (D : K → Draw lam L Bd aT aL Kap) (r : L.EncodingRandomness) (s : ℕ → Bits)
    (hr : ∀ κ, (D κ).r = r) (hs : ∀ κ, (D κ).s = s)
    (B : K → L.OutOfDomainSeed → L.OutOfDomainSeed → Set (Rho L.link.shape)) {δ : ℝ≥0∞}
    (hδ : ∀ e e', expect μ (fun κ => pr (unif (Rho L.link.shape))
      {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ B κ e e'}) ≤ δ) :
    expect μ (fun κ => PrFrom T₀ (subL W S cA b₀ st capL isk (D κ))
      {y | y.2 ∈ evT (B κ y.1.1 y.1.2)}) ≤
      capFail L.link.shape aL (wLC W).sh capL 0 + δ := by
  unfold subL
  simp only [hr, hs]
  refine expect_PrFrom_bind_le μ T₀ _ _ _ fun o1 h1 => ?_
  have f1 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.link b₀ _ _) hT.Lk o1 h1
  refine expect_PrFrom_bind_le μ o1.2 _ _ _ fun o2 h2 => ?_
  have f2 := fresh_after_asksIn (seedQ_seedsO W S _) off f1 o2 h2
  refine expect_PrFrom_bind_le μ o2.2 _ _ _ fun o3 h3 => ?_
  have f3 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.link b₀ _ _) f2 o3 h3
  refine expect_PrFrom_bind_le μ o3.2 _ _ _ fun o4 h4 => ?_
  have f4 := fresh_after_asksIn (seedQ_seedsO W S _) off f3 o4 h4
  refine (expect_mono μ (G := fun κ => capFail L.link.shape aL (wLC W).sh capL 0 +
      pr (unif (Rho L.link.shape))
        {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ B κ o2.1 o4.1}) fun κ => ?_).trans ?_
  · rw [PrFrom_bind_pure]
    exact prove_law Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) _ _ _ _ _ (D κ).coL
      capL o4.2 f4 hW hF hP Function.injective_id (B κ o2.1 o4.1)
  · rw [expect_add, expect_const]
    exact add_le_add le_rfl (hδ _ _)

/-- The session: the same. -/
theorem meanB_le (μ : PMF K) {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hT : FreshAll W S T₀) (off : OffAt W S Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann id)
    (hW : (wBC W).OKG) (hF : L.onlineBatch.ann.Fmt)
    (hP : PutsApart L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0) (i : I) (x : X)
    (D : K → Draw lam L Bd aT aL Kap) (r : L.EncodingRandomness) (s : ℕ → Bits)
    (hr : ∀ κ, (D κ).r = r) (hs : ∀ κ, (D κ).s = s)
    (B : K → L.OutOfDomainSeed → Set (Rho L.onlineBatch.loc.shape)) {δ : ℝ≥0∞}
    (hδ : ∀ e, expect μ (fun κ => pr (unif (Rho L.onlineBatch.loc.shape))
      {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ B κ e}) ≤ δ) :
    expect μ (fun κ => PrFrom T₀ (subB W S cA r₀ b₀ st capB i x (D κ))
      {y | y.2 ∈ evT (B κ y.1)}) ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 + δ := by
  unfold subB
  simp only [hr, hs]
  refine expect_PrFrom_bind_le μ T₀ _ _ _ fun o1 h1 => ?_
  have f1 := fresh_after_avoids (avoids_committerTreeKeptByProver W Tag.onl b₀ _ _) hT.B o1 h1
  refine expect_PrFrom_bind_le μ o1.2 _ _ _ fun o2 h2 => ?_
  have f2 := fresh_after_asksIn (seedQ_seedsO W S _) off f1 o2 h2
  refine (expect_mono μ (G := fun κ => capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 +
      pr (unif (Rho L.onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ B κ o2.1}) fun κ => ?_).trans ?_
  · rw [PrFrom_bind_pure]
    exact prove_law Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) _ _ _ _ _ (D κ).coB capB
      o2.2 f2 hW hF hP Function.injective_id (B κ o2.1)
  · rw [expect_add, expect_const]
    exact add_le_add le_rfl (hδ _)

/-- The event of allY_law in five chances, kept as they stand. -/
theorem allY_parts {T₀ : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hT : FreshAll W S T₀)
    (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) (Bs : Bads L)
    {ζ₁ ζ₂ : ℝ≥0∞} (z₁ : pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Bs.Z₁} ≤ ζ₁)
    (z₂ : pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Bs.Z₂} ≤ ζ₂) :
    PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) (EvY Bs) ≤
      ζ₁ + (ζ₂ + (PrFrom T₀ (subT W S cA b₀ st capT isk d) {y | y.2 ∈ evT (Bs.T y.1)} +
        (PrFrom T₀ (subL W S cA b₀ st capL isk d) {y | y.2 ∈ evT (Bs.Lk y.1.1 y.1.2)} +
          PrFrom T₀ (subB W S cA r₀ b₀ st capB isk.1 x d) {y | y.2 ∈ evT (Bs.B y.1)}))) := by
  have hN := noCoin_allY W S cA r₀ b₀ st capT capL capB isk x d
  have hD := fun g => det_allY W S cA r₀ b₀ st capT capL capB g isk x d
  have e1 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) {y | y.2.1 ∈ Bs.Z₁} ≤ ζ₁ :=
    (PrFrom_le_of_det hN (noCoin_subS W S b₀ _ _ _) T₀ fun g h => by
      rw [← (hD g).1]
      exact h).trans ((subS_law b₀ hT _ _ _ Bs.Z₁).trans z₁)
  have e2 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d) {y | y.2.2.1 ∈ Bs.Z₂} ≤ ζ₂ :=
    (PrFrom_le_of_det hN (noCoin_subS W S b₀ _ _ _) T₀ fun g h => by
      rw [← (hD g).2.1]
      exact h).trans ((subS_law b₀ hT _ _ _ Bs.Z₂).trans z₂)
  have e3 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d)
      {y | y.2.2.2.1 ∈ evT (Bs.T y.2.1)} ≤
        PrFrom T₀ (subT W S cA b₀ st capT isk d) {y | y.2 ∈ evT (Bs.T y.1)} :=
    PrFrom_le_of_det (E' := {y | y.2 ∈ evT (Bs.T y.1)}) hN (noCoin_subT W S cA b₀ st capT isk d) T₀
      fun g h => by
        rw [← (hD g).2.2.1]
        exact h
  have e4 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d)
      {y | y.2.2.2.2.1 ∈ evT (Bs.Lk y.2.1 y.2.2.1)} ≤
        PrFrom T₀ (subL W S cA b₀ st capL isk d) {y | y.2 ∈ evT (Bs.Lk y.1.1 y.1.2)} :=
    PrFrom_le_of_det (E' := {y | y.2 ∈ evT (Bs.Lk y.1.1 y.1.2)}) hN
      (noCoin_subL W S cA b₀ st capL isk d) T₀ fun g h => by
        rw [← (hD g).2.2.2.1]
        exact h
  have e5 : PrFrom T₀ (allY W S cA r₀ b₀ st capT capL capB isk x d)
      {y | y.2.2.2.2.2 ∈ evT (Bs.B y.2.2.1)} ≤
        PrFrom T₀ (subB W S cA r₀ b₀ st capB isk.1 x d) {y | y.2 ∈ evT (Bs.B y.1)} :=
    PrFrom_le_of_det (E' := {y | y.2 ∈ evT (Bs.B y.1)}) hN
      (noCoin_subB W S cA r₀ b₀ st capB isk.1 x d) T₀ fun g h => by
        rw [← (hD g).2.2.2.2]
        exact h
  refine (PrFrom_union_le T₀ _ {y : Raw lam L aT aL | y.2.1 ∈ Bs.Z₁} _).trans (add_le_add e1 ?_)
  refine (PrFrom_union_le T₀ _ {y : Raw lam L aT aL | y.2.2.1 ∈ Bs.Z₂} _).trans (add_le_add e2 ?_)
  refine (PrFrom_union_le T₀ _ {y : Raw lam L aT aL | y.2.2.2.1 ∈ evT (Bs.T y.2.1)} _).trans
    (add_le_add e3 ?_)
  exact (PrFrom_union_le T₀ _
    {y : Raw lam L aT aL | y.2.2.2.2.1 ∈ evT (Bs.Lk y.2.1 y.2.2.1)} _).trans (add_le_add e4 e5)

end Runs

/-! ## The premises, over coins and challenges together -/

section Premises
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The sets outside which the accept laws hold, each reading the coin of its own run and no other.
Z₁, Z₂: the seeds set aside, at the first table and at a copy. At ThreeProvers.bads this is so by definition (badsByOf below). -/
structure BadsBy (L : HolographicProtocol I X) (KT KL KB : Type) where
  Z₁ : I → L.EncodingRandomness → Set L.OutOfDomainSeed
  Z₂ : I → L.EncodingRandomness → Set L.OutOfDomainSeed
  /-- the key's test: index, first table's randomness, coin, seed -/
  T : I → L.EncodingRandomness → KT → L.OutOfDomainSeed → Set (Rho L.offline.shape)
  /-- a link: index, the two tables' randomness, coin, seeds -/
  Lk : I → L.EncodingRandomness → L.EncodingRandomness → KL → L.OutOfDomainSeed → L.OutOfDomainSeed → Set (Rho L.link.shape)
  /-- a session: index, the copy's randomness, request, the copy's number, coin, seed -/
  B : I → L.EncodingRandomness → X → ℕ → KB → L.OutOfDomainSeed → Set (Rho L.onlineBatch.loc.shape)

/-- The sets at one fixing of the coins. -/
def BadsBy.at {KT KL KB : Type} (F : BadsBy L KT KL KB) (i : I) (r₁ : L.EncodingRandomness) (x : X)
    (d : Draw lam L Bd aT aL (KT × KL × KB)) : Bads L where
  Z₁ := F.Z₁ i r₁
  Z₂ := F.Z₂ i d.r
  T := F.T i r₁ d.κ.1
  Lk := F.Lk i r₁ d.r d.κ.2.1
  B := F.B i d.r x d.n d.κ.2.2

/-- **The accept laws at all coins, with the bounds over coin and challenges together, at each
seed.** acc is AccLaws' own field; the three last fields take the place of SetsSmall's. -/
structure AccLawsJoint (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    {KT KL KB : Type} [Fintype KT] [Nonempty KT] [Fintype KL] [Nonempty KL] [Fintype KB]
    [Nonempty KB] (st : Strats L (KT × KL × KB)) (Yes : I → X → Prop) (F : BadsBy L KT KL KB)
    (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) : Prop where
  acc : ∀ i r₁ x (d : Draw lam L Bd aT aL (KT × KL × KB)), Yes i x →
    AccAt W S st i r₁ x d (F.at i r₁ x d)
  z₁ : ∀ i r x, Yes i x → pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ F.Z₁ i r} ≤ ζ₁
  z₂ : ∀ i r x, Yes i x → pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ F.Z₂ i r} ≤ ζ₂
  T : ∀ i r x e, Yes i x → pr (unif (KT × Rho L.offline.shape))
    {q | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh q.2 ∈ F.T i r q.1 e} ≤ δT
  Lk : ∀ i r r' x e e', Yes i x → pr (unif (KL × Rho L.link.shape))
    {q | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh q.2 ∈ F.Lk i r r' q.1 e e'} ≤ δL
  B : ∀ i r x n e, Yes i x → pr (unif (KB × Rho L.onlineBatch.loc.shape))
    {q | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh q.2 ∈ F.B i r x n q.1 e} ≤ δB

end Premises

/-! ## The end -/

section End
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)

/-- The chance of the key's test's event at fixed coins. -/
def ptT (F : BadsBy L h.KT h.KL h.KB) (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB) : ℝ≥0∞ :=
  PrFrom (Table.empty _) (subT W S cA h.b₀ h.st.joint h.capT (i, c.r, cutS (2 ^ W.depth) c.s)
    (drawOf W h c e dP)) {y | y.2 ∈ evT (F.T i c.r c.κ y.1)}

/-- The chance of the link's event at fixed coins. -/
def ptL (F : BadsBy L h.KT h.KL h.KB) (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB) : ℝ≥0∞ :=
  PrFrom (Table.empty _) (subL W S cA h.b₀ h.st.joint h.capL (i, c.r, cutS (2 ^ W.depth) c.s)
    (drawOf W h c e dP)) {y | y.2 ∈ evT (F.Lk i c.r e.r e.κ y.1.1 y.1.2)}

/-- The chance of the session's event at fixed coins. -/
def ptB (F : BadsBy L h.KT h.KL h.KB) (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB) : ℝ≥0∞ :=
  PrFrom (Table.empty _) (subB W S cA r₀ h.b₀ h.st.joint h.capB i x (drawOf W h c e dP))
    {y | y.2 ∈ evT (F.B i e.r x (h.nm dP.j) dP.κ y.1)}

variable [Fintype h.KT] [Nonempty h.KT] [Fintype h.KL] [Nonempty h.KL] [Fintype h.KB]
  [Nonempty h.KB]

/-- **At fixed coins**: fixed_law's text, stopped before the five chances are bounded. -/
theorem fixed_parts (Yes : I → X → Prop) (F : BadsBy L h.KT h.KL h.KB)
    {ζ₁ ζ₂ δT δL δB : ℝ≥0∞} (hW : WiresFit W cA) (hF : SideFit W p h)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (hS : StopsIn h.st (BadsBy.at (lam := lam) (Bd := Bd) (aT := aT) (aL := aL) F))
    (i : I) (x : X) (hY : Yes i x) (c : DrawC lam L Bd aT aL h.KT h.KL) (hc : DrawCOf h c)
    (dP : DrawP lam L Bd aT aL h.KB) (hd : DrawPOf h dP) (e : DrawCopy lam L Bd aT aL h.KL)
    (he : c.copies[dP.j]? = some e) :
    PrFrom (Table.empty _) ((commitAt W S cA h i c).bind fun key =>
      (proveAt W cA r₀ h key.2 x dP).bind fun π => verifyW W S cA r₀ p key.1 x π)
      {b | b = false} ≤
      ζ₁ + (ζ₂ + (ptT W S cA h F i c e dP + (ptL W S cA h F i c e dP +
        ptB W S cA r₀ h F i x c e dP))) := by
  obtain ⟨⟨b₁, hs₁⟩, ⟨a₁, k₁, hco₁, hk₁⟩, hlen, hcop⟩ := hc
  obtain ⟨hj, ⟨a₃, k₃, hco₃, hk₃⟩⟩ := hd
  obtain ⟨⟨b₂, hs₂⟩, ⟨a₂, k₂, hco₂, hk₂⟩⟩ := hcop _ (List.mem_of_getElem? he)
  have hD : DrawFit W p (drawOf W h c e dP) :=
    ⟨fun j hjn => by
        show (cutS (2 ^ W.depth) e.s j).length = _
        rw [hs₂]
        exact hF.sl b₂ j hjn,
      by
        show (h.dressT (h.rvT c.κ) c.co).Fit _ _ _
        rw [hco₁, hk₁]
        exact hF.coT a₁ k₁,
      by
        show (h.dressL (h.rvL e.κ) e.co).Fit _ _ _
        rw [hco₂, hk₂]
        exact hF.coL a₂ k₂,
      by
        show (h.dressB (h.rvB dP.κ) dP.co).Fit _ _ _
        rw [hco₃, hk₃]
        exact hF.coB a₃ k₃⟩
  refine (PrFrom_le_of_det (E' := EvY (F.at i c.r x (drawOf W h c e dP))) ?_
    (noCoin_allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c e dP)) _ fun g hg => ?_).trans
    (allY_parts cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (freshAll_empty W S)
      (i, c.r, cutS (2 ^ W.depth) c.s) x (drawOf W h c e dP) _ (acc.z₁ i c.r x hY)
      (acc.z₂ i e.r x hY))
  · exact (noCoin_commitAt W S cA h i c).bind fun key =>
      (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun π => noCoin_VRA W S cA r₀ p _ _ _
  · by_contra hn
    have hy := yes_of_not_ev W S cA r₀ p h g hW i x c e dP he
      (fun j hjn => by rw [hs₁]; exact hF.sl b₁ j hjn) hD _ (acc.acc i c.r x _ hY)
      (fun e₁ ρ => hS.T i c.r x (drawOf W h c e dP) e₁ ρ)
      (fun e₁ e₂ ρ => hS.Lk i c.r x (drawOf W h c e dP) e₁ e₂ ρ)
      (fun e₂ ρ => hS.B i c.r x (drawOf W h c e dP) e₂ ρ) hn
    have hg' : OComp.det g _ = false := hg
    simp only [OComp.det_bind] at hg'
    rw [hy] at hg'
    cases hg'

section Means
variable {Yes : I → X → Prop} {F : BadsBy L h.KT h.KL h.KB} {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}

/-- The mean over the key's test's coin, the other coins fixed. -/
theorem mean_ptT (hL : LawFit W S h.capT h.capL h.capB) (okT : h.kT.OK)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X) (hY : Yes i x)
    (r : L.EncodingRandomness) (s : ℕ → Bits) (co : Coins lam (typedOracleCarrier L Bd aT aL))
    (ds : List (DrawCopy lam L Bd aT aL h.KL)) (e : DrawCopy lam L Bd aT aL h.KL)
    (dP : DrawP lam L Bd aT aL h.KB) :
    expect (unif (Fin (h.kT.n + 1)))
      (fun k => ptT W S cA h F i ⟨r, s, h.kT.e k, co, ds⟩ e dP) ≤
      capFail L.offline.shape aT (wTC W).sh h.capT 0 + δT := by
  refine (expect_enum h.kT okT fun κ => ptT W S cA h F i ⟨r, s, κ, co, ds⟩ e dP).trans_le ?_
  exact meanT_le cA h.b₀ h.st.joint h.capT (unif h.KT) (freshAll_empty W S) hL.offT hL.okT
    hL.fmt.1 hL.putsT (i, r, cutS (2 ^ W.depth) s) (fun κ => drawOf W h ⟨r, s, κ, co, ds⟩ e dP)
    (fun κ => F.T i r κ) fun e₁ =>
      (pr_joint fun κ => {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ F.T i r κ e₁}).symm.trans_le
        (acc.T i r x e₁ hY)

/-- The mean over a copy's coin, the other coins fixed. -/
theorem mean_ptL (hL : LawFit W S h.capT h.capL h.capB) (okL : h.kL.OK)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X) (hY : Yes i x)
    (c : DrawC lam L Bd aT aL h.KT h.KL) (r : L.EncodingRandomness) (s : ℕ → Bits)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (dP : DrawP lam L Bd aT aL h.KB) :
    expect (unif (Fin (h.kL.n + 1)))
      (fun k => ptL W S cA h F i c ⟨r, s, h.kL.e k, co⟩ dP) ≤
      capFail L.link.shape aL (wLC W).sh h.capL 0 + δL := by
  refine (expect_enum h.kL okL fun κ => ptL W S cA h F i c ⟨r, s, κ, co⟩ dP).trans_le ?_
  exact meanL_le cA h.b₀ h.st.joint h.capL (unif h.KL) (freshAll_empty W S) hL.offL hL.okL
    hL.fmt.2.1 hL.putsL (i, c.r, cutS (2 ^ W.depth) c.s) (fun κ => drawOf W h c ⟨r, s, κ, co⟩ dP) r
    (cutS (2 ^ W.depth) s) (fun _ => rfl) (fun _ => rfl) (fun κ => F.Lk i c.r r κ) fun e₁ e₂ =>
      (pr_joint fun κ =>
        {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ F.Lk i c.r r κ e₁ e₂}).symm.trans_le
        (acc.Lk i c.r r x e₁ e₂ hY)

/-- The mean over the session's coin, the other coins fixed. -/
theorem mean_ptB (hL : LawFit W S h.capT h.capL h.capB) (okB : h.kB.OK)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X) (hY : Yes i x)
    (c : DrawC lam L Bd aT aL h.KT h.KL) (e : DrawCopy lam L Bd aT aL h.KL) (j : ℕ)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    expect (unif (Fin (h.kB.n + 1)))
      (fun k => ptB W S cA r₀ h F i x c e ⟨j, h.kB.e k, co⟩) ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 + δB := by
  refine (expect_enum h.kB okB fun κ => ptB W S cA r₀ h F i x c e ⟨j, κ, co⟩).trans_le ?_
  exact meanB_le cA r₀ h.b₀ h.st.joint h.capB (unif h.KB) (freshAll_empty W S) hL.offB hL.okB
    hL.fmt.2.2 hL.putsB i x (fun κ => drawOf W h c e ⟨j, κ, co⟩) e.r (cutS (2 ^ W.depth) e.s)
    (fun _ => rfl) (fun _ => rfl) (fun κ => F.B i e.r x (h.nm j) κ) fun e₂ =>
      (pr_joint fun κ => {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈
        F.B i e.r x (h.nm j) κ e₂}).symm.trans_le (acc.B i e.r x (h.nm j) e₂ hY)

end Means

/-- The mean over the committer's coins, draw by draw. -/
theorem cmean_coinsC (f : DrawC lam L Bd aT aL h.KT h.KL → ℝ≥0∞) :
    cmean (coinsC W h) f =
      expect (unif (Fin (h.ri.n + 1))) fun a => expect (unif (Fin (h.sl.n + 1))) fun b =>
        expect (unif (Fin (h.kT.n + 1))) fun k => expect (unif (Fin (h.coT.n + 1))) fun e =>
          cmean (coinsCopies W h (h.M + 1)) fun ds =>
            f ⟨h.ri.e a, h.sl.e b, h.kT.e k, h.coT.e e, ds⟩ := by
  simp only [coinsC, cmean, cmean_bind]

theorem cmean_coinsCopies_succ (n : ℕ) (f : List (DrawCopy lam L Bd aT aL h.KL) → ℝ≥0∞) :
    cmean (coinsCopies W h (n + 1)) f =
      cmean (coinsCopy W h) fun d => cmean (coinsCopies W h n) fun ds => f (d :: ds) := by
  simp only [coinsCopies, cmean, cmean_bind]

/-- **The coin of the copy at a place**: a bound on the mean over one copy's coin, at its other
draws, is a bound on the mean over the coins of all copies. -/
theorem cmean_copies (G : DrawCopy lam L Bd aT aL h.KL → ℝ≥0∞) {ε : ℝ≥0∞}
    (hG : ∀ r s co, expect (unif (Fin (h.kL.n + 1))) (fun k => G ⟨r, s, h.kL.e k, co⟩) ≤ ε) :
    ∀ n j, j < n → cmean (coinsCopies W h n) (fun ds => (ds[j]?).elim 0 G) ≤ ε
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
    rw [cmean_coinsCopies_succ]
    have e : ∀ d, cmean (coinsCopies W h n)
        (fun ds => ((d :: ds)[0]?).elim 0 G) = G d := fun d =>
      cmean_const (G d) _ (onlyCoins_coinsCopies W h n)
    simp only [e]
    show expect (unif (Fin (h.ri.n + 1))) (fun a => expect (unif (Fin (h.sl.n + 1))) fun b =>
      expect (unif (Fin (h.kL.n + 1))) fun c => expect (unif (Fin (h.coL.n + 1))) fun e =>
        G ⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩) ≤ ε
    refine expect_le_of_forall_le _ fun a _ => expect_le_of_forall_le _ fun b _ => ?_
    rw [expect_comm]
    exact expect_le_of_forall_le _ fun e _ => hG _ _ _
  | n + 1, j + 1, hj => by
    rw [cmean_coinsCopies_succ]
    exact cmean_le (fun d _ => cmean_copies G hG n j (Nat.lt_of_succ_lt_succ hj)) _
      (onlyCoins_coinsCopy W h)

/-- The three chances at the copy at the drawn place; 0 where there is none. -/
def optT (F : BadsBy L h.KT h.KL h.KB) (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (dP : DrawP lam L Bd aT aL h.KB) : ℝ≥0∞ :=
  (c.copies[dP.j]?).elim 0 fun e => ptT W S cA h F i c e dP

def optL (F : BadsBy L h.KT h.KL h.KB) (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (dP : DrawP lam L Bd aT aL h.KB) : ℝ≥0∞ :=
  (c.copies[dP.j]?).elim 0 fun e => ptL W S cA h F i c e dP

def optB (F : BadsBy L h.KT h.KL h.KB) (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (dP : DrawP lam L Bd aT aL h.KB) : ℝ≥0∞ :=
  (c.copies[dP.j]?).elim 0 fun e => ptB W S cA r₀ h F i x c e dP

section Total
variable {Yes : I → X → Prop} {F : BadsBy L h.KT h.KL h.KB} {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}

theorem mean_optT (hL : LawFit W S h.capT h.capL h.capB) (okT : h.kT.OK)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X) (hY : Yes i x) :
    cmean (coinsC W h) (fun c => cmean (coinsP W h) (optT W S cA h F i c)) ≤
      capFail L.offline.shape aT (wTC W).sh h.capT 0 + δT := by
  rw [cmean_coinsC]
  refine expect_le_of_forall_le _ fun a _ => expect_le_of_forall_le _ fun b _ => ?_
  rw [expect_comm]
  refine expect_le_of_forall_le _ fun e _ => ?_
  refine (cmean_expect_comm _ _ _).symm.le.trans ?_
  refine cmean_le (fun ds _ => ?_) _ (onlyCoins_coinsCopies W h _)
  refine (cmean_expect_comm _ _ _).symm.le.trans ?_
  refine cmean_le (fun dP _ => ?_) _ (onlyCoins_coinsP W h)
  show expect _ (fun k => (ds[dP.j]?).elim 0 fun e' =>
    ptT W S cA h F i ⟨h.ri.e a, h.sl.e b, h.kT.e k, h.coT.e e, ds⟩ e' dP) ≤ _
  cases hO : ds[dP.j]? with
  | none =>
    simp only [Option.elim]
    rw [expect_const]
    exact zero_le _
  | some e' => exact mean_ptT W S cA h hL okT acc i x hY _ _ _ _ e' dP

theorem mean_optL (hL : LawFit W S h.capT h.capL h.capB) (okL : h.kL.OK)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X) (hY : Yes i x) :
    cmean (coinsC W h) (fun c => cmean (coinsP W h) (optL W S cA h F i c)) ≤
      capFail L.link.shape aL (wLC W).sh h.capL 0 + δL := by
  rw [cmean_comm (coinsP W h) (fun c dP => optL W S cA h F i c dP) (coinsC W h)]
  refine cmean_le (fun dP hdP => ?_) _ (onlyCoins_coinsP W h)
  rw [cmean_coinsC]
  refine expect_le_of_forall_le _ fun a _ => expect_le_of_forall_le _ fun b _ =>
    expect_le_of_forall_le _ fun k _ => expect_le_of_forall_le _ fun e _ => ?_
  exact cmean_copies W h
    (fun e' => ptL W S cA h F i ⟨h.ri.e a, h.sl.e b, h.kT.e k, h.coT.e e, []⟩ e' dP)
    (fun r s co => mean_ptL W S cA h hL okL acc i x hY _ r s co dP) _ _ hdP.1

theorem mean_optB (hL : LawFit W S h.capT h.capL h.capB) (okB : h.kB.OK)
    (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X) (hY : Yes i x) :
    cmean (coinsC W h) (fun c => cmean (coinsP W h) (optB W S cA r₀ h F i x c)) ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 + δB := by
  refine cmean_le (fun c _ => ?_) _ (onlyCoins_coinsC W h)
  show expect (unif (Fin (h.M + 1))) (fun j => expect (unif (Fin (h.kB.n + 1))) fun k =>
    expect (unif (Fin (h.coB.n + 1))) fun e =>
      optB W S cA r₀ h F i x c ⟨j.val, h.kB.e k, h.coB.e e⟩) ≤ _
  refine expect_le_of_forall_le _ fun j _ => ?_
  rw [expect_comm]
  refine expect_le_of_forall_le _ fun e _ => ?_
  show expect _ (fun k => (c.copies[j.val]?).elim 0 fun e' =>
    ptB W S cA r₀ h F i x c e' ⟨j.val, h.kB.e k, h.coB.e e⟩) ≤ _
  cases hO : c.copies[j.val]? with
  | none =>
    simp only [Option.elim]
    rw [expect_const]
    exact zero_le _
  | some e' => exact mean_ptB W S cA r₀ h hL okB acc i x hY c e' j.val _

/-- **The mean of the bound at fixed coins**: the number of complete_argW. -/
theorem mean_total (hL : LawFit W S h.capT h.capL h.capB) (okT : h.kT.OK) (okL : h.kL.OK)
    (okB : h.kB.OK) (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB) (i : I) (x : X)
    (hY : Yes i x) :
    cmean (coinsC W h) (fun c => cmean (coinsP W h) fun dP =>
      ζ₁ + (ζ₂ + (optT W S cA h F i c dP + (optL W S cA h F i c dP +
        optB W S cA r₀ h F i x c dP)))) ≤
      alphaAll W h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB := by
  have e : ∀ c : DrawC lam L Bd aT aL h.KT h.KL,
      cmean (coinsP W h) (fun dP => ζ₁ + (ζ₂ + (optT W S cA h F i c dP +
        (optL W S cA h F i c dP + optB W S cA r₀ h F i x c dP)))) =
      ζ₁ + (ζ₂ + (cmean (coinsP W h) (optT W S cA h F i c) +
        (cmean (coinsP W h) (optL W S cA h F i c) +
          cmean (coinsP W h) (optB W S cA r₀ h F i x c)))) :=
    fun c => cmean_sum5 (onlyCoins_coinsP W h) ζ₁ ζ₂ _ _ _
  simp only [e]
  rw [cmean_sum5 (onlyCoins_coinsC W h) ζ₁ ζ₂]
  refine (add_le_add le_rfl (add_le_add le_rfl (add_le_add
    (mean_optT W S cA h hL okT acc i x hY) (add_le_add
      (mean_optL W S cA h hL okL acc i x hY)
      (mean_optB W S cA r₀ h hL okB acc i x hY))))).trans (le_of_eq ?_)
  unfold alphaAll
  ring

end Total

/-- **COMPLETENESS OF THE SCHEME WITH THE WHOLE KEY, FROM BOUNDS OVER COINS AND CHALLENGES
TOGETHER.** complete_argW's number and conclusion; in the place of SetsSmall at every draw, the
bounds of AccLawsJoint at each seed; beside them, the three enumerations of the strategies' coins
list each coin once. -/
theorem complete_argW_joint (Yes : I → X → Prop) (F : BadsBy L h.KT h.KL h.KB)
    {ζ₁ ζ₂ δT δL δB : ℝ≥0∞} (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA)
    (hF : SideFit W p h) (acc : AccLawsJoint W S h.st.joint Yes F ζ₁ ζ₂ δT δL δB)
    (hS : StopsIn h.st (BadsBy.at (lam := lam) (Bd := Bd) (aT := aT) (aL := aL) F)) (okT : h.kT.OK) (okL : h.kL.OK) (okB : h.kB.OK) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (argW W S cA r₀ p h) 1 (alphaAll W h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB) := by
  intro i b hb
  show PrFrom (Table.empty _) _ {c | c = false} ≤ _
  match b, hb with
  | [], _ =>
    refine le_of_eq_of_le ?_ (zero_le _)
    refine le_antisymm (PrFrom_bind_le _ _ _ _ fun out _ => ?_) (zero_le _)
    exact le_of_eq (PrFrom_pure _ true _ (by intro h; cases h))
  | [(x, u)], hb =>
    have hY : Yes i x := hb.2 (x, u) (by simp)
    show PrFrom _ (((coinsC W h).bind fun d => commitAt W S cA h i d).bind fun key =>
      ((coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π =>
        (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof lam L) [(x, u)]))).bind fun πs =>
          ZKCP.Gen.verifyAll (argW W S cA r₀ p h) key.1 (([(x, u)].map Prod.fst).zip πs.val)) _ ≤ _
    simp only [OComp.bind_assoc]
    refine (PrFrom_coins_eq _ _ _ _ (onlyCoins_coinsC W h)).trans_le ?_
    refine (cmean_mono (fun c hc => ?_) _ (onlyCoins_coinsC W h)).trans
      (mean_total W S cA r₀ h hL okT okL okB acc i x hY)
    refine (PrFrom_bind_coins_eq _ (commitAt W S cA h i c) _ _ _
      (onlyCoins_coinsP W h)).trans_le ?_
    refine cmean_mono (fun dP hdP => ?_) _ (onlyCoins_coinsP W h)
    have hj' : dP.j < c.copies.length := by rw [hc.2.2.1]; exact hdP.1
    have he : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj'
    refine (PrFrom_le_of_det (E' := {b | b = false}) ?_ ?_ _ fun g hg => ?_).trans
      ((fixed_parts W S cA r₀ p h Yes F hW hF acc hS i x hY c hc dP hdP _ he).trans (le_of_eq ?_))
    · exact (noCoin_commitAt W S cA h i c).bind fun key =>
        (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun π =>
          noCoin_verifyAll _ (fun k x π => noCoin_VRA W S cA r₀ p _ _ _) _ _
    · exact (noCoin_commitAt W S cA h i c).bind fun key =>
        (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun π => noCoin_VRA W S cA r₀ p _ _ _
    · have h1 : OComp.det g _ = false := hg
      simp only [OComp.det_bind] at h1
      change (ZKCP.Gen.verifyAll _ _ [(x, _)]).det g = false at h1
      rw [det_verifyAll_one, Bool.and_true] at h1
      show OComp.det g _ = false
      simp only [OComp.det_bind]
      exact h1
    · simp only [optT, optL, optB, he, Option.elim]
  | _ :: _ :: _, hb => exact absurd hb.1 (by simp)

end End

/-! ## Each bound at every coin gives the bound over coins and challenges together -/

section PerCoin
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

theorem pr_joint_le {K R : Type} [Fintype K] [Nonempty K] [Fintype R] [Nonempty R]
    (A : K → Set R) {δ : ℝ≥0∞} (h : ∀ κ, pr (unif R) (A κ) ≤ δ) :
    pr (unif (K × R)) {q | q.2 ∈ A q.1} ≤ δ := by
  rw [pr_joint]
  exact expect_le_of_forall_le _ fun κ _ => h κ

/-- **The law at every coin is a member**: AccLaws at a family of this form gives AccLawsJoint.
d₀: any draw. -/
theorem accLawsJoint_of_accLaws {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {KT KL KB : Type} [Fintype KT] [Nonempty KT] [Fintype KL]
    [Nonempty KL] [Fintype KB] [Nonempty KB] {st : Strats L (KT × KL × KB)} {Yes : I → X → Prop}
    {F : BadsBy L KT KL KB} {ζ₁ ζ₂ δT δL δB : ℝ≥0∞} (d₀ : Draw lam L Bd aT aL (KT × KL × KB))
    (acc : AccLaws W S st Yes (BadsBy.at (lam := lam) (Bd := Bd) (aT := aT) (aL := aL) F) ζ₁ ζ₂ δT δL δB) :
    AccLawsJoint W S st Yes F ζ₁ ζ₂ δT δL δB where
  acc := acc.acc
  z₁ := fun i r x hY => (acc.small i r x d₀ hY).z₁
  z₂ := fun i r x hY => (acc.small i r x { d₀ with r := r } hY).z₂
  T := fun i r x e hY =>
    pr_joint_le (fun κ => {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ F.T i r κ e}) fun κ =>
      (acc.small i r x { d₀ with κ := (κ, d₀.κ.2) } hY).T e
  Lk := fun i r r' x e e' hY =>
    pr_joint_le (fun κ => {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ F.Lk i r r' κ e e'})
      fun κ => (acc.small i r x { d₀ with r := r', κ := (d₀.κ.1, κ, d₀.κ.2.2) } hY).Lk e e'
  B := fun i r x n e hY =>
    pr_joint_le
      (fun κ => {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ F.B i r x n κ e}) fun κ =>
      (acc.small i r x { d₀ with r := r, n := n, κ := (d₀.κ.1, d₀.κ.2.1, κ) } hY).B e

/-- The three structures' sets as a family: ThreeProvers.bads reads each coin in its own run alone. -/
def badsByOf (Hs : ThreeProvers L) (Fl : Falls Hs) (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) :
    BadsBy L Hs.T.Coin Hs.Lk.Coin Hs.B.Coin where
  Z₁ := Z
  Z₂ := Z
  T := fun i r κ e => Hs.T.withheld (i, r, e) (L.recOf i r e) ∪ Fl.T (i, r, e) (L.recOf i r e) κ
  Lk := fun i r r' κ e e' =>
    Hs.Lk.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      Fl.Lk (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') κ
  B := fun i r x n κ e =>
    Hs.B.withheld (i, r, e, n) (x, L.recOf i r e) ∪ Fl.B (i, r, e, n) (x, L.recOf i r e) κ

theorem badsByOf_at (Hs : ThreeProvers L) (Fl : Falls Hs) (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (i : I) (r₁ : L.EncodingRandomness)
    (x : X) (d : Draw lam L Bd aT aL (Hs.T.Coin × Hs.Lk.Coin × Hs.B.Coin)) :
    (badsByOf Hs Fl Z).at i r₁ x d = badsOf Hs Fl Z i r₁ x d := rfl

end PerCoin

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.cmean_comm
#print axioms OnBytes.WholeKey.PrFrom_bind_coins_eq
#print axioms OnBytes.WholeKey.expect_PrFrom_bind_le
#print axioms OnBytes.WholeKey.expect_enum
#print axioms OnBytes.WholeKey.pr_joint
#print axioms OnBytes.WholeKey.meanT_le
#print axioms OnBytes.WholeKey.meanL_le
#print axioms OnBytes.WholeKey.meanB_le
#print axioms OnBytes.WholeKey.allY_parts
#print axioms OnBytes.WholeKey.fixed_parts
#print axioms OnBytes.WholeKey.cmean_copies
#print axioms OnBytes.WholeKey.mean_total
#print axioms OnBytes.WholeKey.complete_argW_joint
#print axioms OnBytes.WholeKey.accLawsJoint_of_accLaws
#print axioms OnBytes.WholeKey.badsByOf_at
