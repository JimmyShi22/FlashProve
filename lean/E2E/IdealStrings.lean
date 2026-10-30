-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/IdealStrings.lean: in the ideal experiment of index privacy with the scheme's simulator, every
session's proof in the view is produced, except with probability at most N · `capFail`.

Summary. The simulator is `simWholeKey` (Johnson/WholeKey/Wrap.lean). The bound holds against every
adversary, whatever it asks, because the simulator answers a simulated run's Fiat-Shamir queries
with its own fresh samples. It joins the bound for one request (E2E/IdealOneCall.lean), the
invariant (E2E/IdealInvariant.lean) and the union bound (E2E/IdealLoop.lean). It holds for any
interface, wiring and provers.

Main results.
  `ideal_le`: `pr (idealExp R (simWholeKey …) Vt Z i N) {v | some session's proof is not
    produced} ≤ N · capFail …`, for every adversary Vt, every environment that is valid for batches
    of at most one instance, and N ≤ s1 batches. Premises: every OOD seed is in Gs · the listed
    coins hold as many sibling digests as the request tree is deep · the session's simulator always
    returns a value · the proof file's wiring meets its conditions · its annotation is formatted.

Terms: E2E/HidingTerms.lean.

Limits. The ideal experiment alone: for the real one see E2E/SessionsInGame.lean. The first table's
proof and the link proofs are not treated. Nothing about what a proof holds. No security property is
stated.

Definitions and helper lemmas.
  `InvW k s`: the reduction holds all copies, the game has made as many further tables, and at most
    k sessions have been run on each. Three local signs: 𝔉 is the simulated game's host (`hostOf W
    r₀ h Sm i₀`), 𝓛 the bounds on its counts (`boundsW h s1`), 𝒮 the simulator (`simWholeKey W S cA
    r₀ h Sm i₀ s1 Gs PP`).
  `shape_proveStepA`: a reply to a batch of one instance is a list of one proof.
  `inv_init`, `inv_answer`, `inv_prove`: the simulator's three moves keep the invariant.
  `pr_prove`: one batch (`step_none_le`, E2E/IdealOneCall.lean).


-/
import E2E.IdealInvariant
import E2E.IdealLoop

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Hiop.Seeded (gameSim gameW gameReply HostF GSt GOut GIn)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL) (Sm : Sims L) (i₀ : I)
  (s1 : ℕ) (Gs : L.OutOfDomainSeed → Prop)

local notation "𝔉" => hostOf W r₀ h Sm i₀
local notation "𝓛" => boundsW h s1

/-- A reply to a batch of one instance is a list of one proof. -/
theorem shape_proveStepA (w : StG W) (x : X) :
    Keeps 𝔉 𝓛 Gs (proveStepA W cA r₀ h w [x]) (fun _ => True) fun y _ => ∃ π, y.1 = .inr [π] := by
  unfold proveStepA
  refine keeps_bind 𝔉 𝓛 Gs (keeps_quiet 𝔉 𝓛 Gs (fun g => interact_runLazyA _ _ _ g) _)
    fun o => ?_
  cases hm : (w.2.bind fun ts => ts[o.1.j]?) with
  | none =>
    exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh =>
      ⟨⟨o.1.j, h.nm o.1.j, none⟩, congrArg Prod.fst hh.1⟩
  | some t =>
    intro gs T _ y hy
    have hy' : y ∈ (interact (gameW 𝔉 𝓛 Gs _)
        (.call (.sess (o.1.j + 1) x ()) (afterSess W cA r₀ h w.2 x o.1.j t o.1.co o.2))
        (gs, T)).support := hy
    rw [interact] at hy'
    obtain ⟨p, -, hy''⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
    unfold afterSess at hy''
    rw [interact_bind] at hy''
    obtain ⟨q, -, hq⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy''
    obtain rfl := (PMF.mem_support_pure_iff _ _).1 hq
    exact ⟨_, rfl⟩

/-! ## The simulator's three moves under the invariant -/

variable (PP : Type)

local notation "𝒮" => simWholeKey W S cA r₀ h Sm i₀ s1 Gs PP

/-- The reduction holds all copies, the game has made as many further tables, and at most k sessions
have been run on each. -/
def InvW (k : ℕ) (s : StG W × GSt 𝔉 × Tb W) : Prop := WAt W h s.1 ∧ GAt 𝔉 (h.M + 1) k s.2.1

theorem inv_init (hGs : ∀ s, Gs s) (pp : PP) (N : ℕ) :
    ∀ out ∈ ((𝒮).init pp N).support, InvW W r₀ h Sm i₀ 0 out.2 := by
  intro out ho
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ha
  exact keeps_setupA W S cA r₀ h Sm i₀ s1 Gs hGs _ none _ rfl y hy

theorem inv_answer (k : ℕ) (s : StG W × GSt 𝔉 × Tb W)
    (o : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).ι) (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o)
    (hi : InvW W r₀ h Sm i₀ k s) :
    ∀ out ∈ ((𝒮).answer s o q).support, InvW W r₀ h Sm i₀ k out.2 := by
  intro out ho
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
  obtain ⟨e, hg⟩ := keeps_ans W S cA r₀ h Sm i₀ s1 Gs s.1 o q (GAt 𝔉 (h.M + 1) k) s.2.1 s.2.2 hi.2
    y hy
  obtain ⟨ts, hts, hl⟩ := hi.1
  exact ⟨⟨ts, e.trans hts, hl⟩, hg⟩

theorem inv_prove (k : ℕ) (s : StG W × GSt 𝔉 × Tb W) (xs : List X)
    (hi : InvW W r₀ h Sm i₀ k s) :
    ∀ out ∈ ((𝒮).prove s xs).support, InvW W r₀ h Sm i₀ (k + 1) out.2 := by
  intro out ho
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ha
  obtain ⟨e, hg⟩ := keeps_proveStepA W cA r₀ h Sm i₀ s1 Gs s.1 xs (h.M + 1) k s.2.1 s.2.2 hi.2 y hy
  obtain ⟨ts, hts, hl⟩ := hi.1
  exact ⟨⟨ts, e.trans hts, hl⟩, hg⟩

/-- **One batch of the simulator: every proof is produced, except with probability at most
`capFail`.** -/
theorem pr_prove (k : ℕ) (s : StG W × GSt 𝔉 × Tb W) (xs : List X) (hi : InvW W r₀ h Sm i₀ k s)
    (hk : k < s1) (hx : xs.length ≤ 1)
    (hlen : ∀ pv e, (h.dressB pv (h.coB.e e)).path.length = W.depthReq)
    (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support)
    (hOK : RoundsQueryLayout.OKG L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh) (hF : L.onlineBatch.ann.Fmt) :
    pr ((𝒮).prove s xs) {out | ∃ π ∈ out.1.val, π.piB = none} ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 := by
  match xs, hx with
  | [], _ =>
    refine (pr_zero_of_support _ _ fun out _ hb => ?_).trans (zero_le _)
    obtain ⟨π, hπ, -⟩ := hb
    have h0 : out.1.val = [] := List.length_eq_zero_iff.1 out.1.property
    rw [h0] at hπ
    cases hπ
  | [x], _ =>
    obtain ⟨w, gs, T'⟩ := s
    obtain ⟨⟨ts, hts, hl⟩, u, st, rfl, hu⟩ := hi
    show pr (((interact (gameW 𝔉 𝓛 Gs _) (proveStepA W cA r₀ h w [x])
      (some (h.M + 1, u, st), T')).map fun y => (y.1.1, (y.1.2, y.2))).map _) _ ≤ _
    rw [pr_map, pr_map]
    refine (pr_mono_support _ (F := Prod.fst ⁻¹' {a | NoString a.1}) fun y hy hE => ?_).trans ?_
    · obtain ⟨π, hπ⟩ := shape_proveStepA W cA r₀ h Sm i₀ s1 Gs w x _ _ trivial y hy
      obtain ⟨π', hm, hn⟩ := hE
      refine ⟨[π], hπ, π', ?_, hn⟩
      letI : Inhabited (RequestProof lam L) := ⟨⟨0, 0, none⟩⟩
      have hm' : π' ∈ (Compile.GlueB.fit [x] (Compile.GlueB.listOf y.1.1)).val := hm
      rw [hπ] at hm'
      exact hm'
    · rw [← pr_map]
      exact step_none_le W cA r₀ h Sm i₀ s1 Gs w ts hts hl x hlen (h.M + 1) u st T' le_rfl
        (fun e => (hu e).trans_lt hk) hSm hOK hF
  | _ :: _ :: _, hx => exact absurd hx (by simp)

/-- **The ideal experiment: every session's proof in the view is produced, except with probability
at most N · `capFail`**: against every adversary, every environment that names batches of at most
one instance, and at most s1 batches. -/
theorem ideal_le {Wn : Type} (R : ZKCP.Gen.RelPair I X Wn PP)
    (Vt : FullKey lam L aT aL → ZKCP.Gen.AdvVerifier (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) X
      (RequestProof lam L))
    (Z : ZKCP.Gen.ViewEnv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (FullKey lam L aT aL) X Wn
      (RequestProof lam L)) (i : I) (hZ : Z.IsValid R 1 i) (N : ℕ) (hN : N ≤ s1) (hGs : ∀ s, Gs s)
    (hlen : ∀ pv e, (h.dressB pv (h.coB.e e)).path.length = W.depthReq)
    (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support)
    (hOK : RoundsQueryLayout.OKG L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh) (hF : L.onlineBatch.ann.Fmt) :
    pr (ZKCP.Gen.idealExp R (𝒮) Vt Z i N) {v | BadView (fun π => π.piB = none) v} ≤
      (N : ℝ≥0∞) * capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 := by
  refine pr_bind_le_of_forall _ _ _ fun out ho => ?_
  refine idealLoop_le (𝒮) Z (fun π => π.piB = none) (InvW W r₀ h Sm i₀) s1 _
    (fun k s o q hi => inv_answer W S cA r₀ h Sm i₀ s1 Gs PP k s o q hi)
    (fun k s xs hi => inv_prove W S cA r₀ h Sm i₀ s1 Gs PP k s xs hi)
    (fun k s xs hi hk hx => pr_prove W S cA r₀ h Sm i₀ s1 Gs PP k s xs hi hk hx hlen hSm hOK hF)
    (fun v b hb => ?_) _ N _ out.2 0 (fun hb => ?_)
    (inv_init W S cA r₀ h Sm i₀ s1 Gs PP hGs _ N out ho) (by omega)
  · have h1 := (hZ v b hb).1
    unfold ZKCP.Gen.Batch.pairs at h1
    rw [List.length_map] at h1
    unfold ZKCP.Gen.Batch.ownX
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans h1
  · obtain ⟨l, hl, -⟩ := hb
    cases hl

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.pr_prove
#print axioms AtPublicFiles.Shown.ideal_le
#print axioms AtPublicFiles.Shown.inv_init
#print axioms AtPublicFiles.Shown.inv_answer
#print axioms AtPublicFiles.Shown.inv_prove
#print axioms AtPublicFiles.Shown.shape_proveStepA
