-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/IdealOneCall.lean: one request to the scheme's simulator produces a proof, except with
probability at most `capFail`.

Summary. The simulator `simWholeKey` is the reduction (`proveStepA`, Johnson/WholeKey/Wrap.lean)
around the library's simulated game (Hiop/Seeded/Game.lean). By the definitions, a simulated session
produces no proof in five cases: the setup was refused · the game refuses the call · the first pass
has yielded no verifier messages · the interactive protocol's simulator returns nothing · the second
pass's chain does not end in a value. Premises on the two states exclude the first two, and a
premise on the simulator the fourth. The last reduces to the third (`rho_of_replay`,
OnBytes/Dry/ViewAt.lean), which is `pass1_ends` (E2E/DryEndsWell.lean). The results hold for any
interface, wiring and provers.

Main results.
  `step_none_le`: one request produces a proof, except with probability at most `capFail`, if the
    reduction holds all M + 1 copies · the game has made as many further tables, and fewer than s1
    sessions have been run on each · the listed coins hold as many sibling digests as the request
    tree is deep · the session's simulator always returns a value · the wiring meets its conditions
    · the annotation is formatted.
  `call_none_le`: the same for one session's call and what follows it.

Terms: E2E/HidingTerms.lean.

Limits. One request, from given states: that these states are reached is proved in
E2E/IdealInvariant.lean. Nothing about what the proof holds. No security property is stated.

Definitions and helper lemmas.
  `gameOf`, `hostOf`: the simulated game and its host.
  `NoString out`: a reply to a batch in which some proof is not produced.
  `afterSess`: what follows a session's call in the reduction.
  `pass2_some`: if the first pass has yielded verifier messages and there is a view, the second pass
    produces a proof.
  `reply_sess`: the game's reply to a session's call within the bounds.
  `pr_zero_of_support`, `onlyCoins_support`: two tools.


-/
import E2E.DryEndsWell
import OnBytes.Dry.ViewAt
import Hiop.Seeded.GameProof
import Rom.Handle.Adv
import Johnson.WholeKey.Complete

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Hiop.Seeded (gameSim gameW gameReply showAt)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL) (Sm : Sims L) (i₀ : I)
  (s1 : ℕ) (Gs : L.OutOfDomainSeed → Prop)

/-- The simulated game, around which the scheme's simulator is the reduction. -/
abbrev gameOf : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (Hiop.Seeded.GOut L (kitW W r₀ h).form) (Hiop.Seeded.GIn L (kitW W r₀ h).form) :=
  gameSim L (kitW W r₀ h) (simsG h Sm) i₀ (boundsW h s1) Gs _

/-- A reply to a batch in which some proof is not produced. -/
def NoString (out : Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) : Prop :=
  ∃ l, out = .inr l ∧ ∃ π ∈ l, π.piB = none

/-- If the first pass of a simulated session has yielded verifier messages and there is a view, the
second pass produces a proof. -/
theorem pass2_some (x : X) (t : TabW lam L Bd aT aL) (d : DView L.onlineBatch.loc)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (hlen : co.path.length = W.depthReq)
    (rc : L.Rec) (a : (kitW W r₀ h).AB)
    (ha : a ∈ ((kitW W r₀ h).μB 0 (x, rc)).support) (hρ : a.1.toOption ≠ none)
    (T : Tb W) (g : (gameOf W r₀ h Sm i₀ s1 Gs).σ) :
    ∀ y ∈ (interact (gameOf W r₀ h Sm i₀ s1 Gs)
      (pass2A Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2) (x, t.ood)
        (fun _ => t.tree) h.capB W.embE (some d) co a.2 T) g).support, y.1.1.isSome = true := by
  intro y hy
  unfold pass2A at hy
  rw [interact_bind, interact_runReplayA, PMF.bind_map] at hy
  obtain ⟨o, ho, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  have e := rho_of_replay Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) []
    (cmsBA cA t.tree.root t.ood.2) (x, rc) (x, t.ood) h.capB (Strat.dflt _ ())
    (blank h.b₀ W.depthReq) co (by rw [hlen]; exact List.length_replicate ..)
    (stratFor L.onlineBatch (wBC W) (some d)) T [] a ha o ho
  have hy' : y = ((handOut L.onlineBatch (wBC W) (x, t.ood)
      ((wBC W).ext.build (ansOf L.onlineBatch (some d)))
      (namedAt L.onlineBatch (wBC W) (fun _ => t.tree) W.embE (ansOf L.onlineBatch (some d))) true co o), g) :=
    (PMF.mem_support_pure_iff _ _).1 hy
  rw [hy']
  cases ho1 : o.1 with
  | ok z =>
    unfold handOut
    rw [ho1]
    rfl
  | noFormat => rw [ho1] at e; exact absurd (by rw [e]; rfl) hρ
  | ranOut j => rw [ho1] at e; exact absurd (by rw [e]; rfl) hρ

/-- The simulated game's host. -/
abbrev hostOf : Hiop.Seeded.HostF L (kitW W r₀ h).form :=
  (Hiop.Seeded.simWholeF L (kitW W r₀ h).form
    (Hiop.Seeded.simsFG L (kitW W r₀ h) (simsG h Sm)) i₀).host

/-- The game's reply to a session's call within the bounds. -/
theorem reply_sess (x : X) (e c : ℕ) (u : Hiop.UsedR) (st : ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed))
    (hc : e ≤ c) (he : e ≠ 0) (hu : u.sess e < s1) :
    gameReply (hostOf W r₀ h Sm i₀) (boundsW h s1) Gs (some (c, u, st)) (.sess e x ()) =
      ((hostOf W r₀ h Sm i₀).session st e x ()).map fun p =>
        (.sess x p.1, some (c, { u with sess := Hiop.bump u.sess e }, p.2)) := by
  have hb : (boundsW h s1).sess e = s1 := if_neg he
  simp only [gameReply]
  rw [if_pos ⟨hc, by rw [hb]; exact hu, le_rfl⟩]

theorem pr_zero_of_support {α : Type} (p : PMF α) (E : Set α) (hE : ∀ y ∈ p.support, y ∉ E) :
    pr p E ≤ 0 :=
  le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff p E).2 (Set.disjoint_left.2 hE))

/-- What follows a session's call in the reduction. -/
abbrev afterSess (w₂ : Option (List (TabW lam L Bd aT aL))) (x : X) (j : ℕ)
    (t : TabW lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) (T : Tb W) :
    Hiop.Seeded.GIn L (kitW W r₀ h).form →
      AdvG W r₀ h (Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L) × StG W) := fun rp =>
  (match rp with
    | .sess _ u =>
        pass2A Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2)
          (x, t.ood) (fun _ => t.tree) h.capB W.embE u.2
          (match u.2 with
            | some d => h.dressB (h.pvB d.plains) co
            | none => co) u.1.2 T
    | _ => .halt (none, T)).bind fun o' =>
  .halt (.inr [⟨j, h.nm j, o'.1⟩], (o'.2, w₂))

/-- **One session's call and what follows it: the proof is produced, except with probability at most
`capFail`.** -/
theorem call_none_le (w₂ : Option (List (TabW lam L Bd aT aL))) (x : X) (j : ℕ)
    (t : TabW lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL))
    (hlen : ∀ pv, (h.dressB pv co).path.length = W.depthReq) (T : Tb W) (c : ℕ)
    (u : Hiop.UsedR) (st : ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)) (T' : Tb W) (hc : j + 1 ≤ c)
    (hu : u.sess (j + 1) < s1) (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support)
    (hOK : RoundsQueryLayout.OKG L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh) (hF : L.onlineBatch.ann.Fmt) :
    pr ((interact (gameW (hostOf W r₀ h Sm i₀) (boundsW h s1) Gs _)
      (.call (.sess (j + 1) x ()) (afterSess W cA r₀ h w₂ x j t co T))
      (some (c, u, st), T')).map Prod.fst) {a | NoString a.1} ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 := by
  rw [Hiop.Seeded.interact_call, reply_sess W r₀ h Sm i₀ s1 Gs x (j + 1) c u st hc
    (Nat.succ_ne_zero j) hu, PMF.bind_map]
  obtain ⟨A, hs⟩ : ∃ A : (kitW W r₀ h).AB → (oneExternalString L.wordLength L.Symbol).Pos → Option (oneExternalString L.wordLength L.Symbol).Sym,
      (hostOf W r₀ h Sm i₀).session st (j + 1) x () =
      (((kitW W r₀ h).μB 0 (x, L.recOf i₀ (st.2 (j + 1)).1 (st.2 (j + 1)).2)).bind fun a =>
        showAt a a.1.toOption fun r =>
          Sm.B (h.nm j) (x, L.recOf i₀ (st.2 (j + 1)).1 (st.2 (j + 1)).2) r (A a)).map
        fun a => (a, st) := ⟨_, rfl⟩
  rw [hs]
  erw [PMF.bind_map, PMF.bind_bind]
  refine (pr_bind_le_add _ _ _ {a | a.1.toOption = none} (ε := 0) fun a ha hn => ?_).trans ?_
  · obtain ⟨ρ, hρ⟩ := Option.ne_none_iff_exists'.1 hn
    rw [hρ]
    show pr (((Sm.B (h.nm j) _ ρ (A a)).map fun o => (a, o)).bind _) _ ≤ 0
    rw [PMF.bind_map]
    refine pr_bind_le_of_forall _ _ _ fun v hv => ?_
    cases v with
    | none => exact absurd hv (hSm _ _ _ _)
    | some d =>
      refine pr_zero_of_support _ _ fun y hy hbad => ?_
      obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
      have hz' : z ∈ (interact (gameOf W r₀ h Sm i₀ s1 Gs)
          ((pass2A Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2)
            (x, t.ood) (fun _ => t.tree) h.capB W.embE (some d) (h.dressB (h.pvB d.plains) co) a.2
            T).bind fun o' =>
          .halt ((.inr [⟨j, h.nm j, o'.1⟩] :
            Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)), (o'.2, w₂)))
          (some (c, { u with sess := Hiop.bump u.sess (j + 1) }, st), T')).support := hz
      rw [interact_bind] at hz'
      obtain ⟨q, hq, hz''⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz'
      have hsome := pass2_some W cA r₀ h Sm i₀ s1 Gs x t d _ (hlen _) _ a ha hn T _ q hq
      have ez : z = (((.inr [⟨j, h.nm j, q.1.1⟩] :
          Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)), (q.1.2, w₂)), q.2) :=
        (PMF.mem_support_pure_iff _ _).1 hz''
      rw [ez] at hbad
      obtain ⟨l, el, π, hπ, hnone⟩ := hbad
      obtain rfl := Sum.inr.inj el
      obtain rfl := List.mem_singleton.1 hπ
      have hnone' : q.1.1 = none := hnone
      rw [hnone'] at hsome
      cases hsome
  · rw [add_zero]
    exact pass1_ends Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) [] _ h.capB _ hOK hF

/-- A program that samples coins and asks nothing returns, from any table, a value that it can
sample, and the table. -/
theorem onlyCoins_support {S' : OSpec} {γ : Type} {P : γ → Prop} (T : Table S') :
    ∀ c : OComp S' γ, OnlyCoins P c → ∀ y ∈ (c.runLazy T).support, P y.1 ∧ y.2 = T
  | .pure a, hc, y, hy => by
    obtain rfl : y = (a, T) := (PMF.mem_support_pure_iff _ _).1 hy
    exact ⟨hc, rfl⟩
  | .sample n k, hc, y, hy => by
    obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    exact onlyCoins_support T (k r) (hc r) y hr
  | .query _ _ _, hc, _, _ => hc.elim

/-- **One request to the reduction around the simulated game: the proof is produced, except with
probability at most `capFail`**, if the setup was not refused, the game holds all copies, and fewer
than s1 sessions have been run on each. -/
theorem step_none_le (w : StG W) (ts : List (TabW lam L Bd aT aL)) (hw : w.2 = some ts)
    (hts : ts.length = h.M + 1) (x : X)
    (hlen : ∀ pv e, (h.dressB pv (h.coB.e e)).path.length = W.depthReq) (c : ℕ)
    (u : Hiop.UsedR) (st : ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)) (T' : Tb W) (hc : h.M + 1 ≤ c)
    (hu : ∀ e, u.sess e < s1) (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support)
    (hOK : RoundsQueryLayout.OKG L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh) (hF : L.onlineBatch.ann.Fmt) :
    pr ((interact (gameW (hostOf W r₀ h Sm i₀) (boundsW h s1) Gs _)
      (proveStepA W cA r₀ h w [x]) (some (c, u, st), T')).map Prod.fst) {a | NoString a.1} ≤
      capFail L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 := by
  unfold proveStepA
  rw [interact_bind, interact_runLazyA, PMF.bind_map, PMF.map_bind]
  refine pr_bind_le_of_forall _ _ _ fun y hy => ?_
  obtain ⟨⟨hj, e, κ, hco, -⟩, hT⟩ := onlyCoins_support w.1 _ (onlyCoins_coinsP W h) y hy
  obtain ⟨t, ht⟩ : ∃ t, ts[y.1.j]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by rw [hts]; exact hj)⟩
  have hm : (w.2.bind fun ts => ts[y.1.j]?) = some t := by rw [hw]; exact ht
  simp only [Function.comp, hm]
  exact call_none_le W cA r₀ h Sm i₀ s1 Gs w.2 x y.1.j t y.1.co
    (fun pv => by rw [hco]; exact hlen pv e) y.2 c u st T' (by omega) (hu _) hSm hOK hF

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.pr_zero_of_support
#print axioms AtPublicFiles.Shown.onlyCoins_support
#print axioms AtPublicFiles.Shown.step_none_le
#print axioms AtPublicFiles.Shown.call_none_le
#print axioms AtPublicFiles.Shown.reply_sess
#print axioms AtPublicFiles.Shown.pass2_some
