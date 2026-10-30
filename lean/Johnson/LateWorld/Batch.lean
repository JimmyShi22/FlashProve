-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Batch.lean: THE MAP OF STATES COMMUTES WITH A BATCH AND WITH AN ORACLE QUERY, and
these moves keep the invariant; so after a good setup the reduction around the real game and the
honest side that lays late and counts give an admissible adversary the same law of output.

This file states no goal of the release: one step of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean). The head of Johnson/LateWorld/Steps.lean says what the two
challengers, the map (toC) and the invariant (InvG) are.

Main names (namespace OnBytes.LateWorld).
  bind_enum, ctr_bump, coinsP_run, lateAt_some   small tools.
  latB         the honest session laid late, at the letters that the map of states gives.
  place_eq     at a drawn place: served (the session lemma) or refused.
  batch_one    a batch of one own request.
  wrap_one, wrap_quiet, late_quiet, batch_cases, sess_keeps, wrap_answer, lateC_answer   unfoldings
               and cases.
  batch_toC, batch_inv, answer_toC, answer_inv   the map of states commutes with a batch and with an
               oracle query; both keep the invariant.
  after_setup  THE STEP.

Limits. It says nothing of the setup.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Steps

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn GAdm asW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## Small tools -/

/-- A draw through an enumeration that lists each member once is a uniform draw. -/
theorem bind_enum {β γ : Type} [Fintype β] [Nonempty β] (e : Enum β) (he : e.OK)
    (F : β → PMF γ) : ((unif (Fin (e.n + 1))).bind fun c => F (e.e c)) = (unif β).bind F := by
  rw [← map_unif_of_bijective he, PMF.bind_map]
  rfl

/-- the game's count of sessions, one more on the table number j + 1, as counters of places -/
theorem ctr_bump {M : ℕ} (us : ℕ → ℕ) (j : Fin (M + 1)) :
    (fun j' : Fin (M + 1) => Hiop.bump us (j.val + 1) (j'.val + 1)) =
      Function.update (fun j' : Fin (M + 1) => us (j'.val + 1)) j (us (j.val + 1) + 1) := by
  funext j'
  by_cases h : j' = j
  · subst h
    simp [Hiop.bump]
  · have h' : j'.val + 1 ≠ j.val + 1 := fun e => h (Fin.ext (Nat.succ.inj e))
    simp [Hiop.bump, Function.update_of_ne h, Function.update_of_ne h']

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} (r₀ : L.Rec) {a : AtRecs lam L Bd aT aL} {Gs : L.OutOfDomainSeed → Prop}
  (s1 : ℕ) (i : I)

theorem coinsP_run (h : HonestSide lam L Bd aT aL) (T : Tb W) :
    (coinsP W h).runLazy T =
      (unif (Fin (h.M + 1))).bind fun j => (unif (Fin (h.kB.n + 1))).bind fun c =>
        (unif (Fin (h.coB.n + 1))).bind fun e => PMF.pure (⟨j.val, h.kB.e c, h.coB.e e⟩, T) := by
  simp only [coinsP, OComp.runLazy]

theorem lateAt_some (h : HonestSide lam L Bd aT aL) (isk : Isk lam L Bd aT aL) (x : X)
    (d : DrawP lam L Bd aT aL h.KB) (T : Tb W) (t : TabK lam L Bd aT aL)
    (ht : isk.copies[d.j]? = some t) :
    lateAt W cA r₀ h isk x d T =
      (lateBA W cA r₀ (fun _ => t.tree) (h.dressB (h.rvB d.κ) d.co) h.capB t.tree.root x
        (L.recOf isk.i t.r t.seed) (L.encodeIndex isk.i t.r) (h.st.stopB isk.i t.r t.seed x (h.nm d.j))
        (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ) T).map fun o => (⟨d.j, h.nm d.j, o.1⟩, o.2) := by
  simp only [lateAt, ht]

/-- The honest session laid late, on the copy at the place j whose table the reduction keeps as t
and whose (randomness, seed) the game keeps as rs; co: the run's coins as drawn; κ: the strategy's.
-/
def latB (t : TabW lam L Bd aT aL) (rs : L.EncodingRandomness × L.OutOfDomainSeed) (j : ℕ) (x : X) (T : Tb W)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (κ : a.Hs.B.Coin) :
    PMF (Option (OneProtocolProof lam L.onlineBatch) × Tb W) :=
  lateBA W cA r₀ (fun _ => realTree W a.b₀ (L.encodeIndex i rs.1) t.tree)
    (a.side.dressB (a.side.rvB κ) co) a.side.capB t.tree.root x (L.recOf i rs.1 rs.2)
    (L.encodeIndex i rs.1) (a.side.st.stopB i rs.1 rs.2 x (a.nm j)) (a.side.st.B i rs.1 rs.2 x (a.nm j) κ) T

/-! ## At a drawn place -/

theorem place_eq {ok : I → Prop} {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i)
    (T : Tb W)
    (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W)
    (hlen : ts.length = a.M + 1) (hc : ts.length ≤ c)
    (hood : ∀ e t, ts[e]? = some t → t.ood = L.recOf i (st.2 (e + 1)).1 (st.2 (e + 1)).2) (x : X)
    (j : Fin (a.side.M + 1)) :
    (((unif (Fin (a.side.kB.n + 1))).bind fun cc => (unif (Fin (a.side.coB.n + 1))).bind fun e =>
        (runG W r₀ a Gs s1 i
          (sessA' W cA r₀ a.side (T, some ts) x (⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩, T)
            (ts[j.val]?)) (some (c, u, st), Tg)).map fun z => (z.1.1, (z.1.2, z.2))).map
      (Prod.map id (toC W a i))) =
      if u.sess (j.val + 1) < s1 then
        (sessAt W cA r₀ a.side ⟨i, realCopies W a i st.2 1 ts⟩ x T j).map fun o =>
          (.inr [o.1], ((some ⟨i, realCopies W a i st.2 1 ts⟩, o.2),
            Function.update (fun j' : Fin (a.side.M + 1) => u.sess (j'.val + 1)) j
              (u.sess (j.val + 1) + 1)))
      else PMF.pure (.inr [⟨j.val, a.side.nm j.val, none⟩],
        ((some ⟨i, realCopies W a i st.2 1 ts⟩, T), fun j' => u.sess (j'.val + 1))) := by
  have hjl : j.val < ts.length := by
    rw [hlen]
    exact j.isLt
  obtain ⟨t, ht⟩ : ∃ t, ts[j.val]? = some t := ⟨ts[j.val], List.getElem?_eq_getElem hjl⟩
  have hb1 : (boundsW a.side s1).sess (j.val + 1) = s1 := by
    show (if j.val + 1 = 0 then 0 else s1) = s1
    exact if_neg (Nat.succ_ne_zero j.val)
  have hoo := hood j.val t ht
  rw [ht]
  by_cases hj : u.sess (j.val + 1) < s1
  · rw [if_pos hj]
    -- what both sides come to
    let F : Option (OneProtocolProof lam L.onlineBatch) × Tb W →
        GIn (FullKey lam L aT aL) (RequestProof lam L) × StC W a.side := fun o' =>
      (.inr [⟨j.val, a.side.nm j.val, o'.1⟩], ((some ⟨i, realCopies W a i st.2 1 ts⟩, o'.2),
        Function.update (fun j' : Fin (a.side.M + 1) => u.sess (j'.val + 1)) j
          (u.sess (j.val + 1) + 1)))
    have h1 : ∀ cc e, ((runG W r₀ a Gs s1 i
        (sessA' W cA r₀ a.side (T, some ts) x (⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩, T)
          (some t)) (some (c, u, st), Tg)).map fun z => (z.1.1, (z.1.2, z.2))).map
          (Prod.map id (toC W a i)) =
        ((unif a.Hs.B.Coin).bind fun κ =>
          latB (cA := cA) r₀ i t (st.2 (j.val + 1)) j.val x T (a.side.coB.e e) κ).map F := by
      intro cc e
      rw [sessA_served r₀ s1 i T ts c u st Tg x ⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩ t
        (Nat.succ_le_of_lt (lt_of_lt_of_le hjl hc)) (by rw [hb1]; exact hj), hoo]
      have hb := sess_branch r₀ i hP hi t (st.2 (j.val + 1)).1 (st.2 (j.val + 1)).2 j.val x
        (a.side.coB.e e) (hP.pathB e) T
      show _ = PMF.map F ((unif a.Hs.B.Coin).bind fun κ =>
        lateBA W cA r₀ (fun _ => realTree W a.b₀ (L.encodeIndex i (st.2 (j.val + 1)).1) t.tree)
          (a.side.dressB (a.side.rvB κ) (a.side.coB.e e)) a.side.capB t.tree.root x
          (L.recOf i (st.2 (j.val + 1)).1 (st.2 (j.val + 1)).2) (L.encodeIndex i (st.2 (j.val + 1)).1)
          (a.side.st.stopB i (st.2 (j.val + 1)).1 (st.2 (j.val + 1)).2 x (a.nm j.val))
          (a.side.st.B i (st.2 (j.val + 1)).1 (st.2 (j.val + 1)).2 x (a.nm j.val) κ) T)
      rw [← hb]
      simp only [PMF.map_bind, PMF.map_comp]
      refine congrArg _ (funext fun v => congrArg (fun G => PMF.map G _) (funext fun o' => ?_))
      exact Prod.ext rfl (Prod.ext rfl (ctr_bump u.sess j))
    have hk : (realCopies W a i st.2 1 ts)[j.val]? =
        some ⟨(st.2 (j.val + 1)).1, realTree W a.b₀ (L.encodeIndex i (st.2 (j.val + 1)).1) t.tree,
          (st.2 (j.val + 1)).2⟩ := by
      rw [realCopies_get, ht, Nat.add_comm 1 j.val]
      rfl
    have h2 : ∀ cc e, (lateAt W cA r₀ a.side ⟨i, realCopies W a i st.2 1 ts⟩ x
        ⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩ T).map (fun o =>
          ((.inr [o.1], ((some ⟨i, realCopies W a i st.2 1 ts⟩, o.2),
            Function.update (fun j' : Fin (a.side.M + 1) => u.sess (j'.val + 1)) j
              (u.sess (j.val + 1) + 1))) :
            GIn (FullKey lam L aT aL) (RequestProof lam L) × StC W a.side)) =
        (latB (cA := cA) r₀ i t (st.2 (j.val + 1)) j.val x T (a.side.coB.e e)
          (a.side.kB.e cc)).map F := by
      intro cc e
      rw [lateAt_some r₀ a.side ⟨i, realCopies W a i st.2 1 ts⟩ x
        ⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩ T _ hk, PMF.map_comp]
      rfl
    simp only [PMF.map_bind, h1, sessAt, h2, PMF.bind_const]
    rw [PMF.bind_comm]
    exact (bind_enum (β := a.Hs.B.Coin) a.kB hP.kB fun κ =>
      (unif (Fin (a.side.coB.n + 1))).bind fun e =>
      (latB (cA := cA) r₀ i t (st.2 (j.val + 1)) j.val x T (a.side.coB.e e) κ).map F).symm
  · rw [if_neg hj]
    have h1 : ∀ cc e, runG W r₀ a Gs s1 i
        (sessA' W cA r₀ a.side (T, some ts) x (⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩, T)
          (some t)) (some (c, u, st), Tg) =
        PMF.pure ((.inr [⟨j.val, a.side.nm j.val, none⟩], (T, some ts)), (some (c, u, st), Tg)) :=
      fun cc e => sessA_refused r₀ s1 i T ts c u st Tg x
        ⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩ t (by rw [hb1]; exact hj)
    simp only [h1, PMF.pure_map, PMF.bind_const]
    rfl

/-! ## A batch -/

/-- The reduction's reply to a batch of one own request, unfolded. -/
theorem wrap_one (T : Tb W) (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR) (st : StH L)
    (Tg : Tb W) (x : X) :
    repW W S cA r₀ a Gs s1 i ((T, some ts), (some (c, u, st), Tg)) (.batch [(x, (), true)]) =
      (unif (Fin (a.side.M + 1))).bind fun j => (unif (Fin (a.side.kB.n + 1))).bind fun cc =>
        (unif (Fin (a.side.coB.n + 1))).bind fun e =>
          (runG W r₀ a Gs s1 i
            (sessA' W cA r₀ a.side (T, some ts) x (⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩, T)
              (ts[j.val]?)) (some (c, u, st), Tg)).map fun z => (z.1.1, (z.1.2, z.2)) := by
  rw [repW_batch]
  show (runG W r₀ a Gs s1 i (proveStepA W cA r₀ a.side (T, some ts) [x]) (some (c, u, st), Tg)).map
    (fun z => (z.1.1, (z.1.2, z.2))) = _
  rw [proveStepA_one, runG_bind, runG_lazy, coinsP_run]
  simp only [PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.bind_map, PMF.pure_map,
    Function.comp_def]
  rfl

theorem batch_one {ok : I → Prop} {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i)
    (T : Tb W)
    (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W)
    (hlen : ts.length = a.M + 1) (hc : ts.length ≤ c)
    (hood : ∀ e t, ts[e]? = some t → t.ood = L.recOf i (st.2 (e + 1)).1 (st.2 (e + 1)).2) (x : X) :
    (repW W S cA r₀ a Gs s1 i ((T, some ts), (some (c, u, st), Tg))
        (.batch [(x, (), true)])).map (Prod.map id (toC W a i)) =
      replyC W S cA r₀ a.side s1 i
        ((some ⟨i, realCopies W a i st.2 1 ts⟩, T), fun j => u.sess (j.val + 1))
        (.batch [(x, (), true)]) (some (⟨i, realCopies W a i st.2 1 ts⟩, x)) := by
  rw [wrap_one, PMF.map_bind]
  exact congrArg _ (funext fun j => place_eq r₀ s1 i hP hi T ts c u st Tg hlen hc hood x j)

/-- A batch without an own slot: the reduction replies with no proof and does nothing. -/
theorem wrap_quiet (s : StWG W) (b : ZKCP.Gen.Batch X Unit) (hb : b.ownX = []) :
    repW W S cA r₀ a Gs s1 i s (.batch b) = PMF.pure (.inr [], s) := by
  rw [repW_batch, hb]
  show (runG W r₀ a Gs s1 i
    (.halt ((Sum.inr [] : GIn (FullKey lam L aT aL) (RequestProof lam L)), s.1)) s.2).map _ = _
  rw [runG_halt, PMF.pure_map]

/-- The same for the honest side that counts, at the two batches of at most one slot without an own
slot. -/
theorem late_quiet (k : Isk lam L Bd aT aL) (T : Tb W) (ct : Fin (a.side.M + 1) → ℕ)
    (b : ZKCP.Gen.Batch X Unit) (hb : b = [] ∨ ∃ x, b = [(x, (), false)]) :
    replyC W S cA r₀ a.side s1 i ((some k, T), ct) (.batch b) none =
      PMF.pure (.inr [], ((some k, T), ct)) := by
  rcases hb with rfl | ⟨x, rfl⟩
  · exact (congrArg (PMF.map _) (PMF.pure_map _ _)).trans (PMF.pure_map _ _)
  · exact (congrArg (PMF.map _) (PMF.pure_map _ _)).trans (PMF.pure_map _ _)

/-- a batch of at most one slot -/
theorem batch_cases (b : ZKCP.Gen.Batch X Unit) (hb : b.length ≤ 1) :
    b = [] ∨ (∃ x, b = [(x, (), false)]) ∨ ∃ x, b = [(x, (), true)] := by
  match b, hb with
  | [], _ => exact Or.inl rfl
  | [(x, (), false)], _ => exact Or.inr (Or.inl ⟨x, rfl⟩)
  | [(x, (), true)], _ => exact Or.inr (Or.inr ⟨x, rfl⟩)
  | _ :: _ :: _, h => exact absurd h (by simp)

/-- **The map of states commutes with a batch of at most one slot.** -/
theorem batch_toC {ok : I → Prop} {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i)
    (s : StWG W) (hs : InvG W a i s)
    (b : ZKCP.Gen.Batch X Unit) (hb : b.length ≤ 1) :
    (repW W S cA r₀ a Gs s1 i s (.batch b)).map (Prod.map id (toC W a i)) =
      replyC W S cA r₀ a.side s1 i (toC W a i s) (.batch b)
        (oneOwn (.batch b) (toC W a i s).1.1) := by
  obtain ⟨T, ts, c, u, st, Tg, rfl, hlen, hc, hood⟩ := hs
  rcases batch_cases b hb with rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [wrap_quiet r₀ s1 i _ _ rfl, PMF.pure_map]
    exact (late_quiet r₀ s1 i _ T _ _ (Or.inl rfl)).symm
  · rw [wrap_quiet r₀ s1 i _ _ rfl, PMF.pure_map]
    exact (late_quiet r₀ s1 i _ T _ _ (Or.inr ⟨x, rfl⟩)).symm
  · exact batch_one r₀ s1 i hP hi T ts c u st Tg hlen hc hood x

/-- what a session leaves of the reduction's and the game's states -/
theorem sess_keeps (T : Tb W) (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR)
    (st : StH L) (Tg : Tb W) (x : X) (d : DrawP lam L Bd aT aL a.side.KB) (hd : d.j + 1 ≤ c)
    (ot : Option (TabW lam L Bd aT aL)) :
    ∀ z ∈ (runG W r₀ a Gs s1 i (sessA' W cA r₀ a.side (T, some ts) x (d, T) ot)
        (some (c, u, st), Tg)).support,
      ∃ (T' : Tb W) (u' : Hiop.UsedR), z.1.2 = (T', some ts) ∧ z.2 = (some (c, u', st), Tg) := by
  intro z hz
  cases ot with
  | none =>
    rw [sessA', runG_halt, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨T, u, rfl, rfl⟩
  | some t =>
    by_cases hu : u.sess (d.j + 1) < (boundsW a.side s1).sess (d.j + 1)
    · rw [sessA_served r₀ s1 i T ts c u st Tg x d t hd hu] at hz
      obtain ⟨v, -, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
      obtain ⟨o', -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      exact ⟨o'.2, _, rfl, rfl⟩
    · rw [sessA_refused r₀ s1 i T ts c u st Tg x d t hu, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨T, u, rfl, rfl⟩

/-- **A batch keeps the invariant.** -/
theorem batch_inv (s : StWG W) (hs : InvG W a i s) (b : ZKCP.Gen.Batch X Unit)
    (hb : b.length ≤ 1) :
    ∀ y ∈ (repW W S cA r₀ a Gs s1 i s (.batch b)).support, InvG W a i y.2 := by
  obtain ⟨T, ts, c, u, st, Tg, rfl, hlen, hc, hood⟩ := hs
  intro y hy
  rcases batch_cases b hb with rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [wrap_quiet r₀ s1 i _ _ rfl, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨T, ts, c, u, st, Tg, rfl, hlen, hc, hood⟩
  · rw [wrap_quiet r₀ s1 i _ _ rfl, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨T, ts, c, u, st, Tg, rfl, hlen, hc, hood⟩
  · rw [wrap_one] at hy
    obtain ⟨j, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    obtain ⟨cc, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    obtain ⟨e, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    have hjl : j.val < ts.length := by
      rw [hlen]
      exact j.isLt
    obtain ⟨T', u', h1, h2⟩ := sess_keeps r₀ s1 i T ts c u st Tg x
      ⟨j.val, a.side.kB.e cc, a.side.coB.e e⟩ (Nat.succ_le_of_lt (lt_of_lt_of_le hjl hc)) _ z hz
    exact ⟨T', ts, c, u', st, Tg, Prod.ext h1 h2, hlen, hc, hood⟩

/-! ## An oracle query -/

/-- The reduction's answer to an oracle query, unfolded: lazy sampling from its table. -/
theorem wrap_answer (s : StWG W) (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o) :
    ansW W S cA r₀ a Gs s1 i s o q =
      (lazyAnswer s.1.1 o q).map fun p => (p.1, ((p.2, s.1.2), s.2)) := by
  show (runG W r₀ a Gs s1 i
    ((HandlerA.lazy s.1.1 o q).bind fun p => .halt (p.1, (p.2, s.1.2))) s.2).map
    (fun z => (z.1.1, (z.1.2, z.2))) = _
  have e : runG W r₀ a Gs s1 i (HandlerA.lazy s.1.1 o q) s.2 =
      (lazyAnswer s.1.1 o q).map fun p => (p, s.2) :=
    realises_lazy (gameG W r₀ a Gs s1 i) s.2 s.1.1 o q
  rw [runG_bind, e, PMF.bind_map]
  simp only [Function.comp_def, runG_halt]
  exact map_map_eq _ _ _ _ fun _ => rfl

theorem answer_toC (s : StWG W) (hs : InvG W a i s) (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o) :
    (ansW W S cA r₀ a Gs s1 i s o q).map (Prod.map id (toC W a i)) =
      ((lazyAnswer (toC W a i s).1.2 o q).map fun p =>
        (p.1, (((toC W a i s).1.1, p.2), (toC W a i s).2))) := by
  obtain ⟨T, ts, c, u, st, Tg, rfl, -, -, -⟩ := hs
  rw [wrap_answer]
  exact map_map_eq _ _ _ _ fun _ => rfl

theorem answer_inv (s : StWG W) (hs : InvG W a i s) (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o) :
    ∀ y ∈ (ansW W S cA r₀ a Gs s1 i s o q).support, InvG W a i y.2 := by
  obtain ⟨T, ts, c, u, st, Tg, rfl, hlen, hc, hood⟩ := hs
  intro y hy
  rw [wrap_answer] at hy
  obtain ⟨p, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  exact ⟨p.2, ts, c, u, st, Tg, rfl, hlen, hc, hood⟩

/-- the answer of the honest side that counts, unfolded -/
theorem lateC_answer (h : HonestSide lam L Bd aT aL) (s : StC W h)
    (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o) :
    (lateC W S cA r₀ h s1 i).answer s o q =
      (lazyAnswer s.1.2 o q).map fun p => (p.1, ((s.1.1, p.2), s.2)) :=
  map_map_eq _ _ _ _ fun _ => rfl

/-! ## The step -/

/-- **After a good setup** an admissible adversary has the same law of output against the reduction
around the real game and against the honest side that lays late and counts. -/
theorem after_setup {ok : I → Prop} {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i)
    {α : Type}
    {okb : ZKCP.Gen.Batch X Unit → Prop} (hok : ∀ b, okb b → b.length ≤ 1)
    (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ) (hA : GAdm okb A true n) (s : StWG W)
    (hs : InvG W a i s) :
    (interact (wrapG W S cA r₀ a Gs s1 i) A s).map Prod.fst =
      (interact (lateC W S cA r₀ a.side s1 i) A (toC W a i s)).map Prod.fst :=
  DeferRun.lump_gAdm_fst okb (wrapG W S cA r₀ a Gs s1 i) (lateC W S cA r₀ a.side s1 i) (toC W a i)
    (fun f s => f = true ∧ InvG W a i s)
    (fun _ s o q h => (answer_toC r₀ s1 i s h.2 o q).trans
      (lateC_answer r₀ s1 i a.side (toC W a i s) o q).symm)
    (fun _ s o q h y hy => ⟨h.1, answer_inv r₀ s1 i s h.2 o q y hy⟩)
    (fun _ h => absurd h.1 Bool.false_ne_true)
    (fun _ h => absurd h.1 Bool.false_ne_true)
    (fun s b hb h => batch_toC r₀ s1 i hP hi s h.2 b (hok b hb))
    (fun s b hb h y hy => ⟨rfl, batch_inv r₀ s1 i s h.2 b (hok b hb) y hy⟩)
    A true n s hA ⟨rfl, hs⟩

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.batch_toC
#print axioms OnBytes.LateWorld.batch_inv
#print axioms OnBytes.LateWorld.after_setup
