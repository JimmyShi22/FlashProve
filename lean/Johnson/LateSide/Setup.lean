-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Setup.lean: THE TOKEN SIDE's COMMITTER IN MODE I IS THE COMMITTER THAT LAYS LATE,
each secret coin drawn just before its part (commitInward, Johnson/LateSide/Need.lean): the proof of
Spec.setupLate (Johnson/LateSide/Good.lean). Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

Part by part, in the calculus of Compile/DeferRun/Sim.lean, with the invariant HoldsW carried along:
  tabAt, tabAt_stable a table, read off a state's store; it stays as the store grows.
  simBind             sequential composition, what follows taken as a map on pairs.
  simCopies           the coins that are drawn at the start.
  simTab, simTabs     one table, the copies' tables (tabStep; holdsTab).
  simTest, simLinkRun the two kinds of compiled run of the committer (runStep; holdsRun).
  simLink, simLinks   one entry, all entries of the key's list.
  simCommitAt         the committer behind the coins that are drawn at the start.
  setupLate           THE THEOREM.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateSide.Good

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open OnBytes.HopSide OnBytes.LateWorld OnBytes.TokenRel
open _root_.Compile.DeferRun (SimAt)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- a table, read off a state's store -/
def tabAt (pre : Bits) (t : TabT lam L Bd aT aL) {K : ℕ}
    (D' : DSt (typedOracleFamily lam K (typedOracleCarrier L Bd aT aL))) : TabK lam L Bd aT aL :=
  t.toK (fun u => D'.vals.getD u []) pre

theorem tabAt_stable {K : ℕ} {D D' : DSt (typedOracleFamily lam K (typedOracleCarrier L Bd aT aL))}
    (hp : D.vals <+: D'.vals) (pre : Bits) (t : TabT lam L Bd aT aL)
    (ht : ∀ a ∈ t.tree.tok, a.1 < D.vals.length) : tabAt pre t D' = tabAt pre t D :=
  tabK_stable hp pre t ht

/-- Sequential composition (SimAt.bind), what follows taken as a map on pairs. -/
theorem simBind {S' : OSpec} {sp : Split S'} {τ α β α' β' : Type} {tb : DSt S' → τ}
    {D : DSt S'} {ψ : α → DSt S' → β} {R : α → DSt S' → Prop} {κ : PMF (β × τ)}
    {c : Step S' sp α} {g : α → Step S' sp α'} {ψ' : α' → DSt S' → β'}
    {R' : α' → DSt S' → Prop} {k' : β × τ → PMF (β' × τ)} (h1 : SimAt tb c D ψ R κ)
    (h2 : ∀ a D', R a D' → SimAt tb (g a) D' ψ' R' (k' (ψ a D', tb D'))) :
    SimAt tb (c.bind g) D ψ' R' (κ.bind k') :=
  SimAt.bind (k' := fun b T => k' (b, T)) h1 h2

variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  (cA : L.OutOfDomainAnswer → List (Dig lam)) {h : HonestSide lam L Bd aT aL}
  {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB} {bl bf : ℕ}

set_option quotPrecheck false in
/-- the plain state: the oracle's table, exchanged -/
local notation "tbW" =>
  fun D' : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) => Table.via (ghost W) D'.table

/-! ## The coins that are drawn at the start -/

theorem simCopies : ∀ (n : ℕ) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    SimAt tbW (coinsCopiesT W h n) D (fun ds _ => ds) (fun _ D' => D' = D)
      ((copiesInward h n).map fun ds => (ds, Table.via (ghost W) D.table))
  | 0, D => SimAt.pure rfl (PMF.pure_map _ _)
  | n + 1, D => by
    have hn := simCopies n D
    show SimAt _ (Step.sample h.ri.n fun a => Step.sample h.kL.n fun c =>
      (coinsCopiesT W h n).bind fun ds =>
        Step.pure ((⟨h.ri.e a, h.kL.e c⟩ : DrawCopyD L h.KL) :: ds)) D _ _ _
    refine (SimAt.sample fun a => SimAt.sample fun c =>
      SimAt.bind (k' := fun ds T => PMF.pure ((⟨h.ri.e a, h.kL.e c⟩ : DrawCopyD L h.KL) :: ds, T))
        hn fun ds D' hR => SimAt.pure hR rfl).congr ?_
    show ((unif (Fin (h.ri.n + 1))).bind fun a => (unif (Fin (h.kL.n + 1))).bind fun c =>
      (copiesInward h n).bind fun ds => PMF.pure (⟨h.ri.e a, h.kL.e c⟩ :: ds)).map _ = _
    rw [PMF.map_bind]
    refine congrArg _ (funext fun a => ?_)
    rw [PMF.map_bind]
    refine congrArg _ (funext fun c => ?_)
    rw [PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun ds => ?_)
    exact PMF.pure_map _ _

variable (hF : FitAll W S h tl bl bf) (i : I)
include hF

/-! ## Tables -/

theorem simTab (r : L.EncodingRandomness) {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))} (hD : HoldsW W S tl.preE bl bf D Ts) :
    SimAt tbW (tabT W S h tl h.b₀ i r) D (fun t D' => tabAt tl.preE t D')
      (fun t D' => HoldsW W S tl.preE bl bf D' (t.tree :: Ts) ∧ D.vals <+: D'.vals)
      (tabInward W S h i r (Table.via (ghost W) D.table)) where
  law := tabStep W S h tl hF.tok.sl i r (rt_tabT h tl hF.ghost h.b₀ i r) D
  post := fun v hv => by
    obtain ⟨h1, h2⟩ :=
      holdsTab I X lam L Bd aT aL W S h tl bl bf h.b₀ i r D Ts hF.lens.frE hD.1 v hv
    refine ⟨⟨h1, fun T hT => ?_⟩, Life2.vals_prefix true _ D v hv⟩
    rcases List.mem_cons.mp hT with rfl | hT
    · exact h2
    · exact hD.2 T hT

theorem simTabs (ds : List (DrawCopyD L h.KL)) :
    ∀ (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
      (Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))), HoldsW W S tl.preE bl bf D Ts →
      SimAt tbW (tabsT W S h tl i ds) D (fun ts D' => ts.map fun t => tabAt tl.preE t D')
        (fun ts D' => HoldsW W S tl.preE bl bf D' ((ts.map fun t => t.tree) ++ Ts) ∧
          D.vals <+: D'.vals)
        (tabsInward W S h i ds (Table.via (ghost W) D.table)) := by
  induction ds with
  | nil =>
    intro D Ts hD
    exact SimAt.pure ⟨hD, List.prefix_rfl⟩ rfl
  | cons d ds ih =>
    intro D Ts hD
    show SimAt _ ((tabT W S h tl h.b₀ i d.r).bind fun t =>
        (tabsT W S h tl i ds).bind fun ts => Step.pure (t :: ts)) D _ _
      ((tabInward W S h i d.r (Table.via (ghost W) D.table)).bind fun o =>
        (tabsInward W S h i ds o.2).bind fun o' => PMF.pure (o.1 :: o'.1, o'.2))
    refine SimAt.bind
      (k' := fun b T => (tabsInward W S h i ds T).bind fun o' => PMF.pure (b :: o'.1, o'.2))
      (simTab hF i d.r hD) fun t D' hR => ?_
    refine SimAt.bind (k' := fun bs T => PMF.pure (tabAt tl.preE t D' :: bs, T))
      (ih D' (t.tree :: Ts) hR.1) fun ts D'' hR' => ?_
    refine SimAt.pure ⟨hR'.1.sub fun T hT => ?_, hR.2.trans hR'.2⟩ ?_
    · simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hT ⊢
      tauto
    · show PMF.pure (tabAt tl.preE t D' :: ts.map (fun t' => tabAt tl.preE t' D''),
          Table.via (ghost W) D''.table) =
        PMF.pure (tabAt tl.preE t D'' :: ts.map (fun t' => tabAt tl.preE t' D''),
          Table.via (ghost W) D''.table)
      rw [tabAt_stable hR'.2 tl.preE t (HoldsW.lt hR.1 List.mem_cons_self)]

/-! ## The committer's compiled runs -/

theorem simTest (t₁ : TabT lam L Bd aT aL) (κ : h.KT)
    {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))}
    (hD : HoldsW W S tl.preE bl bf D Ts) (h1 : t₁.tree ∈ Ts) :
    SimAt tbW
      (proveC Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
        (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed)
        (L.encodeIndex i t₁.r) (fun _ => t₁.tree) tl.preE (h.st.T i t₁.r t₁.seed κ) tl.T (tl.stT κ) h.capT
        (h.st.stopT i t₁.r t₁.seed)) D (fun a _ => a)
      (fun _ D' => HoldsW W S tl.preE bl bf D' Ts ∧ D.vals <+: D'.vals)
      (testInward W cA h i (tabAt tl.preE t₁ D) κ (Table.via (ghost W) D.table)) where
  law := by
    rw [runStep W Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) _ _ _ _ tl.preE _ tl.T
      (tl.stT κ) h.capT _ h.coT h.rtail h.nR h.nK h.nJ h.fill hF.tok.coT hF.tok.rsT hF.tok.fitT
      (runGood_of hD (batTC L aT) (wTC W) (fun _ => t₁.tree) tl.T (fun _ => h1) hF.ext.T
        hF.lens.frT hF.lens.sT hF.lens.dig)
      (rt_hashT W Tag.test (batTC L aT) (wTC W) W.embT id _ _ _ _ _ _ _ (fun _ => rfl)
        hF.ghost.backT) hF.tok.okT, hF.tok.stT]
    rfl
  post := fun v hv =>
    ⟨⟨holdsRun _ _ lam W.K (typedOracleCarrier L Bd aT aL) bl bf (seedPts W S) Tag.test _ _ (batTC L aT)
        (wTC W) W.embT id _ _ _ _ (fun _ => t₁.tree) tl.preE _ tl.T _ h.capT _ D Ts hF.lens.frT
        hF.lens.sT hF.lens.dig hD.1 (fun _ => h1) v hv, hD.2⟩,
      Life2.vals_prefix true _ D v hv⟩

theorem simLinkRun (t₁ t₂ : TabT lam L Bd aT aL) (κ : h.KL)
    {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))}
    (hD : HoldsW W S tl.preE bl bf D Ts) (h1 : t₁.tree ∈ Ts) (h2 : t₂.tree ∈ Ts) :
    SimAt tbW
      (proveC Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
        (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed).2
          (L.recOf i t₂.r t₂.seed).2)
        (L.recOf i t₁.r t₁.seed, L.recOf i t₂.r t₂.seed) (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
        (fun k => if k = 0 then t₁.tree else t₂.tree) tl.preE
        (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) κ) tl.Lk (tl.stL κ) h.capL
        (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))) D (fun a _ => a)
      (fun _ D' => HoldsW W S tl.preE bl bf D' Ts ∧ D.vals <+: D'.vals)
      (linkInward W cA h i (tabAt tl.preE t₁ D) (tabAt tl.preE t₂ D) κ
        (Table.via (ghost W) D.table)) := by
  have hx : ∀ k : ℕ, (if k = 0 then t₁.tree else t₂.tree) ∈ Ts := fun k => by
    by_cases hk : k = 0
    · rw [if_pos hk]; exact h1
    · rw [if_neg hk]; exact h2
  refine ⟨?_, fun v hv =>
    ⟨⟨holdsRun _ _ lam W.K (typedOracleCarrier L Bd aT aL) bl bf (seedPts W S) Tag.link _ _ (batLC L aL)
        (wLC W) W.embL id _ _ _ _ (fun k => if k = 0 then t₁.tree else t₂.tree) tl.preE _ tl.Lk _
        h.capL _ D Ts hF.lens.frL hF.lens.sL hF.lens.dig hD.1 hx v hv, hD.2⟩,
      Life2.vals_prefix true _ D v hv⟩⟩
  rw [runStep W Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) _ _ _ _ tl.preE _ tl.Lk
    (tl.stL κ) h.capL _ h.coL h.rtail h.nR h.nK h.nJ h.fill hF.tok.coL hF.tok.rsL hF.tok.fitL
    (runGood_of hD (batLC L aL) (wLC W) (fun k => if k = 0 then t₁.tree else t₂.tree) tl.Lk hx
      hF.ext.Lk hF.lens.frL hF.lens.sL hF.lens.dig)
    (rt_hashT W Tag.link (batLC L aL) (wLC W) W.embL id _ _ _ _ _ _ _ (fun _ => rfl)
      hF.ghost.backL) hF.tok.okL, hF.tok.stL]
  have ex : (fun k : ℕ => (if k = 0 then t₁.tree else t₂.tree).toK
      (fun w => D.vals.getD w []) tl.preE) =
      fun k => if k = 0 then (tabAt tl.preE t₁ D).tree else (tabAt tl.preE t₂ D).tree :=
    funext fun k => by
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk]; rfl
      · rw [if_neg hk, if_neg hk]; rfl
  rw [ex]
  rfl

theorem simLink (t₁ t₂ : TabT lam L Bd aT aL) (d : DrawCopyD L h.KL)
    {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))}
    (hD : HoldsW W S tl.preE bl bf D Ts) (h1 : t₁.tree ∈ Ts) (h2 : t₂.tree ∈ Ts) :
    SimAt tbW (linkT W cA h tl i t₁ t₂ d) D (fun e _ => e)
      (fun _ D' => HoldsW W S tl.preE bl bf D' Ts ∧ D.vals <+: D'.vals)
      ((linkInward W cA h i (tabAt tl.preE t₁ D) (tabAt tl.preE t₂ D) d.κ
        (Table.via (ghost W) D.table)).bind fun o =>
          PMF.pure ((t₂.tree.root, L.recOf i t₂.r t₂.seed, o.1), o.2)) :=
  SimAt.bind (k' := fun b T => PMF.pure ((t₂.tree.root, L.recOf i t₂.r t₂.seed, b), T))
    (simLinkRun cA hF i t₁ t₂ d.κ hD h1 h2) fun _ _ hR => SimAt.pure hR rfl

theorem simLinks (t₁ : TabT lam L Bd aT aL) {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))}
    (h1 : t₁.tree ∈ Ts) (l : List (DrawCopyD L h.KL × TabT lam L Bd aT aL)) :
    ∀ (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))), HoldsW W S tl.preE bl bf D Ts →
      (∀ a ∈ l, a.2.tree ∈ Ts) →
      SimAt tbW (linksT W cA h tl i t₁ l) D (fun es _ => es)
        (fun _ D' => HoldsW W S tl.preE bl bf D' Ts ∧ D.vals <+: D'.vals)
        (linksInward W cA h i (tabAt tl.preE t₁ D) (l.map fun a => (a.1, tabAt tl.preE a.2 D))
          (Table.via (ghost W) D.table)) := by
  induction l with
  | nil =>
    intro D hD _
    exact SimAt.pure ⟨hD, List.prefix_rfl⟩ rfl
  | cons a l ih =>
    intro D hD hl
    show SimAt _ ((linkT W cA h tl i t₁ a.2 a.1).bind fun e =>
      (linksT W cA h tl i t₁ l).bind fun es => Step.pure (e :: es)) D _ _ _
    refine (SimAt.bind
      (k' := fun e T => (linksInward W cA h i (tabAt tl.preE t₁ D)
        (l.map fun a' => (a'.1, tabAt tl.preE a'.2 D)) T).bind fun o' =>
          PMF.pure (e :: o'.1, o'.2))
      (simLink cA hF i t₁ a.2 a.1 hD h1 (hl a List.mem_cons_self)) fun e D' hR => ?_).congr ?_
    · have e1 : linksInward W cA h i (tabAt tl.preE t₁ D)
          (l.map fun a' => (a'.1, tabAt tl.preE a'.2 D)) (Table.via (ghost W) D'.table) =
          linksInward W cA h i (tabAt tl.preE t₁ D')
            (l.map fun a' => (a'.1, tabAt tl.preE a'.2 D')) (Table.via (ghost W) D'.table) := by
        rw [tabAt_stable hR.2 tl.preE t₁ (HoldsW.lt hD h1)]
        refine congrArg (fun z => linksInward W cA h i (tabAt tl.preE t₁ D) z _)
          (List.map_congr_left fun a' ha' => ?_)
        rw [tabAt_stable hR.2 tl.preE a'.2 (HoldsW.lt hD (hl a' (List.mem_cons_of_mem _ ha')))]
      refine SimAt.bind (k' := fun es T => PMF.pure (e :: es, T))
        ((ih D' hR.1 fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')).congr e1)
        fun es D'' hR' => SimAt.pure ⟨hR'.1, hR.2.trans hR'.2⟩ rfl
    · show (linkInward W cA h i (tabAt tl.preE t₁ D) (tabAt tl.preE a.2 D) a.1.κ
          (Table.via (ghost W) D.table)).bind _ = _
      rw [PMF.bind_bind]
      refine congrArg _ (funext fun o => ?_)
      rw [PMF.pure_bind]
      rfl

/-! ## The committer -/

theorem simCommitAt (d : DrawCD L h.KT h.KL) {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hD : HoldsW W S tl.preE bl bf D []) :
    SimAt tbW (commitAtT W S cA h tl i d) D (fun o D' => (o.1, iskOf tl.preE o.2 D'.vals))
      (fun o D' => GoodW W S tl.preE bl bf (some o.2) D')
      (commitAtInward W S cA h i d (Table.via (ghost W) D.table)) := by
  unfold commitAtT commitAtInward
  refine simBind (simTab hF i d.r hD) fun t₁ D₁ hR₁ => ?_
  dsimp only
  refine simBind (simTabs hF i d.copies D₁ [t₁.tree] hR₁.1) fun ts D₂ hR₂ => ?_
  dsimp only
  have m₁ : t₁.tree ∈ (ts.map fun t => t.tree) ++ [t₁.tree] :=
    List.mem_append_right _ List.mem_cons_self
  have s₁ : tabAt tl.preE t₁ D₂ = tabAt tl.preE t₁ D₁ :=
    tabAt_stable hR₂.2 tl.preE t₁ (HoldsW.lt hR₁.1 List.mem_cons_self)
  have hz : ∀ a' ∈ d.copies.zip ts, a'.2.tree ∈ (ts.map fun t => t.tree) ++ [t₁.tree] :=
    fun a' ha' => List.mem_append_left _ (List.mem_map.mpr ⟨a'.2, (List.of_mem_zip ha').2, rfl⟩)
  refine simBind ((simTest cA hF i t₁ d.κ hR₂.1 m₁).congr (by rw [s₁])) fun a D₃ hR₃ => ?_
  dsimp only
  have e3 : linksInward W cA h i (tabAt tl.preE t₁ D₁)
      (d.copies.zip (ts.map fun t => tabAt tl.preE t D₂)) (Table.via (ghost W) D₃.table) =
      linksInward W cA h i (tabAt tl.preE t₁ D₃)
        ((d.copies.zip ts).map fun a' => (a'.1, tabAt tl.preE a'.2 D₃))
        (Table.via (ghost W) D₃.table) := by
    rw [tabAt_stable hR₃.2 tl.preE t₁ (HoldsW.lt hR₂.1 m₁), s₁]
    refine congrArg (fun z => linksInward W cA h i (tabAt tl.preE t₁ D₁) z _) ?_
    rw [List.zip_map_right]
    refine List.map_congr_left fun a' ha' => ?_
    show (a'.1, tabAt tl.preE a'.2 D₂) = (a'.1, tabAt tl.preE a'.2 D₃)
    rw [tabAt_stable hR₃.2 tl.preE a'.2 (HoldsW.lt hR₂.1 (hz a' ha'))]
  refine simBind ((simLinks cA hF i t₁ m₁ (d.copies.zip ts) D₃ hR₃.1 hz).congr e3)
    fun ls D₄ hR₄ => ?_
  dsimp only
  refine SimAt.pure (hR₄.1.sub fun T hT => List.mem_append_left _ hT) ?_
  refine congrArg (fun z : List (TabK lam L Bd aT aL) =>
    PMF.pure (((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, a, ls⟩ : FullKey lam L aT aL),
      (⟨i, z⟩ : Isk lam L Bd aT aL)), Table.via (ghost W) D₄.table))
    (List.map_congr_left fun t ht => ?_)
  exact (tabAt_stable (hR₃.2.trans hR₄.2) tl.preE t (HoldsW.lt hR₂.1
    (List.mem_append_left _ (List.mem_map.mpr ⟨t, ht, rfl⟩)))).symm

omit hF in
/-- **The token side's committer in mode I is the committer that lays late.** -/
theorem setupLate : Spec.setupLate := by
  intro I X lam L Bd aT aL W S cA h tl bl bf i D hF hD
  show SimAt _ (Step.sample h.ri.n fun a => Step.sample h.kT.n fun c =>
    ((coinsCopiesT W h (h.M + 1)).bind fun ds =>
      Step.pure (⟨h.ri.e a, h.kT.e c, ds⟩ : DrawCD L h.KT h.KL)).bind fun d =>
        commitAtT W S cA h tl i d) D _ _ _
  refine (SimAt.sample fun a => SimAt.sample fun c =>
    SimAt.bind (k' := fun d T => commitAtInward W S cA h i d T)
      (SimAt.bind (ψ' := fun d _ => d) (R' := fun _ D' => D' = D)
        (k' := fun ds T => PMF.pure ((⟨h.ri.e a, h.kT.e c, ds⟩ : DrawCD L h.KT h.KL), T))
        (simCopies (h.M + 1) D) fun ds D' hR => SimAt.pure hR rfl)
      fun d D' hR => by
        obtain rfl : D' = D := hR
        exact simCommitAt cA hF i d hD).congr ?_
  show ((unif (Fin (h.ri.n + 1))).bind fun a => (unif (Fin (h.kT.n + 1))).bind fun c =>
    (copiesInward h (h.M + 1)).bind fun ds =>
      commitAtInward W S cA h i ⟨h.ri.e a, h.kT.e c, ds⟩ (Table.via (ghost W) D.table)) = _
  refine congrArg _ (funext fun a => congrArg _ (funext fun c => ?_))
  rw [PMF.bind_bind, PMF.bind_map]
  refine congrArg _ (funext fun ds => ?_)
  simp only [Function.comp, PMF.pure_bind]

end OnBytes.LateSide

#print axioms OnBytes.LateSide.setupLate
