-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/TabList.lean: THE MAKING OF ALL TABLES WITH THEIR LEAVES LAID LATE: the proofs of
Spec.tabsBodies and Spec.seedsBadList (Johnson/LateWorld/SpecTabList.lean) and of Spec.phaseBad
(Johnson/LateWorld/SpecSetup.lean). Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

The parts of the setup are maps from a table of answers to a law on (value, table of answers), in
sequence (Ker, Johnson/TokenSide2/Ker.lean). tabK and tabsK say tabBodies
(Johnson/LateWorld/Tables.lean) and its like for a list in that language. The bounds: one table
costs δ (seedsBad); the property SeedsIn of the table of answers is carried from each table to the
next; the costs add up.

Main names (namespace OnBytes.LateWorld).
  tabK, tabsK, tabsFR_nil, tabsFR_cons   the makings of tables as maps in sequence.
  tabsBodies, seedsBadList   THE THEOREMS ON A LIST.
  coinsC_keeps, coinsC_len, tabsFR_len, phase1_len   the committer's coins leave the table of
      answers as it is; there are M + 1 copies' coins, and as many copies' trees.
  coinsC_coins, phase1_coins   the coins of the compiled runs are members of the honest side's
      lists.
  phaseBad     THE THEOREM ON THE WHOLE TABLES' PHASE.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecSetup
import Johnson.LateWorld.Tables
import Johnson.TokenSide2.Ker
import Johnson.TokenSide2.Same

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Rom.Derive (Avoids.bind runLazy_avoids)

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-! ## The makings of tables as maps in sequence -/

/-- tabBodies, in the language of maps in sequence. -/
theorem tabK (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    Ker.ofDefer mkTab (tabO W S b₀ i r s) = Ker.bind (tabFR W S b₀ s) fun o =>
      Ker.pure (⟨r, realTree W b₀ (L.encodeIndex i r) o.1, o.2⟩ : TabK lam L Bd aT aL) :=
  funext fun T => by
    show ((tabO W S b₀ i r s).runDefer mkTab T []).map (fun o => (o.1, o.2.1)) = _
    rw [tabBodies I X lam L Bd aT aL W S b₀ i r s T]
    show _ = (((tabF W S b₀ s).runDefer mkTab T []).map fun o => (o.1, o.2.1)).bind _
    rw [PMF.bind_map]
    rfl

theorem tabsFR_nil (b₀ : Bd) : tabsFR W S b₀ [] = Ker.pure [] := rfl

theorem tabsFR_cons (b₀ : Bd) (s : ℕ → Bits) (ss : List (ℕ → Bits)) :
    tabsFR W S b₀ (s :: ss) = Ker.bind (tabFR W S b₀ s) fun o =>
      Ker.bind (tabsFR W S b₀ ss) fun os => Ker.pure (o :: os) :=
  funext fun _ => rfl

/-- The same for the copies' tables. -/
theorem tabsK (h : HonestSide lam L Bd aT aL) (i : I) :
    ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
      Ker.ofDefer mkTab (tabsO W S h i ds) =
        Ker.bind (tabsFR W S h.b₀ (ds.map fun d => cutS (2 ^ W.depth) d.s)) fun os =>
          Ker.pure (realTabs W h.b₀ i (ds.map fun d => d.r) os)
  | [] => by
    rw [tabsO, Ker.ofDefer_pure, List.map_nil, tabsFR_nil, Ker.pure_bind]
    rfl
  | d :: ds => by
    rw [tabsO, Ker.ofDefer_bind, tabK]
    simp only [Ker.ofDefer_bind, Ker.ofDefer_pure, tabsK h i ds, List.map_cons, tabsFR_cons,
      Ker.bind_assoc, Ker.pure_bind, realTabs]

/-- **The honest copies' tables are the reduction's with the bodies put in.** -/
theorem tabsBodies : Spec.tabsBodies := by
  intro I X lam L Bd aT aL W S h i ds T
  exact congrFun (tabsK W S h i ds) T

/-! ## The seeds of a list of tables -/

/-- **Some seed outside Gs.** -/
theorem seedsBadList : Spec.seedsBadList := by
  intro I X lam L Bd aT aL W S Gs δ b₀ ss
  induction ss with
  | nil =>
    intro T _ hT
    show pr (PMF.pure ([], T)) _ ≤ _
    rw [pr_pure, if_neg]
    · exact zero_le _
    · rintro (⟨x, hx, _⟩ | hn)
      · exact absurd hx (List.not_mem_nil)
      · exact hn hT
  | cons s ss ih =>
    intro T hδ hT
    show pr ((tabFR W S b₀ s T).bind fun o => (tabsFR W S b₀ ss o.2).bind fun o' =>
      PMF.pure (o.1 :: o'.1, o'.2)) _ ≤ _
    refine le_trans (pr_bind_le_add _ _ _ {o | ¬ Gs o.1.2 ∨ ¬ SeedsIn W S Gs o.2}
      (ε := (ss.length : ℝ≥0∞) * δ) fun o _ ho => ?_) ?_
    · have hg : Gs o.1.2 := by
        by_contra hn
        exact ho (Or.inl hn)
      have hs : SeedsIn W S Gs o.2 := by
        by_contra hn
        exact ho (Or.inr hn)
      show pr ((tabsFR W S b₀ ss o.2).map fun o' => (o.1 :: o'.1, o'.2)) _ ≤ _
      rw [pr_map]
      refine le_trans (pr_mono _ ?_) (ih o.2 hδ hs)
      rintro o' (⟨x, hx, hn⟩ | hn)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hg hn
        · exact Or.inl ⟨x, hx, hn⟩
      · exact Or.inr hn
    · have h1 : pr (tabFR W S b₀ s T) {o | ¬ Gs o.1.2 ∨ ¬ SeedsIn W S Gs o.2} ≤ δ := by
        unfold tabFR
        rw [pr_map]
        exact seedsBad I X lam L Bd aT aL W S Gs δ b₀ s T hδ hT
      calc _ ≤ δ + (ss.length : ℝ≥0∞) * δ := add_le_add h1 le_rfl
        _ = ((s :: ss).length : ℝ≥0∞) * δ := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-! ## The whole tables' phase -/

variable (h : HonestSide lam L Bd aT aL)

theorem avoids_coinsCopies (o : TypedOracleCompiler.Compile.Batch.OracleName) :
    ∀ n : ℕ, (coinsCopies W h n).Avoids o
  | 0 => trivial
  | n + 1 => Avoids.bind (c := coinsCopy W h) (fun _ _ _ _ => trivial) fun _ =>
      Avoids.bind (avoids_coinsCopies o n) fun _ => trivial

/-- The committer's coins leave the table of answers as it is. -/
theorem coinsC_keeps (T : Tb W) : ∀ x ∈ ((coinsC W h).runLazy T).support, x.2 = T :=
  fun x hx => funext fun o => runLazy_avoids o (coinsC W h)
    (fun _ _ _ _ => Avoids.bind (avoids_coinsCopies W h o (h.M + 1)) fun _ => trivial) T x hx

theorem post_coinsCopies : ∀ n : ℕ, Post (fun ds => ds.length = n) (coinsCopies W h n)
  | 0 => rfl
  | n + 1 => Post.bind (c := coinsCopy W h) (P := fun _ => True) (fun _ _ _ _ => trivial) fun d _ =>
      Post.bind (post_coinsCopies n) fun ds hds => by
        show (d :: ds).length = n + 1
        rw [List.length_cons, hds]

/-- There are M + 1 copies' coins. -/
theorem coinsC_len (T : Tb W) :
    ∀ x ∈ ((coinsC W h).runLazy T).support, x.1.copies.length = h.M + 1 := by
  intro x hx
  rw [← OComp.interp_lazy] at hx
  exact Post.support Handler.lazy (P := fun d : DrawC lam L Bd aT aL h.KT h.KL =>
    d.copies.length = h.M + 1) (c := coinsC W h)
    (fun _ _ _ _ => Post.bind (post_coinsCopies W h (h.M + 1)) fun ds hds => hds) T x hx

theorem tabsFR_len (b₀ : Bd) : ∀ (ss : List (ℕ → Bits)) (T : Tb W),
    ∀ x ∈ (tabsFR W S b₀ ss T).support, x.1.length = ss.length
  | [], T, x, hx => by
    rw [(PMF.mem_support_pure_iff _ _).mp hx]
    rfl
  | s :: ss, T, x, hx => by
    obtain ⟨o, _, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨o', ho', hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    rw [(PMF.mem_support_pure_iff _ _).mp hx]
    show (o.1 :: o'.1).length = (s :: ss).length
    rw [List.length_cons, List.length_cons, tabsFR_len b₀ ss o.2 o' ho']

/-- **What the tables' phase gives has M + 1 copies' coins and M + 1 copies' trees.** -/
theorem phase1_len (T : Tb W) : ∀ ω ∈ (phase1 W S h T).support,
    ω.d.copies.length = h.M + 1 ∧ ω.os.length = h.M + 1 := by
  intro ω hω
  obtain ⟨o₀, h0, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  obtain ⟨o₁, _, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  obtain ⟨o₂, h2, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  rw [(PMF.mem_support_pure_iff _ _).mp hω]
  have hl := coinsC_len W h T o₀ h0
  refine ⟨hl, ?_⟩
  show o₂.1.length = h.M + 1
  rw [tabsFR_len W S h.b₀ _ _ o₂ h2, List.length_map, hl]

theorem post_coinsCopies_co : ∀ n : ℕ,
    Post (fun ds => ∀ d' ∈ ds, ∃ m, d'.co = h.coL.e m) (coinsCopies W h n)
  | 0 => fun _ hd => absurd hd (List.not_mem_nil)
  | n + 1 => Post.bind (c := coinsCopy W h) (P := fun d => ∃ m, d.co = h.coL.e m)
      (fun _ _ _ e => ⟨e, rfl⟩) fun d hd =>
      Post.bind (post_coinsCopies_co n) fun ds hds => fun d' hd' => by
        rcases List.mem_cons.mp hd' with rfl | hm
        · exact hd
        · exact hds d' hm

/-- The coins of the compiled runs are members of the honest side's lists. -/
theorem coinsC_coins (T : Tb W) : ∀ x ∈ ((coinsC W h).runLazy T).support,
    (∃ n, x.1.co = h.coT.e n) ∧ ∀ d' ∈ x.1.copies, ∃ n, d'.co = h.coL.e n := by
  intro x hx
  rw [← OComp.interp_lazy] at hx
  exact Post.support Handler.lazy (P := fun d : DrawC lam L Bd aT aL h.KT h.KL =>
    (∃ n, d.co = h.coT.e n) ∧ ∀ d' ∈ d.copies, ∃ n, d'.co = h.coL.e n) (c := coinsC W h)
    (fun _ _ _ e => Post.bind (post_coinsCopies_co W h (h.M + 1)) fun ds hds => ⟨⟨e, rfl⟩, hds⟩)
    T x hx

/-- **In what the tables' phase gives, the coins of the compiled runs are members of the honest
side's lists.** -/
theorem phase1_coins (T : Tb W) : ∀ ω ∈ (phase1 W S h T).support,
    (∃ n, ω.d.co = h.coT.e n) ∧ ∀ d' ∈ ω.d.copies, ∃ n, d'.co = h.coL.e n := by
  intro ω hω
  obtain ⟨o₀, h0, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  obtain ⟨o₁, _, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  obtain ⟨o₂, _, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  rw [(PMF.mem_support_pure_iff _ _).mp hω]
  exact coinsC_coins W h T o₀ h0

/-- **Some seed outside Gs, over the whole tables' phase.** -/
theorem phaseBad : Spec.phaseBad := by
  intro I X lam L Bd aT aL W S h Gs δ T hδ hT
  unfold phase1
  refine pr_bind_le_of_forall _ _ _ fun o₀ h0 => ?_
  rw [coinsC_keeps W h T o₀ h0]
  have hl := coinsC_len W h T o₀ h0
  refine le_trans (pr_bind_le_add _ _ _ {o | ¬ Gs o.1.2 ∨ ¬ SeedsIn W S Gs o.2}
    (ε := ((h.M + 1 : ℕ) : ℝ≥0∞) * δ) fun o₁ _ ho => ?_) ?_
  · have hg : Gs o₁.1.2 := by
      by_contra hn
      exact ho (Or.inl hn)
    have hs : SeedsIn W S Gs o₁.2 := by
      by_contra hn
      exact ho (Or.inr hn)
    show pr ((tabsFR W S h.b₀ (o₀.1.copies.map fun d => cutS (2 ^ W.depth) d.s) o₁.2).map fun o₂ =>
      (⟨o₀.1, o₁.1, o₂.1, o₂.2⟩ : Om W h)) _ ≤ _
    rw [pr_map]
    have hb := seedsBadList I X lam L Bd aT aL W S Gs δ h.b₀
      (o₀.1.copies.map fun d => cutS (2 ^ W.depth) d.s) o₁.2 hδ hs
    rw [List.length_map, hl] at hb
    refine le_trans (pr_mono _ ?_) hb
    rintro o₂ (hn | hn)
    · exact absurd hg hn
    · exact Or.inl hn
  · have h1 : pr (tabFR W S h.b₀ (cutS (2 ^ W.depth) o₀.1.s) T)
        {o | ¬ Gs o.1.2 ∨ ¬ SeedsIn W S Gs o.2} ≤ δ := by
      unfold tabFR
      rw [pr_map]
      exact seedsBad I X lam L Bd aT aL W S Gs δ h.b₀ _ T hδ hT
    calc _ ≤ δ + ((h.M + 1 : ℕ) : ℝ≥0∞) * δ := add_le_add h1 le_rfl
      _ = ((h.M + 2 : ℕ) : ℝ≥0∞) * δ := by
        push_cast
        ring

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.tabsBodies
#print axioms OnBytes.LateWorld.seedsBadList
#print axioms OnBytes.LateWorld.phase1_len
#print axioms OnBytes.LateWorld.phase1_coins
#print axioms OnBytes.LateWorld.phaseBad
